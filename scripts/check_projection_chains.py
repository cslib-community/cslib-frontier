#!/usr/bin/env python3
"""Stop positional projection chains from spreading in public statements (#1764).

Usage: python3 scripts/check_projection_chains.py [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline [--allow-increase]] [--root DIR] [--baseline FILE]

This checks the rule "Named components instead of positional projections" in CONTRIBUTING.md. A
*chain* is a run of two or more positional tuple projections written in any of three forms:

* dotted projection chains after a term: `c.1.2`, `s.2.1.1`, `p.2.fst`, `(f x).1.2`, `(·.1.2)`;
* nested or mixed `Prod.fst` / `Prod.snd` applications: `Prod.fst (Prod.snd p)`,
  `Prod.fst <| Prod.snd p`, `Prod.fst p.2`, `(Prod.snd p).1`, `p.2 |> Prod.fst`,
  `p |> Prod.snd |> Prod.fst` (point-free composition `Prod.fst ∘ Prod.snd` is permitted, as are
  `Prod.fst` / `Prod.snd` passed as higher-order function arguments);
* projections chained through a `let`-bound projection alias: `let rest := p.2` (or
  `let rest := Prod.snd p`) followed by `rest.1` / `Prod.fst rest` / `rest |> Prod.fst` inside
  `rest`'s unshadowed scope.

A single projection `p.1` is not a chain, and neither is a numeric literal such as `1.5.2`. A
module's *count* is the number of chains in

* the signature of each public declaration (theorem, lemma, def, abbrev, instance, opaque, axiom;
  for a structure, class or inductive, the whole declaration with its fields and constructors), and
* the body of each public `def`, `abbrev`, `instance` and `opaque`,

leaving out tactic blocks (`by …` to the end of its bracket group, and `termination_by` and
`decreasing_by` clauses), comments and strings: projections inside proofs are fine, and theorem
bodies are proofs. Public means what it means for `scripts/check_encoding_readability.py`, whose
declaration reader this check shares; unlike that check, `Internal` namespaces and modules count.
The standing exceptions of CONTRIBUTING do not count:

* declarations marked `@[program_certificate]` or `@[fun_prop]`, and chains inside an application
  of an efficiency predicate (`Computable…In…`, `IsPPT…`, `IsOraclePPT…`, `PolyTimeComputable…`,
  `Refines`, bare or namespace-qualified, as in `Turing.MultiTapeTM.ComputableInPolyTime`):
  conclusions that automation looks up by head keep the projection form;
* section `variable`s, which are not declarations;
* named accessors, a `def` or `abbrev` whose body is one chain on a binder, such as
  `abbrev Ctx.desc (c : Ctx) := c.1.2`: these are the recommended remedy.

The reader is syntactic, so the count is a measure, not a proof that a statement reads well.

`scripts/projection_chains_baseline.json` records the count of each module that has chains, as
`{module path: count}`. In a module that the change adds, modifies or deletes (against the merge
base of `--base`, default `origin/main`, and the working tree, as
`scripts/check_changed_files.py` computes it), a count above the module's *limit* fails. The limit
is the module's entry (0 for a new module), capped at the module's count at the merge base unless
the change raises the entry itself. A change therefore cannot add chains back under an entry that
is higher than the count it started from (to add them back on purpose, raise the entry by hand
above its value at the merge base), and removing chains needs no baseline edit: a count below its
entry is only reported. Edits to the baseline are kept to raises, moves and missing entries,
because concurrent edits to neighbouring lines of the file conflict in the merge queue; entries
above their counts are pruned from time to time with `--update-baseline --all`. Only the changed
modules are read, so the check takes seconds. Pull requests run this mode.

`--all` enforces every module. `--report` prints every difference from the baseline and always
succeeds; merge groups and pushes to `main` run it. `--update-baseline` sets the entries of the
changed modules (with `--all`, of every module) to their counts; it refuses a count above its
limit unless `--allow-increase` is given, for instance when a module moves, and always refuses
one that the recorded entry would still leave above its limit.
`--update-baseline --all --allow-increase` regenerates the whole baseline. `--list [PREFIX]`
ignores the baseline and prints every counted chain in the modules under the path PREFIX (such as
`CslibFrontier/DataStructure`), or in every module, with the most affected modules first; it
always succeeds.

The scanner is adapted from the survey script of the #1764 projections lane. The check reads only
the sources: it needs no build outputs.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_changed_files as ccf  # noqa: E402
import check_encoding_readability as cer  # noqa: E402

BASELINE = ROOT / "scripts/projection_chains_baseline.json"
UPDATE = "python3 scripts/check_projection_chains.py --update-baseline"
RULE = "CONTRIBUTING.md, Named components instead of positional projections"

COMPONENT = r"(?:\d+|fst|snd)"
COMPONENT_WORD = re.compile(rf"^(?:{COMPONENT})$")
# Two or more `.1`/`.2`/`.fst`/`.snd` after an identifier character, a closing bracket or `·`.
CHAIN = re.compile(r"(?:(?<=[\w'!?)\]}⟩⦄])|(?<=·))((?:\." + COMPONENT + r"(?![\w'!?])){2,})")
# At least one `.1`/`.2`/`.fst`/`.snd` projection (for pre-filtering and chained projections).
SINGLE_PROJ = re.compile(r"(?:(?<=[\w'!?)\]}⟩⦄])|(?<=·))\." + COMPONENT + r"(?![\w'!?])")
DOT_RUN = re.compile(r"(?:\." + COMPONENT + r"(?![\w'!?]))+")
# Prefix projection function `Prod.fst` / `Prod.snd`, optionally `_root_`-qualified.
PROD_PROJ = re.compile(r"(?<![\w'.])(?:_root_\.)?Prod\.(fst|snd)(?![\w'!?])")
LET_KW = re.compile(r"(?<![\w'.!?])let(?![\w'!?])")
# Words after which a following `Prod.fst` / `Prod.snd` starts an application (not an argument).
HEAD_KEYWORDS = frozenset({
    "if", "then", "else", "match", "with", "where", "do", "return", "let", "have",
    "show", "from", "fun", "λ", "in", "by", "forall", "exists",
})
PREV_WORD = re.compile(r"[\w'][\w'!?]*$")
ATOM_TOP_STOP = frozenset("+-*/=<>∧∨↔→←↦,;:|&^%$~@∘!¬?")
# A chain whose head is only digits is a numeric literal such as `1.5.2`, not a projection.
NUMERIC_HEAD = re.compile(r"(?<![\w'!?.])\d+$")
ATTRIBUTES = re.compile(r"@\[([^\]]*)\]")
CERTIFICATE_ATTRIBUTES = {"program_certificate", "fun_prop"}
BODY_KEYWORDS = {"def", "abbrev", "instance", "opaque"}
TACTIC = re.compile(r"(?<![\w'.!?])(by|decreasing_by|termination_by)(?![\w'!?])")
# An efficiency predicate head, bare or qualified (`Turing.MultiTapeTM.ComputableInPolyTime`,
# `_root_.IsPPT`): automation looks it up by its last component, however it is spelled.
EFFICIENCY = re.compile(
    r"(?<![\w'.])(?:[\w']+\.)*"
    r"(?:Computable\w*In\w*|IsPPT\w*|IsOraclePPT\w*|PolyTimeComputable\w*|Refines)(?![\w'!?])")
# The body of a named accessor: `:= c.1.2` or `:= fun c => c.1.2`, optionally parenthesized.
ACCESSOR = re.compile(r"\s*:=\s*(?:fun\s+\w+\s*=>\s*)?\(?\s*[\w'.]+?(?:\." + COMPONENT
                      + r"){2,}\s*\)?\s*")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


@dataclass(frozen=True)
class Chain:
    declaration: str
    line: int
    chain: str  # such as `.1.2`, `Prod.fst (Prod.snd …)`, or `rest.1 (via let rest := … .2)`


def _group_end(text: str, pos: int) -> int:
    """The offset where the bracket group enclosing `pos` closes, or the length of `text`."""
    depth = 0
    for i in range(pos, len(text)):
        if text[i] in OPEN:
            depth += 1
        elif text[i] in CLOSE:
            if depth == 0:
                return i
            depth -= 1
    return len(text)


def _skip_ws(text: str, pos: int, limit: int | None = None) -> int:
    end = len(text) if limit is None else limit
    while pos < end and text[pos].isspace():
        pos += 1
    return pos


def _strip_parens(text: str, start: int, end: int) -> tuple[int, int]:
    """Trim outer whitespace and matching enclosing `(...)` pairs covering `[start, end)`."""
    while True:
        while start < end and text[start].isspace():
            start += 1
        while end > start and text[end - 1].isspace():
            end -= 1
        if start + 1 < end and text[start] == "(" and text[end - 1] == ")" \
                and _group_end(text, start + 1) == end - 1:
            start += 1
            end -= 1
            continue
        return start, end


def _has_top_level(text: str, start: int, end: int, chars: str) -> bool:
    """Whether any character in `chars` occurs at bracket depth 0 inside `text[start:end]`."""
    depth = 0
    for i in range(start, end):
        ch = text[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and ch in chars:
            return True
    return False


def _is_head_pos(text: str, start: int) -> bool:
    """Whether `text[start:]` is in application-head position rather than an argument of a
    preceding expression (distinguishing `Prod.fst (Prod.snd p)` from `map Prod.fst x`)."""
    j = start - 1
    while j >= 0 and text[j].isspace():
        j -= 1
    if j < 0:
        return True
    ch = text[j]
    if ch in CLOSE or ch == "·":
        return False
    word = PREV_WORD.search(text[:j + 1])
    if word:
        if word.start() > 0 and text[word.start() - 1] == ".":
            return False
        return word[0] in HEAD_KEYWORDS
    return True


def _is_numeric_proj(text: str, dot_offset: int) -> bool:
    return NUMERIC_HEAD.search(text[max(0, dot_offset - 40):dot_offset]) is not None


def _is_atomic_span(text: str, start: int, end: int) -> bool:
    """Whether `text[start:end]` is one unspaced atomic/postfix expression (no top-level spaces or
    infix operators)."""
    if start >= end:
        return False
    depth = 0
    for i in range(start, end):
        ch = text[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            if depth == 0:
                return False
            depth -= 1
        elif depth == 0 and (ch.isspace() or ch in ATOM_TOP_STOP):
            return False
    return depth == 0


def _trailing_dot_run(text: str, start: int, end: int) -> tuple[int, str] | None:
    """If `text[start:end]` is a single atomic expression ending in `.1`/`.2`/`.fst`/`.snd` (one or
    more components), return `(dot_offset, dot_text)`."""
    start, end = _strip_parens(text, start, end)
    if not _is_atomic_span(text, start, end):
        return None
    span = text[start:end]
    # Bare `Prod.fst` / `Prod.snd` is a function name, not a projection applied to a value.
    if PROD_PROJ.fullmatch(span):
        return None
    match = re.search(r"((?:\." + COMPONENT + r")+)$", span)
    if not match or match.start() == 0:
        return None
    dot_offset = start + match.start()
    # Ignore Lean checked indexing `xs[i]'h.2`, where `.2` belongs to the bounds proof `h.2`.
    depth = 0
    for i in range(start, dot_offset):
        if text[i] in OPEN:
            depth += 1
        elif text[i] in CLOSE:
            depth -= 1
            if depth == 0 and text[i] == "]" and i + 1 < dot_offset and text[i + 1] == "'":
                return None
    prev = text[dot_offset - 1]
    if not (prev in CLOSE or prev == "·" or re.match(r"[\w'!?]", prev)):
        return None
    if _is_numeric_proj(text, dot_offset):
        return None
    return dot_offset, match[1]


def _single_postfix_end(text: str, pos: int, limit: int) -> int:
    """Starting at `pos`, read one unspaced postfix expression (brackets, subscript or dotted path)
    and return its end offset."""
    i = pos
    while i < limit:
        ch = text[i]
        if ch in OPEN:
            end = _group_end(text, i + 1)
            if end >= limit:
                return limit
            i = end + 1
        elif ch in CLOSE or ch.isspace() or ch in ATOM_TOP_STOP:
            break
        else:
            i += 1
    return i


def _proj_rhs_label(text: str, start: int, end: int) -> str | None:
    """If `text[start:end]` is a pure positional projection expression (`e.2`, `(f x).1`,
    `Prod.snd e`, `e |> Prod.snd`), return a display snippet (`….2`, `Prod.snd …`), else None."""
    start, end = _strip_parens(text, start, end)
    if start >= end:
        return None
    dot = _trailing_dot_run(text, start, end)
    if dot is not None:
        return "…." + dot[1].rsplit(".", 1)[-1]
    pm = PROD_PROJ.match(text, start, end)
    if pm:
        nxt = _skip_ws(text, pm.end(), end)
        if nxt >= end or text[nxt] == "∘":
            return None
        if text.startswith("<|", nxt) or text[nxt] == "$":
            arg_start = _skip_ws(text, nxt + (2 if text.startswith("<|", nxt) else 1), end)
            if arg_start < end and not _has_top_level(text, arg_start, end, ","):
                return f"Prod.{pm[1]} …"
        else:
            arg_end = _single_postfix_end(text, nxt, end)
            if arg_end > nxt and _skip_ws(text, arg_end, end) == end:
                return f"Prod.{pm[1]} …"
        return None
    tail = re.search(r"\|>\s*(?:_root_\.)?Prod\.(fst|snd)$", text[start:end].rstrip())
    if tail and not _has_top_level(text, start, start + tail.start(), ",;"):
        return f"Prod.{tail[1]} …"
    return None


def _wrap_prod(step: str, inner: str) -> str:
    return f"{step} {inner}" if inner == "…" or inner.startswith("….") else f"{step} ({inner})"


def _peel_atom(text: str, start: int, end: int
               ) -> tuple[int, str, set[int], set[int]] | None:
    """Peel nested `Prod.fst`/`Prod.snd` and trailing dot projections from `[start, end)`.
    Returns `(depth, label, prod_offsets, dot_offsets)`."""
    start, end = _strip_parens(text, start, end)
    if start >= end or _has_top_level(text, start, end, ",∘"):
        return None
    if PROD_PROJ.match(text, start, end):
        peel = _peel_prod_app(text, start, end)
        return peel[:4] if peel is not None and _skip_ws(text, peel[4], end) == end else None
    dot = _trailing_dot_run(text, start, end)
    if dot is not None:
        dot_off, dot_txt = dot
        dot_depth = dot_txt.count(".")
        if dot_off > start and text[start] == "(" and text[dot_off - 1] == ")" \
                and _group_end(text, start + 1) == dot_off - 1:
            inner = _peel_atom(text, start + 1, dot_off - 1)
            if inner is not None:
                i_depth, i_label, i_prods, i_dots = inner
                return (i_depth + dot_depth, f"({i_label}){dot_txt}", i_prods,
                        {dot_off, *i_dots})
        return dot_depth, f"…{dot_txt}", set(), {dot_off}
    return None


def _rhs_ends(text: str, pos: int, limit: int, anchor_pos: int, first_line_col: int,
              *, is_pipe_forward: bool) -> bool:
    """Whether a `<|`/`$` (`is_pipe_forward=False`) or `|>` (`is_pipe_forward=True`) right operand
    ending at `pos` terminates before any further argument or operator."""
    after = _skip_ws(text, pos, limit)
    if after >= limit:
        return True
    ch = text[after]
    if ch in CLOSE or ch in ",;":
        return True
    if is_pipe_forward and (text.startswith("|>", after) or text.startswith("<|", after)
                            or (ch == "$" and (after + 1 >= limit or text[after + 1].isspace()))):
        return True
    if ch == ":" and not text.startswith(":=", after) and not text.startswith("::", after):
        return True
    if ch == "|" and not text.startswith("|>", after) and not text.startswith("||", after):
        return True
    if re.match(r"(?:in|then|else|where|with|by|decreasing_by|termination_by)(?![\w'!?])",
                text[after:]):
        return True
    if "\n" in text[pos:after] \
            and _line_col(text, after, first_line_col) <= _line_indent(
                text, anchor_pos, first_line_col) \
            and ch not in ATOM_TOP_STOP and ch != "." \
            and not text.startswith(":=", after) and not text.startswith("::", after):
        return True
    return False


def _unwrap_ident_parens(tokens: list[re.Match[str]], match: dict[int, int],
                         idx: int, end: int) -> tuple[str, int] | None:
    """If `tokens[idx:end]` starts with a bare or parenthesized identifier (`r`, `(r)`), return
    `(name, after_tok_idx)`."""
    if idx >= end:
        return None
    outer_end = match[idx] + 1 if tokens[idx][0] == "(" else idx + 1
    if outer_end > end:
        return None
    left, right = idx, outer_end
    while left + 1 < right and tokens[left][0] == "(" and match[left] == right - 1 \
            and tokens[right - 1][0] == ")":
        left += 1
        right -= 1
    if left + 1 == right and tokens[left].lastgroup == "ident" and "." not in tokens[left][0]:
        return tokens[left][0], outer_end
    return None


def _peel_prod_app(text: str, prod_start: int, limit: int, first_line_col: int = 0
                   ) -> tuple[int, str, set[int], set[int], int] | None:
    """Unwrap nested `Prod.fst`/`Prod.snd` projection steps starting at `prod_start`, returning
    `(depth, label, prod_offsets, dot_offsets, consumed_end)`."""
    m = PROD_PROJ.match(text, prod_start, limit)
    if not m:
        return None
    nxt = _skip_ws(text, m.end(), limit)
    if nxt >= limit or text[nxt] == "∘":
        return None
    step = f"Prod.{m[1]}"
    if text.startswith("<|", nxt) or text[nxt] == "$":
        arg_start = _skip_ws(text, nxt + (2 if text.startswith("<|", nxt) else 1), limit)
        if arg_start >= limit:
            return None
        if PROD_PROJ.match(text, arg_start, limit):
            sub = _peel_prod_app(text, arg_start, limit, first_line_col)
            if sub is not None and _rhs_ends(
                    text, sub[4], limit, m.start(), first_line_col, is_pipe_forward=False):
                return sub[0] + 1, _wrap_prod(step, sub[1]), {m.start(), *sub[2]}, sub[3], sub[4]
        arg_end = _single_postfix_end(text, arg_start, limit)
        # Only consume `<| e` if `e` is the entire operand of `<|` / `$` (not `e + q`,
        # `e x`, or `e |> f`). Within a comma/semicolon-free span `<|` still wraps the whole tail.
        if not _rhs_ends(text, arg_end, limit, m.start(), first_line_col, is_pipe_forward=False):
            consumed_end = arg_end if _has_top_level(text, arg_start, limit, ",;") else limit
            return 1, f"{step} …", {m.start()}, set(), consumed_end
        sub = _peel_atom(text, arg_start, arg_end)
        if sub is not None:
            return sub[0] + 1, _wrap_prod(step, sub[1]), {m.start(), *sub[2]}, sub[3], arg_end
        return 1, f"{step} …", {m.start()}, set(), arg_end
    arg_end = _single_postfix_end(text, nxt, limit)
    if arg_end == nxt:
        return None
    sub = _peel_atom(text, nxt, arg_end)
    if sub is not None:
        return sub[0] + 1, _wrap_prod(step, sub[1]), {m.start(), *sub[2]}, sub[3], arg_end
    return 1, f"{step} …", {m.start()}, set(), arg_end


def _matching_open(text: str, close_pos: int) -> int:
    depth = 0
    for j in range(close_pos, -1, -1):
        if text[j] in CLOSE:
            depth += 1
        elif text[j] in OPEN:
            depth -= 1
            if depth == 0:
                return j
    return -1


def _prod_chains(text: str, exempt: list[tuple[int, int]], first_line_col: int = 0
                 ) -> tuple[list[tuple[int, str]], set[int], set[int]]:
    """Detect nested/mixed `Prod.fst`/`Prod.snd` projection chains and return
    `(hits, consumed_prod_offsets, consumed_dot_offsets)`."""
    hits: list[tuple[int, str]] = []
    consumed_prods: set[int] = set()
    consumed_dots: set[int] = set()

    def is_exempt(off: int) -> bool:
        return any(s <= off < e for s, e in exempt)

    def extend_hit(target_off: int, new_off: int, suffix: str) -> None:
        for idx, (hoff, hlbl) in enumerate(hits):
            if hoff == target_off:
                hits[idx] = (new_off, f"({hlbl}){suffix}")
                return

    # 1. Prefix `Prod.fst`/`Prod.snd` (`Prod.fst (Prod.snd p)`, `Prod.fst p.2`, `Prod.fst <| ...`)
    for m in PROD_PROJ.finditer(text):
        off = m.start()
        if off in consumed_prods or not _is_head_pos(text, off):
            continue
        peel = _peel_prod_app(text, off, len(text), first_line_col)
        if peel is not None and peel[0] >= 2:
            if not is_exempt(off):
                hits.append((off, peel[1]))
            consumed_prods |= peel[2]
            consumed_dots |= peel[3]

    # 2. Postfix `(Prod.snd p).1`, `(p |> Prod.snd).1`, `(Prod.fst (Prod.snd p)).1`
    for i, ch in enumerate(text):
        if ch != "(":
            continue
        close = _group_end(text, i + 1)
        if close >= len(text) or text[close] != ")":
            continue
        dm = DOT_RUN.match(text, close + 1)
        if not dm or dm.start() in consumed_dots:
            continue
        istart, iend = _strip_parens(text, i + 1, close)
        if _has_top_level(text, istart, iend, ",∘"):
            continue
        if PROD_PROJ.match(text, istart, iend):
            peel = _peel_prod_app(text, istart, iend, first_line_col)
            if peel is not None and _skip_ws(text, peel[4], iend) == iend:
                if istart in consumed_prods:
                    # Extend the existing hit label for `(Prod.fst (Prod.snd p)).1`.
                    extend_hit(istart, i, dm[0])
                    consumed_dots.add(dm.start())
                    continue
                if not is_exempt(i):
                    hits.append((i, f"({peel[1]}){dm[0]}"))
                consumed_prods |= peel[2]
                consumed_dots |= peel[3] | {dm.start()}
        elif pm := re.search(r"\|>\s*((?:_root_\.)?Prod\.(fst|snd))$", text[istart:iend].rstrip()):
            poff = istart + pm.start(1)
            if poff not in consumed_prods:
                if not is_exempt(i):
                    hits.append((i, f"(… |> Prod.{pm[2]}){dm[0]}"))
                consumed_prods.add(poff)
            consumed_dots.add(dm.start())

    # 3. Pipe-forward `p |> Prod.snd |> Prod.fst`, `p.2 |> Prod.fst`, `(Prod.snd p) |> Prod.fst`
    for m in re.finditer(r"\|>\s*((?:_root_\.)?Prod\.(fst|snd))(?![\w'!?])", text):
        prod_off = m.start(1)
        if prod_off in consumed_prods:
            continue
        if not _rhs_ends(text, m.end(), len(text), prod_off, first_line_col, is_pipe_forward=True):
            continue
        steps, p_offs, cur = [f"Prod.{m[2]}"], {prod_off}, m.end()
        while nm := re.match(r"\s*\|>\s*((?:_root_\.)?Prod\.(fst|snd))(?![\w'!?])", text[cur:]):
            next_off = cur + nm.start(1)
            if not _rhs_ends(text, cur + nm.end(), len(text), next_off, first_line_col,
                             is_pipe_forward=True):
                break
            steps.append(f"Prod.{nm[2]}")
            p_offs.add(next_off)
            cur += nm.end()
        lhs_end = m.start()
        while lhs_end > 0 and text[lhs_end - 1].isspace():
            lhs_end -= 1
        d_offs: set[int] = set()
        lhs_label = ""
        extended = False
        if lhs_end > 0:
            lm = re.search(r"((?:\." + COMPONENT + r")+)$", text[:lhs_end])
            if lm and lm.start() > 0:
                atom_start = lm.start()
                while atom_start > 0:
                    prev_ch = text[atom_start - 1]
                    if prev_ch in CLOSE:
                        matched = _matching_open(text, atom_start - 1)
                        if matched < 0:
                            break
                        atom_start = matched
                    elif prev_ch.isspace() or prev_ch in OPEN or prev_ch in ATOM_TOP_STOP:
                        break
                    else:
                        atom_start -= 1
                dot = _trailing_dot_run(text, atom_start, lhs_end)
                if dot is not None and _is_head_pos(text, atom_start):
                    lhs_label = f"…{dot[1]}"
                    d_offs.add(dot[0])
            elif text[lhs_end - 1] == ")":
                open_i = _matching_open(text, lhs_end - 1)
                if open_i >= 0 and text[open_i] == "(" and _is_head_pos(text, open_i):
                    istart, iend = _strip_parens(text, open_i + 1, lhs_end - 1)
                    if PROD_PROJ.match(text, istart, iend) \
                            and not _has_top_level(text, istart, iend, ",∘"):
                        peel = _peel_prod_app(text, istart, iend, first_line_col)
                        if peel is not None and _skip_ws(text, peel[4], iend) == iend:
                            if istart in consumed_prods:
                                extend_hit(istart, open_i, " |> " + " |> ".join(steps))
                                extended = True
                            else:
                                lhs_label = f"({peel[1]})"
                                p_offs |= peel[2]
                                d_offs |= peel[3]
        if extended or len(steps) >= 2 or lhs_label:
            if not extended and not is_exempt(prod_off):
                hits.append((prod_off, " |> ".join([lhs_label or "…", *steps])))
            consumed_prods |= p_offs
            consumed_dots |= d_offs

    return hits, consumed_prods, consumed_dots


def _line_col(text: str, pos: int, first_line_col: int = 0) -> int:
    nl = text.rfind("\n", 0, pos)
    return pos + first_line_col if nl < 0 else pos - nl - 1


def _line_indent(text: str, pos: int, first_line_col: int = 0) -> int:
    nl = text.rfind("\n", 0, pos)
    start = 0 if nl < 0 else nl + 1
    i = start
    while i < len(text) and text[i] in " \t":
        i += 1
    return (i - start) + (first_line_col if nl < 0 else 0)


def _let_rhs_end(text: str, tokens: list[re.Match[str]], match: dict[int, int],
                 let_idx: int, op_end_tok: int, stop: int, first_line_col: int) -> tuple[int, int]:
    """Return `(rhs_end_char, body_tok_idx)` for `let` at `let_idx` whose `:=`/`←` ends at
    `op_end_tok`."""
    let_col = _line_col(text, tokens[let_idx].start(), first_line_col)
    k = op_end_tok + 1
    while k < stop:
        tok = tokens[k]
        if tok[0] == ";":
            return tok.start(), k + 1
        if k > op_end_tok + 1 and "\n" in text[tokens[k - 1].end():tok.start()] \
                and _line_col(text, tok.start(), first_line_col) <= let_col:
            return tokens[k - 1].end(), k
        if tok.lastgroup == "open":
            k = match[k] + 1
            continue
        if tok.lastgroup == "ident" and tok[0] == "in":
            return tok.start(), k + 1
        k += 1
    end_char = tokens[stop - 1].end() if stop > op_end_tok + 1 else tokens[op_end_tok].end()
    return end_char, stop


def _let_alias_chains(text: str, exempt: list[tuple[int, int]],
                      consumed_prods: set[int], consumed_dots: set[int],
                      first_line_col: int = 0) -> list[tuple[int, str]]:
    """Find projections applied to a `let`-bound projection alias (`let rest := p.2; rest.1`,
    `let rest := Prod.snd p; Prod.fst rest`), respecting layout, `if`/`match` branches, and
    binder shadowing."""
    if not LET_KW.search(text):
        return []
    tokens = cer._tokens(text)
    if not tokens:
        return []
    match = cer._matching(tokens)
    hits: list[tuple[int, str]] = []
    # Active bindings: (end_tok, origin_tok, depth, anchor_indent, name, label_or_None)
    scopes: list[tuple[int, int, int, int, str, str | None]] = []
    pending: list[tuple[int, int, int, int, int, str, str | None]] = []
    closes: list[int] = []
    rhs_stops: list[int] = []
    if_stack: list[tuple[int, int, int]] = []   # (depth, indent, if_tok)
    arm_stack: list[tuple[int, int, int | None]] = []  # (depth, indent, last_arm_tok)
    quant_commas: set[int] = set()
    prev_end = 0

    def adj(j: int, a: str, b: str) -> bool:
        return j + 1 < len(tokens) and tokens[j][0] == a and tokens[j + 1][0] == b \
            and tokens[j + 1].start() == tokens[j].end()

    def is_word(j: int, w: str) -> bool:
        return tokens[j].lastgroup == "ident" and tokens[j][0] == w

    def is_exempt(off: int) -> bool:
        return any(s <= off < e for s, e in exempt)

    def lookup(name: str) -> str | None:
        for entry in reversed(scopes):
            if entry[4] == name:
                return entry[5]
        return None

    for k, tok in enumerate(tokens):
        depth = len(closes)
        new_line = k > 0 and "\n" in text[prev_end:tok.start()]
        tok_col = _line_col(text, tok.start(), first_line_col) if new_line else -1
        prev_end = tok.end()

        while rhs_stops and rhs_stops[-1] <= k:
            rhs_stops.pop()
        scopes = [s for s in scopes if s[0] > k]
        if new_line:
            scopes = [s for s in scopes
                      if not (s[2] == depth and s[3] >= 0 and tok_col < s[3])]
            if not is_word(k, "else"):
                while if_stack and if_stack[-1][0] == depth and tok_col <= if_stack[-1][1] \
                        and not is_word(k, "then"):
                    if_stack.pop()
            if tok[0] != "|":
                while arm_stack and arm_stack[-1][0] == depth and tok_col < arm_stack[-1][1]:
                    _, _, arm_tok = arm_stack.pop()
                    if arm_tok is not None:
                        scopes = [s for s in scopes
                                  if not (s[2] == depth and s[1] >= arm_tok)]
        activated = [p for p in pending if p[0] <= k < p[1]]
        pending = [p for p in pending if p[0] > k]
        for _, end_tok, orig, bdepth, anchor, nm, lbl in activated:
            scopes.append((end_tok, orig, bdepth, anchor, nm, lbl))

        end = min(closes[-1] if closes else len(tokens),
                  rhs_stops[-1] if rhs_stops else len(tokens))
        word = tok[0]

        if tok.lastgroup == "open":
            close = match[k]
            if close + 1 < len(tokens) and tokens[close + 1][0] == "→" and word in "({⦃[" \
                    and any(cer._is_colon(tokens, j) for j in range(k + 1, close)):
                for j in cer._group_names(tokens, match, k):
                    pending.append((close + 1, end, k, depth, -1, tokens[j][0], None))
            elif word == "{":
                bar = next((j for j in range(k + 1, close) if tokens[j][0] == "|"), None)
                if bar is not None:
                    for j, _ in cer._binders(tokens, match, k + 1, bar):
                        pending.append((bar, close, k, depth + 1, -1, tokens[j][0], None))
            closes.append(close)
            continue
        if tok.lastgroup == "close":
            if closes:
                closes.pop()
            if_stack = [e for e in if_stack if e[0] <= len(closes)]
            arm_stack = [e for e in arm_stack if e[0] <= len(closes)]
            continue

        if word == "," and closes and k not in quant_commas:
            scopes = [s for s in scopes if s[2] < depth]
            continue
        if is_word(k, "if"):
            if_stack.append((depth, _line_indent(text, tok.start(), first_line_col), k))
            continue
        if is_word(k, "else"):
            if if_stack and if_stack[-1][0] == depth:
                _, _, if_tok = if_stack.pop()
                scopes = [s for s in scopes if not (s[2] == depth and s[1] > if_tok)]
            continue
        if is_word(k, "match"):
            arm_stack.append((depth, _line_indent(text, tok.start(), first_line_col), None))
            continue
        if word == "|" and (k == 0 or tokens[k - 1][0] not in "<|") \
                and not adj(k, "|", ">") and not adj(k, "|", "|"):
            j = k + 1
            while j < end and tokens[j][0] not in ";,":
                if tokens[j].lastgroup == "open":
                    j = match[j] + 1
                    continue
                if adj(j, "=", ">"):
                    col = _line_indent(text, tok.start(), first_line_col)
                    if arm_stack and arm_stack[-1][0] == depth:
                        prev_col, prev_arm = arm_stack[-1][1], arm_stack[-1][2]
                        if prev_arm is not None:
                            scopes = [s for s in scopes
                                      if not (s[2] == depth and s[1] >= prev_arm)]
                        arm_stack[-1] = (depth, min(prev_col, col), k)
                    else:
                        arm_stack.append((depth, col, k))
                    for p in range(k + 1, j):
                        if cer._is_name(tokens[p]):
                            pending.append((j + 2, end, k, depth, -1, tokens[p][0], None))
                    break
                j += 1
            continue
        if word in cer.QUANTIFIERS or word in ("fun", "λ", "forall", "exists"):
            is_lam = word in ("fun", "λ")
            stop = cer._separator(tokens, match, k + 1, end, is_lam)
            if not is_lam and stop < end and tokens[stop][0] == ",":
                quant_commas.add(stop)
            for idx, vis in cer._binders(tokens, match, k + 1, stop):
                pending.append((vis, end, k, depth, -1, tokens[idx][0], None))
            continue
        if tok.lastgroup == "ident" and word in ("let", "have") and k + 1 < end:
            is_rec = is_word(k + 1, "rec")
            j = k + 1 + is_rec
            if word == "let" and not is_rec and j < end and cer._is_name(tokens[j]):
                lhs = tokens[j][0]
                scan, in_type, simple, op_tok, monadic = j + 1, False, True, -1, False
                while scan < end:
                    t = tokens[scan]
                    if t.lastgroup == "open":
                        if not in_type:
                            simple = False
                            break
                        scan = match[scan] + 1
                        continue
                    if adj(scan, ":", "="):
                        op_tok = scan + 1
                        break
                    if t[0] == "←":
                        op_tok, monadic = scan, True
                        break
                    if cer._is_colon(tokens, scan):
                        in_type = True
                    elif not in_type:
                        simple = False
                        break
                    scan += 1
                if simple and op_tok >= 0:
                    rhs_end, body_tok = _let_rhs_end(
                        text, tokens, match, k, op_tok, end, first_line_col)
                    lbl = None if monadic else _proj_rhs_label(text, tokens[op_tok].end(), rhs_end)
                    anchor = _line_indent(text, tok.start(), first_line_col)
                    pending.append((body_tok, end, k, depth, anchor, lhs, lbl))
                    rhs_stops.append(body_tok)
                    continue
            names = ([tokens[p][0] for p in cer._group_names(tokens, match, j)]
                     if j < end and tokens[j].lastgroup == "open"
                     else [tokens[j][0]] if j < end and cer._is_name(tokens[j]) else [])
            if is_rec:
                vis = k + 1
            else:
                op_tok = -1
                s_i = j + 1 if not (j < end and tokens[j].lastgroup == "open") else match[j] + 1
                while s_i < end:
                    if tokens[s_i].lastgroup == "open":
                        s_i = match[s_i] + 1
                        continue
                    if adj(s_i, ":", "="):
                        op_tok = s_i + 1
                        break
                    if tokens[s_i][0] == "←":
                        op_tok = s_i
                        break
                    s_i += 1
                vis = (_let_rhs_end(text, tokens, match, k, op_tok, end, first_line_col)[1]
                       if op_tok >= 0 else cer._let_body(text, tokens, match, k, end))
                if op_tok >= 0:
                    rhs_stops.append(vis)
            for nm in names:
                pending.append((vis, end, k, depth, -1, nm, None))
            continue

        # Active alias uses: `x.1` / `x.2` / `x.fst` / `x.snd`, `Prod.fst x`, `x |> Prod.fst`
        limit_char = tokens[end].start() if end < len(tokens) else len(text)
        if tok.lastgroup == "ident" and PROD_PROJ.fullmatch(word):
            poff = tok.start()
            if poff not in consumed_prods and _is_head_pos(text, poff):
                nxt = k + 1
                has_app_op = False
                if nxt < end and tokens[nxt][0] == "$":
                    nxt += 1
                    has_app_op = True
                elif nxt + 1 < end and adj(nxt, "<", "|"):
                    nxt += 2
                    has_app_op = True
                unwrapped = _unwrap_ident_parens(tokens, match, nxt, end)
                if unwrapped is not None:
                    target, after_tok = unwrapped
                    if (not has_app_op or _rhs_ends(
                            text, tokens[after_tok - 1].end(), limit_char, poff, first_line_col,
                            is_pipe_forward=False)) \
                            and (lbl := lookup(target)) is not None and not is_exempt(poff):
                        which = word.rsplit(".", 1)[-1]
                        hits.append((poff, f"Prod.{which} {target} (via let {target} := {lbl})"))
        elif tok.lastgroup == "ident" and "." in word:
            parts = word.split(".")
            lbl = lookup(parts[0])
            if lbl is not None and len(parts) >= 2 and COMPONENT_WORD.match(parts[1]):
                dot_off = tok.start() + len(parts[0])
                if not (len(parts) >= 3 and COMPONENT_WORD.match(parts[2])) \
                        and dot_off not in consumed_dots and not is_exempt(tok.start()):
                    hits.append((tok.start(),
                                 f"{parts[0]}.{parts[1]} (via let {parts[0]} := {lbl})"))
        elif tok.lastgroup == "ident" and "." not in word and (lbl := lookup(word)) is not None:
            if k + 3 < end and adj(k + 1, "|", ">") and _is_head_pos(text, tok.start()):
                rhs_tok = tokens[k + 3]
                if rhs_tok.lastgroup == "ident" and PROD_PROJ.fullmatch(rhs_tok[0]) \
                        and rhs_tok.start() not in consumed_prods and not is_exempt(tok.start()) \
                        and _rhs_ends(text, rhs_tok.end(), limit_char, rhs_tok.start(),
                                      first_line_col, is_pipe_forward=True):
                    which = rhs_tok[0].rsplit(".", 1)[-1]
                    hits.append((tok.start(),
                                 f"{word} |> Prod.{which} (via let {word} := {lbl})"))

    return hits


def mask_tactics(text: str) -> str:
    """Blank each `by` block to the end of its enclosing bracket group (or of `text`), and each
    `decreasing_by` or `termination_by` clause to the end of `text`, keeping offsets."""
    out, pos = list(text), 0
    while match := TACTIC.search(text, pos):
        end = _group_end(text, match.end()) if match[1] == "by" else len(text)
        for i in range(match.start(), end):
            if out[i] != "\n":
                out[i] = " "
        pos = max(end, match.end())
    return "".join(out)


def chains(text: str, first_line_col: int = 0) -> list[tuple[int, str]]:
    """The chains of masked source, as `(offset, chain)`, outside efficiency predicates."""
    exempt = [(m.start(), _group_end(text, m.end())) for m in EFFICIENCY.finditer(text)]
    prod_hits, consumed_prods, consumed_dots = _prod_chains(text, exempt, first_line_col)
    dot_hits = [(m.start(), m[1]) for m in CHAIN.finditer(text)
                if m.start() not in consumed_dots
                and not _is_numeric_proj(text, m.start())
                and not any(start <= m.start() < end for start, end in exempt)]
    let_hits = _let_alias_chains(text, exempt, consumed_prods, consumed_dots, first_line_col)
    return sorted(dot_hits + prod_hits + let_hits, key=lambda item: item[0])


def _may_have_chain(text: str) -> bool:
    """Fast sound pre-filter skipping files with no possible projection chain."""
    return (CHAIN.search(text) is not None
            or PROD_PROJ.search(text) is not None
            or (LET_KW.search(text) is not None and SINGLE_PROJ.search(text) is not None))


def module_chains(text: str) -> list[Chain]:
    """The counted chains of a Lean source file, in order."""
    found = []
    for command in cer.commands(text):
        keyword = command.keyword
        if keyword not in cer.DECLARATIONS or not command.public:
            continue
        attributes = {item.split()[0] for group in ATTRIBUTES.finditer(
            command.text[:command.keyword_start]) for item in group[1].split(",") if item.split()}
        if attributes & CERTIFICATE_ATTRIBUTES:
            continue
        name, pos, split = command.parts()
        source = command.text
        if keyword in cer.TYPE_DECLARATIONS:
            parts = [(pos, len(source))]  # fields and constructors are the statement
        elif keyword in BODY_KEYWORDS:
            if keyword in ("def", "abbrev") and ACCESSOR.fullmatch(mask_tactics(source[split:])):
                continue
            parts = [(pos, split), (split, len(source))]
        else:
            parts = [(pos, split)]
        name = name or f"{keyword}@{command.line}"
        for start, end in parts:
            line_start = command.syntax.rfind("\n", 0, command.start + start) + 1
            first_col = command.start + start - line_start
            for offset, chain in chains(mask_tactics(source[start:end]), first_col):
                line = command.syntax.count("\n", 0, command.start + start + offset) + 1
                found.append(Chain(name, line, chain))
    return found


def module_paths(root: Path, prefix: str = "") -> list[str]:
    """The checked modules under `prefix`, as paths relative to `root`."""
    parts = Path(prefix).parts
    return [path.relative_to(root).as_posix()
            for path in sorted((root / "CslibFrontier").rglob("*.lean"))
            if path.relative_to(root).parts[:len(parts)] == parts]


def _scan_one(args: tuple[Path, str]) -> tuple[str, list[Chain]]:
    root, rel = args
    path = root / rel
    if not path.is_file():
        return rel, []
    text = path.read_text(encoding="utf-8")
    if not _may_have_chain(text):  # masking only removes matches
        return rel, []
    try:
        rows = module_chains(text)
    except ValueError as error:
        raise ValueError(f"{rel}: {error}") from error
    return rel, rows


def scan(root: Path, paths: list[str], *, jobs: int | None = None) -> dict[str, list[Chain]]:
    """The counted chains of each of `paths` that exists and has any."""
    found: dict[str, list[Chain]] = {}
    worker_count = min(8, max(1, os.cpu_count() or 1)) if jobs is None else max(1, jobs)
    if worker_count > 1 and len(paths) >= 256 and sys.platform.startswith("linux"):
        import multiprocessing
        try:
            ctx = multiprocessing.get_context("fork")
            with ProcessPoolExecutor(max_workers=min(worker_count, len(paths)), mp_context=ctx) as pool:
                for rel, rows in pool.map(_scan_one, ((root, rel) for rel in paths), chunksize=64):
                    if rows:
                        found[rel] = rows
            return found
        except (OSError, PermissionError, RuntimeError):
            found.clear()
    for rel in paths:
        _, rows = _scan_one((root, rel))
        if rows:
            found[rel] = rows
    return found


def load_baseline(path: Path) -> dict[str, int]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not all(
            isinstance(k, str) and type(v) is int and v > 0 for k, v in data.items()):
        sys.exit(f"{path}: expected a JSON object from source paths to positive counts")
    return data


def baseline_text(counts: dict[str, int]) -> str:
    return json.dumps({k: v for k, v in sorted(counts.items()) if v}, indent=1) + "\n"


Change = tuple[str, int, int]  # (path, count, baseline entry or limit)


def compare(counts: dict[str, int], baseline: dict[str, int], paths: list[str],
            limits: dict[str, int] | None = None) -> tuple[list[Change], list[Change]]:
    """`(over, under)`: those of `paths` whose count exceeds their limit (by default their entry),
    with the limit, or falls short of their entry, with the entry. A missing count or entry is
    0."""
    limits = baseline if limits is None else limits
    over, under = [], []
    for path in sorted(paths):
        count, entry, cap = counts.get(path, 0), baseline.get(path, 0), limits.get(path, 0)
        if count > cap:
            over.append((path, count, cap))
        elif count < entry:
            under.append((path, count, entry))
    return over, under


def read_at(root: Path, revision: str, rel: str) -> str | None:
    """The text of `rel` at `revision`, or None when it is not there."""
    shown = subprocess.run(["git", "show", f"{revision}:{rel}"], cwd=root, capture_output=True)
    return shown.stdout.decode("utf-8") if shown.returncode == 0 else None


MergeBase = tuple[int, int | None]  # (entry at the merge base, count there or None if absent)


def merge_base_state(root: Path, base: str, baseline_rel: str | None, paths: list[str],
                     baseline: dict[str, int]) -> dict[str, MergeBase]:
    """The entry and the count of each of `paths` at `base`. Without a baseline at `base`, the
    current entries stand in, which keeps every entry capped."""
    old_text = read_at(root, base, baseline_rel) if baseline_rel else None
    old = json.loads(old_text) if old_text else baseline
    state = {}
    for path in paths:
        text = read_at(root, base, path)
        try:
            count = None if text is None else len(module_chains(text)) if _may_have_chain(text) else 0
        except ValueError as error:
            raise ValueError(f"{path} at {base}: {error}") from error
        state[path] = (old.get(path, 0), count)
    return state


def limit(entry: int, old_entry: int, base_count: int | None) -> int:
    """A module's limit given its entry: the entry, capped at the count at the merge base unless
    the module is new there or the entry is above its value there."""
    return entry if base_count is None or entry > old_entry else min(entry, base_count)


def unrecordable(over: list[Change], state: dict[str, MergeBase] | None) -> list[Change]:
    """Those of `over` that recording their count as the entry would leave over the limit."""
    return [change for change in over
            if state is not None and limit(change[1], *state[change[0]]) < change[1]]


def over_report(over: list[Change], found: dict[str, list[Chain]],
                baseline: dict[str, int] | None = None,
                state: dict[str, MergeBase] | None = None) -> str:
    out = ["Public statements and the bodies of public definitions bind tuple components by name "
           f"instead of chaining positional projections such as `c.1.2` (#1764; {RULE}). These "
           "modules have more chains than their limit; the counted chains are:", ""]
    for path, count, cap in over:
        entry = cap if baseline is None else baseline.get(path, 0)
        bound = (f"baseline {entry}" if cap == entry
                 else f"limit {cap} (the count at the merge base; baseline {entry})")
        out.append(f"{path}: {count} chain(s), {bound}:")
        out += [f"  {path}:{row.line}: {row.declaration}: `{row.chain}`"
                for row in found.get(path, [])]
    stuck = unrecordable(over, state)
    if stuck:
        out += ["", "Recording these counts with `--update-baseline` would not raise the entry above "
                "its value at the merge base, so the limit would stay the count there. Remove the "
                "chains or, to add them back on purpose, raise the entry by hand above its value at "
                "the merge base, so that the raise is visible in review:"]
        out += [f"  {path}: above {state[path][0]}" for path, _, _ in stuck]
    return "\n".join(out)


def under_report(under: list[Change]) -> str:
    return "\n".join(f"  {path}: {count} (baseline {entry})" for path, count, entry in under)


def listing(found: dict[str, list[Chain]]) -> str:
    total = sum(len(rows) for rows in found.values())
    out = [f"{total} counted projection chain(s) in {len(found)} module(s)."]
    for path, rows in sorted(found.items(), key=lambda item: (-len(item[1]), item[0])):
        out += ["", f"{path}: {len(rows)}"]
        by_declaration: dict[str, list[Chain]] = defaultdict(list)
        for row in rows:
            by_declaration[row.declaration].append(row)
        for name, chain_rows in by_declaration.items():
            out.append(f"  {path}:{chain_rows[0].line}: {name}: "
                       + " ".join(f"`{row.chain}`" for row in chain_rows))
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="enforce in the modules changed since the merge base with this "
                            "revision (default origin/main)")
    scope.add_argument("--all", action="store_true", help="enforce in every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help="ignore the baseline and list every counted chain in the modules "
                            "under the path PREFIX, or in every module; always succeeds")
    parser.add_argument("--update-baseline", action="store_true",
                        help="lower the baseline entries of the enforced modules")
    parser.add_argument("--allow-increase", action="store_true",
                        help="with --update-baseline, allow adding and raising entries")
    parser.add_argument("--root", type=Path, default=ROOT, help="the repository to check")
    parser.add_argument("--baseline", type=Path, help="default: the root's baseline file")
    args = parser.parse_args(argv)
    if args.allow_increase and not args.update_baseline:
        parser.error("--allow-increase needs --update-baseline")
    if (args.report or args.list is not None) and args.update_baseline:
        parser.error("--report and --list do not combine with --update-baseline")
    if args.list is not None:
        print(listing(scan(args.root, module_paths(args.root, args.list))))
        return 0
    baseline_path = args.baseline or args.root / BASELINE.relative_to(ROOT)
    baseline = load_baseline(baseline_path) if baseline_path.exists() else {}
    whole = args.all or args.report
    paths = (sorted(set(module_paths(args.root)) | set(baseline)) if whole
             else sorted(cer.touched_modules(args.root, args.base)))
    found = scan(args.root, paths)
    counts = {path: len(rows) for path, rows in found.items()}
    state = limits = None
    if not whole:
        try:
            baseline_rel = baseline_path.resolve().relative_to(args.root.resolve()).as_posix()
        except ValueError:
            baseline_rel = None
        state = merge_base_state(args.root, ccf.comparison_base(args.root, args.base),
                                 baseline_rel, paths, baseline)
        limits = {path: limit(baseline.get(path, 0), *state[path]) for path in paths}
    over, under = compare(counts, baseline, paths, limits)
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    status = (f"{sum(counts.values())} counted projection chain(s) in {len(counts)} module(s), "
              f"checking {scope_text}")
    if args.report:
        if over:
            print(over_report(over, found))
        if under:
            print(("\n" if over else "") + "Entries above the current count:\n"
                  + under_report(under))
        print(("\n" if over or under else "") + f"{status}; report only, nothing is enforced.")
        return 0
    if args.update_baseline:
        stuck = unrecordable(over, state)
        if stuck:
            print(over_report(stuck, found, baseline, state), file=sys.stderr)
            return 1
        if over and not args.allow_increase:
            print(over_report(over, found, baseline), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module.", file=sys.stderr)
            return 1
        updated = dict(baseline)
        for path in paths:
            updated[path] = counts.get(path, 0)
        baseline_path.write_text(baseline_text(updated), encoding="utf-8")
        print(f"Wrote {baseline_path} for {scope_text}: {status}.")
        return 0
    if under:
        print("Projection chains were removed. No baseline edit is needed: the check caps each "
              "changed module at its count at the merge base, and stale entries are pruned "
              f"periodically with `{UPDATE} --all`:\n" + under_report(under))
    if over:
        print(("\n" if under else "") + over_report(over, found, baseline, state),
              file=sys.stderr)
        return 1
    print(f"{status}; none exceeds its limit.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
