#!/usr/bin/env python3
"""The line format of `manual/sources.md`: each sentence of a paragraph or list item on its own
line.

Many pull requests add a sentence to the same bibliography entry, and when an entry's prose is
one long line any two of them conflict, even when they add different sentences. In the line
format each sentence starts a line, so independent edits touch different lines. GitHub's
Markdown and the Pandoc reader of the PDF build both join the lines of a paragraph with spaces,
so the file renders exactly as it would with each paragraph on one line.

`canonical(text)` writes `text` in this format. It joins the lines of each paragraph and of
each list item and splits the result after every sentence end: `.`, `?` or `!`, possibly followed
by closing quotes, brackets or emphasis, then one space and the start of a sentence (a capital
letter, `[`, `(`, `*`, `` ` ``, `§` or an opening quote). It does not split inside code spans,
`$...$` math or HTML tags, after an initial or a common abbreviation, or where the next line
could start another Markdown block. Continuation lines of a list item are indented to its text.
Headings, anchors, blank lines, fenced code, HTML comments and every other kind of block
are kept as they are. The result joins back to the same text: `canonical` refuses to return
output whose words or punctuation differ from its input apart from line breaks and the
indentation of list continuation lines.

    python3 scripts/sources_format.py --check [FILE]      # exit 1 if FILE is not in the format
    python3 scripts/sources_format.py --write [FILE]      # rewrite FILE in the format
    python3 scripts/sources_format.py --compare OLD NEW   # same text apart from line breaks?

FILE defaults to `manual/sources.md`. `scripts/resolve_sources_conflict.py`, the file's merge
driver, uses `canonical` to merge versions written before and after the conversion.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "manual" / "sources.md"

# A list item: its marker and the text after it.
LIST_ITEM = re.compile(r"(?P<marker>(?:[-*+]|\d{1,9}[.)])[ ]+)(?P<text>\S.*)")
# Lines that are kept as they are and end any paragraph: blank lines, anchors and other HTML,
# headings, block quotes, tables, fences, thematic breaks, indented code and Pandoc's `:::` divs.
OPAQUE = re.compile(r"\s*$|<|#|>|\||```|~~~|:::|( {4}|\t)|([-*_])( *\2){2,} *$")
# The opening line of a fenced code block, whose lines up to the closing fence are kept.
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
# The end of a sentence: the last word before a split ends this way.
SENTENCE_END = re.compile(r"(?P<word>\S*?)[.?!][\"”’)\]*_]*")
# Words that end with a period without ending a sentence, compared without case: Pandoc's own
# list (`pandoc --print-default-data-file abbreviations`), after which its `smart` extension
# writes a non-breaking space that a line break would lose, and a few more.
ABBREVIATIONS = frozenset("""
    aet aetat al apr aug bk bros c capt cf ch chap chs co col corp cp d dec dr e.g ed eds esp f
    fasc feb ff fig fl fol fols fr gen gov hon i.e ill inc incl jan jr jul jun ltd m.a m.d mar mr
    mrs ms n n.b nn no nov oct p ph.d pp pres prof pt q.v rep rev s.v s.vv saec sec sen sep sept
    sgt sr st univ viz vol vs
    approx art cor def dept eq eqs etc ex figs lem nos op prop resp secs thm vols""".split())
# Characters that may start a sentence line (with the exceptions in `starts_sentence`).
STARTERS = frozenset("[(*_`§\"“‘")
# How much of the text after a space `starts_sentence` reads.
LOOKAHEAD = 200


def protected(text: str) -> list[tuple[int, int]]:
    """The spans of `text` that are never split: code spans, `$...$` math and HTML tags."""
    spans: list[tuple[int, int]] = []
    # A code span runs from a backtick string to the next one of the same length.
    runs = list(re.finditer(r"`+", text))
    following, latest = [None] * len(runs), {}
    for k in range(len(runs) - 1, -1, -1):
        following[k] = latest.get(len(runs[k].group()))
        latest[len(runs[k].group())] = k
    k = 0
    while k < len(runs):
        close = following[k]
        if close is None:
            k += 1
            continue
        spans.append((runs[k].start(), runs[close].end()))
        k = close + 1

    def free(i: int) -> bool:
        return not any(a <= i < b for a, b in spans)

    # Pandoc's `tex_math_dollars`: `$` before a non-space opens, `$` after one closes unless a
    # digit follows.
    i, math = 0, []
    while (start := text.find("$", i)) != -1:
        i = start + 1
        if not free(start) or (start and text[start - 1] == "\\"):
            continue
        if start + 1 >= len(text) or text[start + 1].isspace():
            continue
        end = start + 1
        while (end := text.find("$", end + 1)) != -1:
            if (not text[end - 1].isspace() and text[end - 1] != "\\"
                    and not text[end + 1:end + 2].isdigit()):
                break
        if end == -1:
            continue
        math.append((start, end + 1))
        i = end + 1
    spans += math
    spans += [(m.start(), m.end()) for m in re.finditer(r"<[^<>]*>", text) if free(m.start())]
    return spans


def ends_sentence(word: str) -> bool:
    """Whether `word`, the last word before a space, ends a sentence."""
    match = SENTENCE_END.fullmatch(word)
    if not match:
        return False
    word = match.group("word").lstrip("([\"“‘*_").rstrip(".")
    if not word:
        return False
    if len(word) == 1 and word.isalpha():  # an initial, or `p.` before a page number
        return False
    return word.casefold() not in ABBREVIATIONS


def starts_sentence(after: str) -> bool:
    """Whether `after`, the text after a space, may start a line inside a paragraph without
    starting another Markdown block in GitHub's or Pandoc's reading."""
    first = after[:1]
    if not first:
        return False
    if first.isupper():
        return True
    if first not in STARTERS:
        return False
    if first in "*_" and (after[1:2] in ("", " ") or OPAQUE.match(after)):
        return False
    if first == "`" and after.startswith("```"):
        return False
    if first == "[" and (after.startswith("[^") or re.match(r"\[[^\]]*\]:", after)):
        return False
    return True


def sentences(text: str) -> list[str]:
    """Split one paragraph's text into sentence lines; joining them with spaces gives `text`."""
    shielded = bytearray(len(text))
    for a, b in protected(text):
        shielded[a:b] = b"\1" * (b - a)
    pieces, start = [], 0
    for space in re.finditer(r" (?=\S)", text):
        i = space.start()
        if shielded[i]:
            continue
        word = max(start, text.rfind(" ", start, i) + 1)
        if ends_sentence(text[word:i]) and starts_sentence(text[i + 1:i + 1 + LOOKAHEAD]):
            pieces.append(text[start:i])
            start = i + 1
    pieces.append(text[start:])
    return pieces


def hard_break(line: str) -> bool:
    """Whether a line ends with a hard line break, which joining would remove."""
    return line.endswith("  ") or line.endswith("\\")


def canonical(text: str) -> str:
    """`text` in the line format; see the module docstring."""
    if text and not text.endswith("\n"):
        text += "\n"
    lines = text.split("\n")[:-1]
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        item = LIST_ITEM.fullmatch(line)
        if fence := FENCE.match(line):  # a fenced code block, kept up to its closing fence
            close = re.compile(rf" {{0,3}}{re.escape(fence.group(1)[0])}{{{len(fence.group(1))},}}"
                               r"\s*$")
            j = next((k for k in range(i + 1, len(lines)) if close.match(lines[k])), len(lines))
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        if line.lstrip(" ").startswith("<!--"):  # an HTML comment, kept up to its end
            j = next((k for k in range(i, len(lines)) if "-->" in lines[k][4 * (k == i):]),
                     len(lines))
            out.extend(lines[i:j + 1])
            i = j + 1
            continue
        if (OPAQUE.match(line) and not item) or line[:1].isspace():
            out.append(line)  # another kind of block, or an indented line outside a list item
            i += 1
            continue
        # A paragraph or top-level list item: this line and its continuation lines, up to a
        # blank line, another list item or a line that starts another block.
        j = i + 1
        while (j < len(lines) and lines[j].strip() and not LIST_ITEM.fullmatch(lines[j])
               and not (OPAQUE.match(lines[j]) and not lines[j][:1].isspace())):
            j += 1
        block = lines[i:j]
        marker = item.group("marker") if item else ""
        indent = " " * len(marker)
        # Kept as they are: a hard line break, which joining would remove, and indentation other
        # than that of an item's text (a nested list, code or a paragraph's indented line).
        if any(hard_break(part) for part in block[:-1]) or any(
                part[:1].isspace() and (not item or not part.startswith(indent)
                                        or part[len(indent):][:1].isspace()
                                        or LIST_ITEM.fullmatch(part.lstrip()))
                for part in block[1:]):
            out.extend(block)
            i = j
            continue
        joined = " ".join(part.strip() for part in [block[0][len(marker):], *block[1:]])
        split = sentences(joined)
        out.append(marker + split[0])
        out.extend(indent + piece for piece in split[1:])
        i = j
    result = "".join(f"{line}\n" for line in out)
    if words(result) != words(text):
        raise ValueError("the line format would change the text; this is a bug in sources_format")
    return result


def words(text: str) -> list[str]:
    """`text` without line structure: its whitespace-separated words, in order."""
    return text.split()


def compare(old: str, new: str) -> list[str]:
    """Differences between `old` and `new` other than line breaks and indentation."""
    a, b = words(old), words(new)
    if a == b:
        return []
    k = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    return [f"word {k + 1} differs: {' '.join(a[max(0, k - 5):k + 5])!r} became "
            f"{' '.join(b[max(0, k - 5):k + 5])!r} ({len(a)} words before, {len(b)} after)"]


def unformatted(text: str) -> list[int]:
    """The 1-based numbers of the lines that `canonical` would change."""
    import difflib

    old, new = text.split("\n"), canonical(text).split("\n")
    changed: list[int] = []
    for tag, i1, i2, _, _ in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag != "equal":
            changed.extend(range(i1 + 1, max(i1, i2 - 1) + 2))
    return sorted(set(changed))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="report lines not in the format")
    mode.add_argument("--write", action="store_true", help="rewrite the file in the format")
    mode.add_argument("--compare", nargs=2, metavar=("OLD", "NEW"), type=Path,
                      help="check that NEW has the text of OLD apart from line breaks")
    parser.add_argument("file", nargs="?", type=Path, default=SOURCES)
    args = parser.parse_args(argv)
    if args.compare:
        old, new = (path.read_text(encoding="utf-8") for path in args.compare)
        differences = compare(old, new)
        for difference in differences:
            print(f"sources_format: {difference}")
        if not differences:
            print(f"sources_format: {args.compare[1]} has the text of {args.compare[0]} "
                  f"({len(words(old))} words) apart from line breaks and indentation")
        return 1 if differences else 0
    text = args.file.read_text(encoding="utf-8")
    if args.write:
        formatted = canonical(text)
        if formatted != text:
            args.file.write_text(formatted, encoding="utf-8")
        return 0
    lines = unformatted(text)
    if lines:
        shown = ", ".join(map(str, lines[:20])) + (", ..." if len(lines) > 20 else "")
        print(f"{args.file}: not one sentence per line at line {shown}; "
              f"run `python3 scripts/sources_format.py --write {args.file}`")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
