#!/usr/bin/env python3
"""Conservatively select whether the Guide workflow must compile and/or render.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

Outputs two GitHub Actions step outputs when `$GITHUB_OUTPUT` is set:
- `render=true|false`: render the Verso site pages and upload the `guide` artifact.
- `check=true|false`: restore Lean caches and compile `CslibFrontierGuide`.

On non-`pull_request` events (such as `workflow_dispatch`), both are `true`. On `pull_request`:
- `render=true` whenever any guide/rendering/pin file changed (`RENDER_PREFIXES`/`RENDER_FILES`).
- `check=false` only when `render=false`, every changed file is a safe `A`/`M` addition or edit,
  no changed `CslibFrontier` module lies inside `guide/`'s transitive `CslibFrontier.*` import
  closure, and any edit to `CslibFrontier.lean` only inserts import lines for newly added modules.
- Any deletion, rename, symlink, unparseable header, missing local module, unfetchable base,
  non-Lean config change, or ambiguous layout fails closed (`check=true`).
"""

from __future__ import annotations

from collections import deque
import os
from pathlib import Path
import re
import subprocess
import sys


RENDER_FILES = frozenset({
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "scripts/guide.sh",
    "scripts/check_docs.py",
    "scripts/ci/select_guide.py",
    ".github/workflows/guide.yml",
})
RENDER_DIRS = (
    "guide/",
    ".github/actions/install-lean/",
    ".github/actions/cache-guide-deps/",
)
# Only files under these paths are allowed outside the guide's import closure when skipping `check`.
SAFE_NON_LIBRARY_PATHS = frozenset({
    "README.md",
    "AGENTS.md",
    "CONTRIBUTING.md",
    "ROADMAP.md",
    "references.bib",
})
SAFE_NON_LIBRARY_DIRS = (
    "CslibFrontierTests/",
    "CslibFrontierResults/",
    "policy/",
    "results/",
    "roadmap/",
    "manual/",
)
class AmbiguousHeader(ValueError):
    """A Lean header could not be parsed conservatively without invoking Lean."""


def _is_letter_like(cp: int) -> bool:
    """Match `Lean.isLetterLike` from `Init/Meta/Defs.lean`."""
    return (
        (0x03B1 <= cp <= 0x03C9 and cp != 0x03BB)
        or (0x0391 <= cp <= 0x03A9 and cp not in (0x03A0, 0x03A3))
        or (0x03CA <= cp <= 0x03FB)
        or (0x1F00 <= cp <= 0x1FFE)
        or (0x2100 <= cp <= 0x214F)
        or (0x1D49C <= cp <= 0x1D59F)
        or (0x00C0 <= cp <= 0x00FF and cp not in (0x00D7, 0x00F7))
        or (0x0100 <= cp <= 0x017F)
    )


def _is_subscript_alnum(cp: int) -> bool:
    """Match `Lean.isSubScriptAlnum` from `Init/Meta/Defs.lean`."""
    return (
        (0x2080 <= cp <= 0x2089)
        or (0x2090 <= cp <= 0x209C)
        or (0x1D62 <= cp <= 0x1D6A)
        or cp == 0x2C7C
    )


def _is_id_first(ch: str) -> bool:
    """Match `Lean.isIdFirst` (`Char.isAlpha` in Lean is ASCII-only)."""
    return ("a" <= ch <= "z") or ("A" <= ch <= "Z") or ch == "_" or _is_letter_like(ord(ch))


def _is_id_rest(ch: str) -> bool:
    """Match `Lean.isIdRest` (`Char.isAlphanum` in Lean is ASCII-only)."""
    return (
        ("a" <= ch <= "z")
        or ("A" <= ch <= "Z")
        or ("0" <= ch <= "9")
        or ch in ("_", "'", "!", "?")
        or _is_letter_like(ord(ch))
        or _is_subscript_alnum(ord(ch))
    )


def _is_unquoted_ident(part: str) -> bool:
    return bool(part) and _is_id_first(part[0]) and all(_is_id_rest(c) for c in part[1:])


def is_unquoted_module_name(mod: str) -> bool:
    parts = mod.split(".")
    return bool(parts) and all(_is_unquoted_ident(p) for p in parts)


def _at_token_boundary(text: str, pos: int) -> bool:
    return (
        pos >= len(text)
        or text[pos] in (" ", "\r", "\n")
        or text.startswith(("--", "/-"), pos)
    )


def _skip_ws_and_comments(text: str, pos: int) -> tuple[int, bool]:
    """Advance past header spaces/newlines, `--` line comments, and nested `/- -/` block comments.

    Returns `(next_pos, stopped_at_doc_or_eof)` where `stopped_at_doc_or_eof` is `True` at EOF or
    at the start of a docstring (`/-!`, `/--` excluding `/---` dividers). Raises `AmbiguousHeader`
    on tabs, non-ASCII whitespace, or unterminated block comments.
    """
    n = len(text)
    i = pos
    while i < n:
        ch = text[i]
        if ch in (" ", "\r", "\n"):
            i += 1
            continue
        if ch == "\t" or ch.isspace():
            raise AmbiguousHeader("unsupported whitespace in module header")
        if ch == "-" and i + 1 < n and text[i + 1] == "-":
            end = text.find("\n", i + 2)
            if end < 0:
                return n, True
            i = end + 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "-":
            if text.startswith(("/-!", "/--"), i) and not text.startswith("/---", i):
                return i, True
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth != 0:
                raise AmbiguousHeader("unterminated block comment in module header")
            continue
        return i, False
    return n, True


def _read_word(text: str, pos: int) -> tuple[str | None, int]:
    if pos < len(text) and _is_id_first(text[pos]):
        j = pos + 1
        n = len(text)
        while j < n and _is_id_rest(text[j]):
            j += 1
        return text[pos:j], j
    return None, pos


def _parse_module_ident(text: str, pos: int) -> tuple[str, int]:
    """Parse a `.`-separated Lean `moduleIdent` (including `'`, Unicode, and safe `«...»` parts).

    Raises `AmbiguousHeader` on missing/malformed components, quoted components containing `.` or
    path/control characters (which would make `.`-joined module names ambiguous), or any unexpected
    continuation character immediately following the module name.
    """
    n = len(text)
    i = pos
    parts: list[str] = []
    while True:
        if i >= n:
            raise AmbiguousHeader("unexpected end of input in module import")
        if text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                raise AmbiguousHeader("unterminated quoted identifier in module header")
            part = text[i + 1 : end]
            if (
                not part
                or part in (".", "..")
                or any(c in ("«", ".", "/", "\\", "\0", "\r", "\n", "\t") for c in part)
            ):
                raise AmbiguousHeader(f"unsupported quoted module component: {part!r}")
            parts.append(part)
            i = end + 1
        elif _is_id_first(text[i]):
            j = i + 1
            while j < n and _is_id_rest(text[j]):
                j += 1
            parts.append(text[i:j])
            i = j
        else:
            raise AmbiguousHeader(f"unsupported import target at {text[i:i + 16]!r}")
        if i < n and text[i] == ".":
            i += 1
            if i >= n:
                raise AmbiguousHeader("trailing dot in module import")
            continue
        if not _at_token_boundary(text, i):
            raise AmbiguousHeader(f"unexpected continuation {text[i]!r} after module name")
        break
    return ".".join(parts), i


def parse_header_imports_text(text: str) -> list[str]:
    """Return all imported module names from a Lean 4 module header.

    Supports Lean's token-based header grammar: optional `module` / `prelude` followed by
    `[public | private] [meta] import [all] <module>`, including line breaks, `--` comments,
    nested `/- ... -/` block comments, full Lean identifier characters (`'`, `!`, `?`, `_`,
    Unicode letters/subscripts), and single-segment `«...»` escapes. Raises `AmbiguousHeader` on
    any unsupported continuation, malformed modifier ordering, or ambiguous quoted component.
    """
    imports: list[str] = []
    pos = 0
    seen_import = False
    seen_module = False
    seen_prelude = False
    while True:
        pos, ended = _skip_ws_and_comments(text, pos)
        if ended:
            break
        word, nxt = _read_word(text, pos)
        if word is None:
            if text[pos] in (".", "«"):
                raise AmbiguousHeader(f"unexpected header token starting with {text[pos]!r}")
            break
        if not seen_import and word == "module" and not seen_module and not seen_prelude:
            if not _at_token_boundary(text, nxt):
                raise AmbiguousHeader("unexpected continuation after 'module'")
            seen_module = True
            pos = nxt
            continue
        if not seen_import and word == "prelude" and not seen_prelude:
            if not _at_token_boundary(text, nxt):
                raise AmbiguousHeader("unexpected continuation after 'prelude'")
            seen_prelude = True
            pos = nxt
            continue
        cur = nxt
        if word in ("public", "private"):
            if not _at_token_boundary(text, cur):
                raise AmbiguousHeader(f"unexpected continuation after {word!r}")
            cur, ended = _skip_ws_and_comments(text, cur)
            if ended:
                break
            word, cur = _read_word(text, cur)
            if word is None:
                break
        if word == "meta":
            if not _at_token_boundary(text, cur):
                raise AmbiguousHeader("unexpected continuation after 'meta'")
            cur, ended = _skip_ws_and_comments(text, cur)
            if ended:
                break
            word, cur = _read_word(text, cur)
            if word is None:
                break
            if word in ("public", "private"):
                after_vis, ended2 = _skip_ws_and_comments(text, cur)
                if not ended2:
                    nxt_word, _ = _read_word(text, after_vis)
                    if nxt_word == "import":
                        raise AmbiguousHeader("unexpected modifier ordering before import")
                break
        if word != "import":
            # Fail closed if an unrecognized/misordered modifier immediately precedes `import`.
            if _at_token_boundary(text, cur):
                peek_pos, peek_ended = _skip_ws_and_comments(text, cur)
                if not peek_ended:
                    peek_word, _ = _read_word(text, peek_pos)
                    if peek_word == "import":
                        raise AmbiguousHeader(f"unexpected modifier {word!r} before import")
            break
        if not _at_token_boundary(text, cur):
            raise AmbiguousHeader("unexpected continuation after 'import'")
        seen_import = True
        cur, ended = _skip_ws_and_comments(text, cur)
        if ended:
            raise AmbiguousHeader("missing module name after import")
        if text.startswith("all", cur):
            if not _at_token_boundary(text, cur + 3):
                raise AmbiguousHeader("ambiguous 'all' prefix in import target")
            cur, ended = _skip_ws_and_comments(text, cur + 3)
            if ended:
                raise AmbiguousHeader("missing module name after 'import all'")
        mod, cur = _parse_module_ident(text, cur)
        imports.append(mod)
        pos = cur
    return imports


def parse_header_imports(path: Path) -> list[str]:
    """Return all imported module names from a Lean file's header.

    Raises `AmbiguousHeader` on any unsupported `import` syntax, ambiguous `«...»` component,
    unterminated block comment, symlink, or missing file.
    """
    if path.is_symlink():
        raise AmbiguousHeader(f"symlinked source: {path}")
    return parse_header_imports_text(path.read_text(encoding="utf-8"))


def guide_import_closure(root: Path) -> set[str]:
    """Return every `CslibFrontier` module transitively imported by `guide/**/*.lean`."""
    guide_dir = root / "guide"
    if guide_dir.is_symlink() or not guide_dir.is_dir():
        raise AmbiguousHeader("missing or symlinked guide directory")
    guide_files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(guide_dir, followlinks=False):
        current = Path(dirpath)
        for d in sorted(dirnames):
            if (current / d).is_symlink():
                raise AmbiguousHeader(f"symlinked guide directory: {current / d}")
        for fname in sorted(filenames):
            if fname.endswith(".lean"):
                p = current / fname
                if p.is_symlink():
                    raise AmbiguousHeader(f"symlinked source: {p}")
                guide_files.append(p)
    guide_files.sort()
    if not guide_files:
        raise AmbiguousHeader("no Lean files under guide/")
    closure: set[str] = set()
    queue: deque[str] = deque()
    for gf in guide_files:
        for mod in parse_header_imports(gf):
            if mod == "CslibFrontier" or mod.startswith("CslibFrontier."):
                if mod not in closure:
                    closure.add(mod)
                    queue.append(mod)
    lib_dir = root / "CslibFrontier"
    if lib_dir.is_symlink():
        raise AmbiguousHeader("symlinked CslibFrontier directory")
    while queue:
        mod = queue.popleft()
        if mod == "CslibFrontier":
            # Importing the root aggregate drags in the entire library.
            raise AmbiguousHeader("guide transitively imports the root aggregate CslibFrontier")
        rel = Path(*mod.split(".")).with_suffix(".lean")
        target = root / rel
        if not target.is_file() or target.is_symlink():
            raise AmbiguousHeader(f"missing or symlinked imported module: {rel.as_posix()}")
        if not target.resolve().is_relative_to(root.resolve()):
            raise AmbiguousHeader(f"module path escapes repository: {rel.as_posix()}")
        for dep in parse_header_imports(target):
            if dep == "CslibFrontier" or dep.startswith("CslibFrontier."):
                if dep not in closure:
                    closure.add(dep)
                    queue.append(dep)
    return closure


def _parse_aggregate_import_line(line: str) -> str | None:
    for prefix in ("public import ", "import "):
        if line.startswith(prefix):
            mod = line[len(prefix):]
            if is_unquoted_module_name(mod):
                return mod
            return None
    return None


def only_adds_imports(old: str, new: str, added_modules: set[str]) -> bool:
    """Whether `new` equals `old` with only import lines for `added_modules` inserted."""
    rest: list[str] = []
    imported: set[str] = set()
    for line in new.split("\n"):
        mod = _parse_aggregate_import_line(line)
        if mod and mod in added_modules and mod not in imported:
            imported.add(mod)
        else:
            rest.append(line)
    return bool(imported) and rest == old.split("\n")


def is_render_trigger(path: str) -> bool:
    if path in RENDER_FILES:
        return True
    return any(path.startswith(prefix) for prefix in RENDER_DIRS)


def is_safe_non_library(path: str) -> bool:
    if path in SAFE_NON_LIBRARY_PATHS:
        return True
    return any(path.startswith(prefix) for prefix in SAFE_NON_LIBRARY_DIRS)


def _git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args], cwd=root, text=True, capture_output=True, check=False,
    )


def ensure_base_commit(root: Path, base_sha: str) -> None:
    """Ensure `base_sha` exists in a shallow checkout (fetching depth=1 from origin if absent)."""
    if not re.fullmatch(r"[0-9a-f]{40}", base_sha):
        raise ValueError(f"invalid GUIDE_BASE_SHA: {base_sha!r}")
    present = _git(root, "cat-file", "-e", f"{base_sha}^{{commit}}")
    if present.returncode != 0:
        fetched = _git(root, "fetch", "--no-tags", "--depth=1", "origin", base_sha)
        if fetched.returncode != 0:
            raise subprocess.CalledProcessError(
                fetched.returncode, fetched.args, output=fetched.stdout, stderr=fetched.stderr,
            )


def resolve_pr_base(root: Path, base_sha: str) -> str:
    """Return the comparison base commit for a pull request checkout.

    On a GitHub `pull_request` synthetic merge commit (`HEAD` has >=2 parents), the first parent is
    the target branch tip used to form `refs/pull/<n>/merge`; comparing against it avoids blaming
    unrelated commits merged onto `main` after `pull_request.base.sha`. For single-parent commits
    (such as direct branch checkouts and tests), compare against `base_sha`.
    """
    head_obj = _git(root, "cat-file", "-p", "HEAD")
    if head_obj.returncode == 0:
        parents: list[str] = []
        for line in head_obj.stdout.splitlines():
            if not line:
                break
            if line.startswith("parent "):
                parents.append(line.split(" ", 1)[1].strip())
        if len(parents) >= 2 and re.fullmatch(r"[0-9a-f]{40}", parents[0]):
            return parents[0]
    return base_sha


def select_mode(root: Path, event: str, base_sha: str) -> tuple[bool, bool, str]:
    """Return `(check, render, reason)` for the workflow run.

    Raises on missing/unfetchable `GUIDE_BASE_SHA` on `pull_request` (matching existing behavior).
    Otherwise any ambiguity fails closed (`check=True`).
    """
    if event != "pull_request":
        return True, True, f"event is {event or 'unknown'}"
    cmp_base = resolve_pr_base(root, base_sha)
    ensure_base_commit(root, cmp_base)
    diff = _git(root, "diff", "--no-ext-diff", "--no-renames", "--name-status", "-z", cmp_base, "HEAD", "--")
    if diff.returncode != 0:
        return True, True, f"git diff failed: {diff.stderr.strip()}"
    parts = diff.stdout.split("\0")
    if parts and parts[-1] == "":
        parts = parts[:-1]
    if len(parts) % 2:
        return True, True, "unexpected git diff format"
    changes = list(zip(parts[::2], parts[1::2]))
    if not changes:
        return False, False, "no changed files against base"

    # First check explicit guide/tooling render triggers (same set checked even on D/R statuses).
    changed_render = [p for _, p in changes if is_render_trigger(p)]
    if changed_render:
        return True, True, f"render trigger changed: {changed_render[0]}"

    # From here render=False; decide whether we may safely skip compiling `CslibFrontierGuide`.
    if not (root / "guide").is_dir():
        return True, False, "guide/ directory absent; keeping compilation enabled"

    added_lib_modules: set[str] = set()
    touched_lib_modules: list[tuple[str, str]] = []
    agg_changed = False
    for status, path in changes:
        if status not in ("A", "M"):
            return True, False, f"non-add/modify change ({status}): {path}"
        if path == "CslibFrontier.lean":
            agg_changed = True
            continue
        if path.startswith("CslibFrontier/") and path.endswith(".lean"):
            mod_parts = Path(path).with_suffix("").parts
            if not all(_is_unquoted_ident(p) for p in mod_parts):
                return True, False, f"unsupported library path: {path}"
            mod = ".".join(mod_parts)
            if status == "A":
                added_lib_modules.add(mod)
            touched_lib_modules.append((status, mod))
            continue
        if is_safe_non_library(path):
            continue
        return True, False, f"non-library path requires conservative check: {path}"

    if agg_changed:
        base_agg = _git(root, "show", f"{cmp_base}:CslibFrontier.lean")
        agg_path = root / "CslibFrontier.lean"
        if base_agg.returncode != 0 or not agg_path.is_file() or agg_path.is_symlink():
            return True, False, "cannot verify CslibFrontier.lean diff"
        if not only_adds_imports(base_agg.stdout, agg_path.read_text(encoding="utf-8"), added_lib_modules):
            return True, False, "CslibFrontier.lean changed beyond added module imports"

    try:
        closure = guide_import_closure(root)
    except (AmbiguousHeader, OSError, UnicodeDecodeError) as error:
        return True, False, f"conservative check ({error})"

    overlapping = [mod for _, mod in touched_lib_modules if mod in closure]
    if overlapping:
        return True, False, f"{len(overlapping)} changed module(s) in guide closure (e.g. {overlapping[0]})"

    return (
        False,
        False,
        f"no changed module in CslibFrontierGuide import closure ({len(closure)} modules checked)",
    )


def main() -> int:
    root = Path.cwd()
    event = os.environ.get("GITHUB_EVENT_NAME", "")
    base_sha = os.environ.get("GUIDE_BASE_SHA", "")
    try:
        check, render, reason = select_mode(root, event, base_sha)
    except (ValueError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"Guide selection: check={str(check).lower()} render={str(render).lower()} ({reason})")
    out_path = os.environ.get("GITHUB_OUTPUT")
    if out_path:
        with Path(out_path).open("a", encoding="utf-8") as handle:
            handle.write(f"check={str(check).lower()}\n")
            handle.write(f"render={str(render).lower()}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
