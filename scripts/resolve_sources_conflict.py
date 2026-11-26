#!/usr/bin/env python3
"""Git merge driver for `manual/sources.md`: merge its entries by key and their lines three ways.

`manual/sources.md` is a list of entries, each an anchor line `<a id="key"></a>`, the heading
`## key` and the entry's prose, separated by one blank line and preceded by the page's preamble.
Pull requests often add or change different sentences of the same entry, or add entries next to
each other. A text merge reports such changes as conflicts when they touch adjacent lines or add
lines at the same place; this driver merges them.

It reads the three versions as the preamble and the entries in order, and merges

- the order of the entries three ways: entries that both sides add at the same place are
  interleaved in key order, and an entry that one side deletes stays deleted unless the other
  side changed it;
- the lines of the preamble and of each entry three ways: changes that touch different lines of
  the base merge even when the lines are adjacent, and disjoint runs of lines that both sides
  insert at the same place are kept as two runs, in a fixed order (a run that starts a new
  paragraph after one that continues the paragraph, and otherwise in text order).

Both rules are symmetric, so the result does not depend on which side is ours. Identical changes
on both sides agree. Two different changes to one line, or to overlapping lines, two insertions
that share a non-blank line or sentence (such as a shared provenance lead-in), a merge that would
turn a line into a Setext heading neither side wrote, an entry that
both sides add with different text, an entry that one side deletes and the other changes, and
duplicate or malformed entries are refused: the driver then leaves `git merge-file`'s text merge,
with conflict markers, and exits nonzero, so git reports a conflict. Entry text is never
rewritten, apart from the separators between entries, which become one blank line each.

When any version is already in the line format of `scripts/sources_format.py` (one sentence per
line), all three are first written in that format and so is the result, so a branch written
before the file was converted merges sentence by sentence with one written after it. Without the
format, the merge works on whole lines.

`.gitattributes` names the driver `sourcesmd` for `manual/sources.md`; enable it once per clone
with

    git config merge.sourcesmd.driver 'python3 scripts/resolve_sources_conflict.py --driver %O %A %B'

Where it is not configured (on GitHub, or in another clone), git uses its ordinary text merge.
`scripts/check_restack.py` and `scripts/restack_mechanical.py` run this checkout's driver for the
file whatever the local configuration says.
"""

from __future__ import annotations

import argparse
import collections
import difflib
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from collections.abc import Callable, Sequence
from typing import TypeVar

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import sources_format  # noqa: E402

ANCHOR = re.compile(r'<a id="([^"]+)"></a>')
T = TypeVar("T")
Hunk = tuple[int, int, int, int]  # base[i1:i2] became side[j1:j2]


class Refusal(Exception):
    """The merge cannot decide; a person resolves the conflict."""


def hunks(base: Sequence[T], side: Sequence[T]) -> list[Hunk]:
    matcher = difflib.SequenceMatcher(None, base, side, autojunk=False)
    return [(i1, i2, j1, j2) for tag, i1, i2, j1, j2 in matcher.get_opcodes() if tag != "equal"]


def interact(a: Hunk, b: Hunk) -> bool:
    """Whether hunks of the two sides touch the same base lines or insert at the same place."""
    (s, e), (t, f) = a[:2], b[:2]
    if s < f and t < e:
        return True
    if s == e == t == f:
        return True
    return (s == e and t < s < f) or (t == f and s < t < e)


def merge3(base: Sequence[T], ours: Sequence[T], theirs: Sequence[T], what: str,
           combine: Callable[[list[T], list[T]], list[T]]) -> list[T]:
    """Merge two edits of `base`. Changes to different base items merge; `combine` joins two
    insertions at the same place; any other overlap is refused, naming `what`."""
    texts = (ours, theirs)
    changes = [(side, hunk) for side in (0, 1) for hunk in hunks(base, texts[side])]
    # Group the hunks that interact, directly or through others.
    group = list(range(len(changes)))

    def find(k: int) -> int:
        while group[k] != k:
            k = group[k]
        return k

    for a, (side_a, hunk_a) in enumerate(changes):
        for b, (side_b, hunk_b) in enumerate(changes[:a]):
            if side_a != side_b and interact(hunk_a, hunk_b):
                group[find(a)] = find(b)
    members: dict[int, list[tuple[int, Hunk]]] = {}
    for k, change in enumerate(changes):
        members.setdefault(find(k), []).append(change)
    regions = sorted(((min(h[0] for _, h in group_changes), max(h[1] for _, h in group_changes),
                       group_changes) for group_changes in members.values()),
                     key=lambda region: region[:2])
    merged: list[T] = []
    position = 0
    for start, end, group_changes in regions:
        if start < position:  # cannot happen for hunks that `interact` groups; kept as a guard
            raise Refusal(f"the changes to {what} could not be ordered")
        merged.extend(base[position:start])
        versions, counts = [], []
        for side in (0, 1):
            version, at = [], start
            side_changes = sorted(h for s, h in group_changes if s == side)
            for i1, i2, j1, j2 in side_changes:
                version += list(base[at:i1]) + list(texts[side][j1:j2])
                at = i2
            versions.append(version + list(base[at:end]))
            counts.append(len(side_changes))
        ours_version, theirs_version = versions
        if not counts[1] or ours_version == theirs_version:
            merged.extend(ours_version)
        elif not counts[0]:
            merged.extend(theirs_version)
        elif start == end and counts == [1, 1]:
            merged.extend(combine(ours_version, theirs_version))
        else:
            raise Refusal(f"both sides changed {what} at the same lines")
        position = end
    merged.extend(base[position:])
    return merged


def line_sentences(lines: Sequence[str]) -> list[str]:
    """Non-blank sentences of `lines`, split as `sources_format` splits a paragraph line."""
    return [piece for line in lines if (stripped := line.strip())
            for piece in sources_format.sentences(stripped) if piece]


def combine_lines(ours: list[str], theirs: list[str], what: str = "the entry") -> list[str]:
    """Two disjoint runs of lines inserted at one place, in an order that does not depend on the
    side: a run that starts a new paragraph after one that continues the paragraph, then text
    order. Runs sharing any non-blank line or sentence, or inserting a Setext underline at the
    same point as another insertion, are refused."""
    if any(run and sources_format.SETEXT.match(run[0]) for run in (ours, theirs)):
        raise Refusal(f"merging {what} would turn a line into a Setext heading")
    ours_lines = {line.strip() for line in ours if line.strip()}
    theirs_lines = {line.strip() for line in theirs if line.strip()}
    if (ours_lines & theirs_lines) or (set(line_sentences(ours)) & set(line_sentences(theirs))):
        raise Refusal(f"both sides inserted overlapping lines in {what}")
    first, second = sorted((ours, theirs), key=lambda run: (run[:1] == [""], run))
    return first + second


def merge_lines(base: Sequence[str], ours: Sequence[str], theirs: Sequence[str],
                what: str) -> list[str]:
    """Merge the lines of `what` three ways, refusing duplicate insertions and new Setext
    headings."""
    merged = merge3(base, ours, theirs, what,
                    lambda left, right: combine_lines(left, right, what))
    for kind, extract in (("lines", lambda seq: [s for x in seq if (s := x.strip())]),
                          ("sentences", line_sentences)):
        b_counts = collections.Counter(extract(base))
        o_counts = collections.Counter(extract(ours))
        t_counts = collections.Counter(extract(theirs))
        m_counts = collections.Counter(extract(merged))
        for item, count in m_counts.items():
            if count > max(b_counts[item], o_counts[item], t_counts[item]):
                raise Refusal(f"both sides inserted overlapping {kind} in {what}")

    def setext_blocks(seq: Sequence[str]) -> set[tuple[str, ...]]:
        return {tuple(payload) for kind, payload in sources_format._iter_blocks(list(seq))
                if kind == "opaque" and len(payload) >= 2
                and sources_format.SETEXT.match(payload[-1])}

    if setext_blocks(merged) - (setext_blocks(ours) | setext_blocks(theirs)):
        raise Refusal(f"merging {what} would turn a line into a Setext heading")
    return merged


def combine_keys(ours: list[str], theirs: list[str]) -> list[str]:
    """Two runs of entries added at one place, interleaved in key order."""
    if set(ours) & set(theirs):
        raise Refusal("both sides added entry `"
                      + "`, `".join(sorted(set(ours) & set(theirs))) + "`")
    merged, i, j = [], 0, 0
    while i < len(ours) and j < len(theirs):
        if ours[i] < theirs[j]:
            merged.append(ours[i])
            i += 1
        else:
            merged.append(theirs[j])
            j += 1
    return merged + ours[i:] + theirs[j:]


def parse(text: str, side: str) -> tuple[list[str], list[str], dict[str, list[str]]]:
    """The preamble's lines, the keys in order and each entry's lines (from its anchor to its
    last nonblank line) of one version."""
    if text and not text.endswith("\n"):
        raise Refusal(f"the {side} version does not end with a newline")
    lines = text.split("\n")[:-1]
    starts = [i for i, line in enumerate(lines) if ANCHOR.fullmatch(line)]
    keys = [ANCHOR.fullmatch(lines[i]).group(1) for i in starts]
    if len(set(keys)) != len(keys):
        raise Refusal(f"the {side} version has duplicate entries")
    if any("<a id=" in line and not ANCHOR.fullmatch(line) for line in lines):
        raise Refusal(f"the {side} version has an anchor that is not on a line of its own")

    def trimmed(part: list[str]) -> list[str]:
        while part and not part[-1].strip():
            part = part[:-1]
        return part

    bounds = starts + [len(lines)]
    preamble = trimmed(lines[:bounds[0]])
    entries = {key: trimmed(lines[a:b]) for key, a, b in zip(keys, bounds, bounds[1:])}
    return preamble, keys, entries


def formatted_versions(texts: Sequence[str]) -> list[str] | None:
    """The versions in the line format when any of them already is, else None."""
    formatted = [sources_format.canonical(text) for text in texts]
    return formatted if any(a == b for a, b in zip(formatted, texts)) else None


def merge_sources(base: str, ours: str, theirs: str) -> str:
    """Merge three versions of `manual/sources.md`, or raise `Refusal`."""
    formatted = formatted_versions((base, ours, theirs))
    if formatted:
        base, ours, theirs = formatted
    (b_pre, b_keys, b_entries), (o_pre, o_keys, o_entries), (t_pre, t_keys, t_entries) = (
        parse(text, side) for text, side in ((base, "base"), (ours, "ours"), (theirs, "theirs")))
    preamble = merge_lines(b_pre, o_pre, t_pre, "the text before the first entry")
    keys = merge3(b_keys, o_keys, t_keys, "the order of the entries", combine_keys)
    twice = sorted({key for key in keys if keys.count(key) > 1})
    if twice:
        raise Refusal("both sides added or moved entry `" + "`, `".join(twice)
                      + "` to different places")
    for key in b_keys:
        if key in keys:
            continue
        for side, entries in (("ours", o_entries), ("theirs", t_entries)):
            if key in entries and entries[key] != b_entries[key]:
                raise Refusal(f"one side deleted entry `{key}` and {side} changed it")
    blocks = []
    for key in keys:
        b, o, t = b_entries.get(key), o_entries.get(key), t_entries.get(key)
        if b is None:
            if o is not None and t is not None and o != t:
                raise Refusal(f"both sides added entry `{key}` with different text")
            block = o if o is not None else t
        elif o == t or t == b or t is None:
            block = o
        elif o == b or o is None:
            block = t
        else:
            block = merge_lines(b, o, t, f"entry `{key}`")
        blocks.append("\n".join(block))
    parts = (["\n".join(preamble)] if preamble else []) + blocks
    text = "\n\n".join(parts) + "\n" if parts else ""
    return sources_format.canonical(text) if formatted else text


def driver(base_path: str, ours_path: str, theirs_path: str) -> int:
    """Git merge driver: write the merge to `ours_path`, else leave a text merge as a conflict.

    Any failure of the merge, expected or not, leaves `git merge-file`'s result, so the driver
    never reports a clean merge it did not make. When a version is in the line format, the text
    merge also works on the formatted versions, so its conflicts are single sentences."""
    paths = [base_path, ours_path, theirs_path]
    try:
        texts = [pathlib.Path(p).read_bytes().decode("utf-8") for p in paths]
    except (OSError, UnicodeDecodeError) as err:
        print(f"resolve_sources_conflict: {err}; leaving a text merge as a conflict",
              file=sys.stderr)
        texts = None
    if texts is not None:
        try:
            write(ours_path, merge_sources(*texts).encode("utf-8"))
            return 0
        except Exception as err:  # noqa: BLE001 - every failure leaves a conflict
            print(f"resolve_sources_conflict: {err}; leaving a text merge as a conflict",
                  file=sys.stderr)
    with tempfile.TemporaryDirectory() as tmp:
        try:
            formatted = formatted_versions(texts) if texts is not None else None
            for k, text in enumerate(formatted or ()):
                paths[k] = os.path.join(tmp, f"{k}.md")
                pathlib.Path(paths[k]).write_bytes(text.encode("utf-8"))
        except Exception:  # noqa: BLE001 - fall back to the versions as they are
            paths = [base_path, ours_path, theirs_path]
        merged = subprocess.run(["git", "merge-file", "-p", "-L", "ours", "-L", "base",
                                 "-L", "theirs", paths[1], paths[0], paths[2]],
                                capture_output=True)
        if 0 <= merged.returncode < 128:  # the number of conflicts; 255 is an error
            write(ours_path, merged.stdout)
    return 1


def write(path: str, data: bytes) -> None:
    """Replace the file at `path` with `data` atomically."""
    target = pathlib.Path(path).resolve()
    fd, tmp = tempfile.mkstemp(dir=target.parent, prefix=f".{target.name}.")
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(data)
        os.replace(tmp, target)
    except BaseException:
        pathlib.Path(tmp).unlink(missing_ok=True)
        raise


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--driver", nargs=3, metavar=("BASE", "OURS", "THEIRS"), required=True,
                        help="run as a git merge driver (%%O %%A %%B)")
    args = parser.parse_args(argv)
    return driver(*args.driver)


if __name__ == "__main__":
    raise SystemExit(main())
