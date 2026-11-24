#!/usr/bin/env python3
"""Forbid all uses of the removed `TimeM` cost monad (policy/statements.md#running-time-claims; #7636, #6301).

`TimeM` annotations are trusted: nothing ties a tick to the work a program does, so a `TimeM` bound
puts the algorithm's own source in the trusted base. All frontier bounds have moved to checked
machine models, and frontier `TimeM` support has been removed. This check unconditionally rejects
any occurrence in masked Lean syntax (outside comments and string, raw-string and character
literals) under the maintained Lean source trees (`CslibFrontier`, `CslibFrontierTests`,
`CslibFrontierResults`, `scripts`, `guide`, `tools`, excluding `.lake/` directories) of:

* `TimeM` (including `Cslib.Algorithms.Lean.TimeM` and `CslibFrontier.Algorithms.Lean.TimeM.*`),
* `✓` (tick notation),
* `Cslib.Algorithms.Lean.MergeSort.MergeSort` (upstream `TimeM`-based merge sort),
* `time_simps` and `time_spec`.

`Cslib.Algorithms.Lean.Query.*` remains allowed. Sources only: no Lean, no build outputs.

Usage: python3 scripts/check_timem.py [--report] [--root DIR]
Exit status: 0 when no forbidden uses exist, 1 otherwise.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_lengths import masks  # noqa: E402

SOURCE_ROOTS = (
    "CslibFrontier",
    "CslibFrontierTests",
    "CslibFrontierResults",
    "scripts",
    "guide",
    "tools",
)
# `TimeM` itself, tick notation `✓`, upstream `MergeSort` over `TimeM`, and `TimeM` tactic/simp tags.
USE = re.compile(
    r"\bTimeM\b|✓|\bCslib\.Algorithms\.Lean\.MergeSort\.MergeSort\b|\btime_simps\b|\btime_spec\b"
)


def count_uses(text: str) -> int:
    return len(USE.findall(masks(text)[1]))


def scan(root: Path) -> dict[str, int]:
    counts: dict[str, int] = {}
    for top in SOURCE_ROOTS:
        base = root / top
        if not base.is_dir():
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if d != ".lake")
            for name in sorted(filenames):
                if not name.endswith(".lean"):
                    continue
                path = Path(dirpath) / name
                n = count_uses(path.read_text(encoding="utf-8"))
                if n:
                    counts[path.relative_to(root).as_posix()] = n
    top_level = [root / f"{top}.lean" for top in SOURCE_ROOTS]
    for path in top_level:
        if path.is_file():
            n = count_uses(path.read_text(encoding="utf-8"))
            if n:
                counts[path.relative_to(root).as_posix()] = n
    return counts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", action="store_true", help="print summary when clean")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (for tests)")
    args = parser.parse_args(argv)

    current = scan(args.root)
    if current:
        print(
            "check_timem: forbidden TimeM usage found. Running times must be stated in a "
            "checked machine model (policy/statements.md#running-time-claims; #7636, #6301).",
            file=sys.stderr,
        )
        for path, n in sorted(current.items()):
            print(f"  {path}: {n} forbidden use(s)", file=sys.stderr)
        return 1
    if args.report:
        print("check_timem: 0 forbidden TimeM uses found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
