#!/usr/bin/env python3
"""Reject new uses of the `TimeM` cost monad (policy/statements.md#running-time-claims; #7636, #6301).

`TimeM` annotations are trusted: nothing ties a tick to the work a program does, so a `TimeM` bound
puts the algorithm's own source in the trusted base. The library is replacing every such bound by
a statement in a machine model. Until that is done, `scripts/timem_baseline.json` records, for each
Lean file under the library and test roots, how often `TimeM` and its tick notation occur in masked
Lean syntax (outside comments and string, raw-string and character literals). This check fails when

* a file that is not in the baseline uses `TimeM`, or
* a file in the baseline uses it more often than recorded.

A lower count, or a file that no longer uses `TimeM` at all, passes without touching the baseline,
so a port does not have to edit a shared file and two ports cannot conflict there. Run with
`--update` now and then to lower the recorded counts; `--update` refuses to raise or add one.

Comments, docstrings and string/character literals are masked with `scripts/proof_lengths.py:masks`
so token separation is preserved and prose may still say what a module does not use.
Sources only: no Lean, no build outputs.

Usage: python3 scripts/check_timem.py [--update] [--report] [--root DIR]
Exit status: 0 when nothing rose, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_lengths import masks  # noqa: E402

BASELINE = Path(__file__).resolve().parent / "timem_baseline.json"
SOURCE_ROOTS = ("CslibFrontier", "CslibFrontierTests", "CslibFrontierResults")
# `TimeM` itself, and the tick notation `✓`, which a file can use after `open` without naming it.
USE = re.compile(r"\bTimeM\b|✓")


def count_uses(text: str) -> int:
    return len(USE.findall(masks(text)[1]))


def scan(root: Path) -> dict[str, int]:
    counts: dict[str, int] = {}
    for top in SOURCE_ROOTS:
        base = root / top
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
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


def compare(baseline: dict[str, int], current: dict[str, int]) -> list[str]:
    """The files whose use of `TimeM` rose, each with a one-line explanation."""
    problems = []
    for path, n in sorted(current.items()):
        allowed = baseline.get(path)
        if allowed is None:
            problems.append(f"{path}: {n} use(s) of TimeM in a file that had none")
        elif n > allowed:
            problems.append(f"{path}: {n} uses of TimeM, up from {allowed}")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--update", action="store_true",
                        help="lower the baseline to the current counts (never raises or adds)")
    parser.add_argument("--report", action="store_true", help="print the remaining totals")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (for tests)")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)

    baseline: dict[str, int] = json.loads(args.baseline.read_text(encoding="utf-8"))["files"]
    current = scan(args.root)
    problems = compare(baseline, current)
    if problems:
        print("check_timem: TimeM use rose. Running times are stated in a machine model "
              "(policy/statements.md#running-time-claims; #7636, #6301); do not add TimeM.",
              file=sys.stderr)
        for line in problems:
            print(f"  {line}", file=sys.stderr)
        return 1
    if args.update:
        lowered = {p: min(n, current[p]) for p, n in baseline.items() if p in current}
        args.baseline.write_text(
            json.dumps({"files": dict(sorted(lowered.items()))}, indent=2, ensure_ascii=False)
            + "\n", encoding="utf-8")
        print(f"check_timem: baseline lowered to {len(lowered)} files, "
              f"{sum(lowered.values())} uses")
        return 0
    if args.report:
        print(f"check_timem: {len(current)} files and {sum(current.values())} uses of TimeM "
              f"remain (baseline {len(baseline)} files, {sum(baseline.values())} uses)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
