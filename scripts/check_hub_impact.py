#!/usr/bin/env python3
"""Advisory check reporting high-fan-in library modules modified by a PR.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

Editing a low-level module's public interface invalidates every module that transitively
imports it, causing thousands of modules to rebuild across CI, merge groups, and contributor
worktrees. Under AGENTS.md, new helper lemmas should generally go in a small topic module
instead of appending to a hub module.

This script scans `import` headers across `CslibFrontier/` and `CslibFrontierTests/` (no Lean
invocation needed), computes direct and transitive reverse-importer counts for each modified
library module relative to `--base`, and prints an advisory summary when any exceeds
`--threshold`. It never fails the job on findings.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import os
from pathlib import Path
import subprocess
import sys

try:
    from scripts.ci.select_guide import AmbiguousHeader, parse_header_imports_text
except ModuleNotFoundError:
    _CI_DIR = str(Path(__file__).resolve().parent / "ci")
    if _CI_DIR not in sys.path:
        sys.path.insert(0, _CI_DIR)
    from select_guide import AmbiguousHeader, parse_header_imports_text


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_THRESHOLD = 500
HIGH_THRESHOLD = 2000


def scan_local_imports(path: Path) -> set[str]:
    """Collect `CslibFrontier.*` module imports from the header of `path`."""
    try:
        mods = parse_header_imports_text(path.read_text(encoding="utf-8", errors="replace"))
    except AmbiguousHeader:
        return set()
    return {m for m in mods if m == "CslibFrontier" or m.startswith("CslibFrontier.")}


def build_reverse_graph(root: Path) -> tuple[dict[str, set[str]], int]:
    """Return `(reverse_importers, total_modules)` over `CslibFrontier/` and `CslibFrontierTests/`."""
    rev: dict[str, set[str]] = defaultdict(set)
    total = 0
    for dirname in ("CslibFrontier", "CslibFrontierTests"):
        base_dir = root / dirname
        if not base_dir.is_dir():
            continue
        for path in base_dir.rglob("*.lean"):
            if path.is_symlink():
                continue
            mod = ".".join(path.relative_to(root).with_suffix("").parts)
            total += 1
            for dep in scan_local_imports(path):
                rev[dep].add(mod)
    return rev, total


def transitive_importers(rev: dict[str, set[str]], module: str) -> int:
    seen: set[str] = {module}
    queue: deque[str] = deque([module])
    while queue:
        u = queue.popleft()
        for v in rev.get(u, ()):
            if v not in seen:
                seen.add(v)
                queue.append(v)
    return len(seen) - 1


def modified_library_modules(root: Path, base: str) -> list[str]:
    """Return paths of existing `CslibFrontier/**/*.lean` files modified (not added) vs `base`."""
    resolved = subprocess.run(
        ["git", "merge-base", base, "HEAD"],
        cwd=root, text=True, capture_output=True, check=False,
    )
    cmp_base = resolved.stdout.strip() if resolved.returncode == 0 and resolved.stdout.strip() else base
    diff = subprocess.run(
        ["git", "diff", "--no-renames", "--diff-filter=M", "--name-only", "-z", cmp_base, "--",
         "CslibFrontier/"],
        cwd=root, text=True, capture_output=True, check=True,
    )
    paths = [p for p in diff.stdout.split("\0") if p.endswith(".lean") and (root / p).is_file()]
    return sorted(paths)


def analyze(root: Path, base: str, threshold: int = DEFAULT_THRESHOLD
            ) -> tuple[list[tuple[str, int, int]], int]:
    """Return `([(rel_path, direct, transitive), ...], total_modules)` exceeding `threshold`."""
    modified = modified_library_modules(root, base)
    if not modified:
        return [], 0
    rev, total = build_reverse_graph(root)
    hits: list[tuple[str, int, int]] = []
    for rel in modified:
        mod = ".".join(Path(rel).with_suffix("").parts)
        direct = len(rev.get(mod, ()))
        if direct == 0:
            continue
        trans = transitive_importers(rev, mod)
        if trans >= threshold:
            hits.append((rel, direct, trans))
    hits.sort(key=lambda row: (-row[2], -row[1], row[0]))
    return hits, total


def format_markdown(hits: list[tuple[str, int, int]], total: int, threshold: int) -> str:
    lines = [
        "### High-fan-in module impact (advisory)",
        "",
        f"This change modifies {len(hits)} module(s) with at least **{threshold}** transitive "
        f"importers (out of {total:,} `CslibFrontier` / `CslibFrontierTests` modules). "
        "Any public interface edit forces Lake to rebuild those dependents across concurrent PRs, "
        "merge groups, and contributor worktrees.",
        "",
        "| Module | Direct importers | Transitive importers | Share |",
        "| --- | ---: | ---: | ---: |",
    ]
    for rel, direct, trans in hits:
        share = f"{(100.0 * trans / total):.1f}%" if total else "0.0%"
        lines.append(f"| `{rel}` | {direct:,} | {trans:,} | {share} |")
    lines += [
        "",
        "If this only adds standalone helper lemmas, consider placing them in a smaller topic "
        "module instead of appending to a hub (see `AGENTS.md`, *Placement and reuse*). "
        "Necessary hub edits should stay sequenced in the merge queue.",
    ]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main",
                        help="comparison revision (default: origin/main)")
    parser.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD,
                        help=f"minimum transitive importer count to report (default: {DEFAULT_THRESHOLD})")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root")
    parser.add_argument("--github", action="store_true",
                        help="emit GitHub Actions notice annotations and step summary")
    args = parser.parse_args(argv)
    try:
        hits, total = analyze(args.root, args.base, threshold=args.threshold)
    except (subprocess.SubprocessError, OSError) as error:
        print(f"Hub-impact check skipped: {error}")
        return 0
    if not hits:
        print(f"No modified library modules exceed {args.threshold} transitive importers.")
        return 0
    for rel, direct, trans in hits:
        share = f"{(100.0 * trans / total):.1f}%" if total else "0.0%"
        msg = (f"{rel} has {trans:,} transitive importers ({share} of {total:,} modules; "
               f"{direct:,} direct). Consider placing new helper lemmas in a small topic module "
               "instead of appending to a hub.")
        print(f"hub-impact: {msg}")
        if args.github:
            severity = "warning" if trans >= HIGH_THRESHOLD else "notice"
            print(f"::{severity} file={rel},title=High-fan-in module edited::{msg}")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if args.github and summary:
        with Path(summary).open("a", encoding="utf-8") as handle:
            handle.write("\n" + format_markdown(hits, total, args.threshold))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
