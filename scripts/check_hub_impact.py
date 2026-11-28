#!/usr/bin/env python3
"""Advisory check reporting high-fan-in library modules modified by a PR.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger

Under Lean 4 and Lake 5's `module` system (`Lake/Build/Module.lean`, `ModuleImportInfo.addImport`),
editing a module `M`'s public `.olean` invalidates downstream modules as follows:
1. Exported imports (`public [meta] import`, or any `import` in a classic file without `module`)
   propagate `transTrace` / `artsTrace` invalidation transitively, while plain private `import`
   rebuilds only one hop because its own exported `.olean` and `transTrace` stay unchanged when its
   public surface and axiom set do not change.
2. `[public] meta import` (without `all`) mixes `metaTransTrace` across the unrestricted import
   closure (`{M} ∪ Reach_any+(M)`), rebuilding `meta import` clients and re-exporting invalidation
   into `transTrace` for `public meta import` clients.
3. Classic files without `module` mix `legacyTransTrace` across `{M} ∪ Reach_any+(M)`, rebuilding
   and re-exporting invalidation to their importers.
4. `[meta] import all` chains propagate from any rebuilt module (`allTransTrace` / `allArtsTrace`).

Under AGENTS.md, new helper lemmas should generally go in a small topic module instead of appending
to a hub module. This script scans `import` headers across `CslibFrontier/` and `CslibFrontierTests/`
(excluding the root aggregator `CslibFrontier.lean`; no Lean invocation needed), computes direct
importer counts and Lake 5 transitive rebuild counts for each modified library module relative to
`--base`, and prints an advisory summary when any reaches `--threshold`. It never fails the job on
findings.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import os
from pathlib import Path
import subprocess
import sys
from typing import NamedTuple

try:
    from scripts.ci.select_guide import (
        AmbiguousHeader,
        HeaderImport,
        parse_header_details_text,
    )
except ModuleNotFoundError:
    _CI_DIR = str(Path(__file__).resolve().parent / "ci")
    if _CI_DIR not in sys.path:
        sys.path.insert(0, _CI_DIR)
    from select_guide import (
        AmbiguousHeader,
        HeaderImport,
        parse_header_details_text,
    )


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_THRESHOLD = 500
HIGH_THRESHOLD = 2000


class ReverseGraph(NamedTuple):
    """Reverse import edges across `CslibFrontier/` and `CslibFrontierTests/`.

    - `any_importers[M]`: modules that directly import `M` with any modifier.
    - `exported_importers[M]`: modules whose `transTrace` mixes `M` (`public [meta] import`, or any
      import in a classic file without `module`).
    - `meta_importers[M]`: modules that import `M` with `[public] meta import` (without `all`),
      mixing `M`'s `metaTransTrace` into their elaboration `trace`.
    - `public_meta_importers[M]`: modules that import `M` with `public meta import` (or `meta` in a
      non-`module` file), mixing `M`'s `metaTransTrace` into their exported `transTrace`.
    - `all_importers[M]`: modules that import `M` with `[meta] import all`, mixing `M`'s
      `allTransTrace` and `allArtsTrace` into their elaboration `trace`.
    - `non_module_files`: scanned modules without a `module` header keyword, which mix
      `legacyTransTrace` across their unrestricted transitive import closure.
    """

    any_importers: dict[str, set[str]]
    exported_importers: dict[str, set[str]]
    meta_importers: dict[str, set[str]]
    public_meta_importers: dict[str, set[str]]
    all_importers: dict[str, set[str]]
    non_module_files: frozenset[str]


def scan_local_imports(path: Path) -> tuple[bool, list[HeaderImport]]:
    """Return `(has_module_kw, local_imports)` from the header of `path`."""
    try:
        has_module, imports = parse_header_details_text(
            path.read_text(encoding="utf-8", errors="replace")
        )
    except AmbiguousHeader:
        return True, []
    return has_module, [
        imp
        for imp in imports
        if imp.module == "CslibFrontier"
        or imp.module.startswith(("CslibFrontier.", "CslibFrontierTests."))
    ]


def build_reverse_graph(root: Path) -> tuple[ReverseGraph, int]:
    """Return `(reverse_graph, total_modules)` over `CslibFrontier/` and `CslibFrontierTests/`."""
    any_imp: dict[str, set[str]] = defaultdict(set)
    exp_imp: dict[str, set[str]] = defaultdict(set)
    meta_imp: dict[str, set[str]] = defaultdict(set)
    pub_meta_imp: dict[str, set[str]] = defaultdict(set)
    all_imp: dict[str, set[str]] = defaultdict(set)
    non_mod: set[str] = set()
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
            has_module, imports = scan_local_imports(path)
            if not has_module:
                non_mod.add(mod)
            for imp in imports:
                dep = imp.module
                if dep == mod:
                    continue
                any_imp[dep].add(mod)
                is_exported = imp.is_public or not has_module
                if is_exported:
                    exp_imp[dep].add(mod)
                if imp.is_meta and not imp.is_all:
                    meta_imp[dep].add(mod)
                if is_exported and imp.is_meta:
                    pub_meta_imp[dep].add(mod)
                if imp.is_all:
                    all_imp[dep].add(mod)
    graph = ReverseGraph(
        any_importers=dict(any_imp),
        exported_importers=dict(exp_imp),
        meta_importers=dict(meta_imp),
        public_meta_importers=dict(pub_meta_imp),
        all_importers=dict(all_imp),
        non_module_files=frozenset(non_mod),
    )
    return graph, total


def rebuilt_importers(graph: ReverseGraph, module: str) -> set[str]:
    """Return downstream modules rebuilt by Lake 5 when `module`'s public `.olean` changes."""
    reach_any: set[str] = {module}
    any_queue: deque[str] = deque([module])
    while any_queue:
        u = any_queue.popleft()
        for v in graph.any_importers.get(u, ()):
            if v not in reach_any:
                reach_any.add(v)
                any_queue.append(v)

    trans_changed: set[str] = {module}
    rebuilt: set[str] = set()
    pub_queue: deque[str] = deque([module])
    all_queue: deque[str] = deque()

    def mark_rebuilt(node: str) -> None:
        if node != module and node not in rebuilt:
            rebuilt.add(node)
            all_queue.append(node)

    def mark_trans_changed(node: str) -> None:
        if node not in trans_changed:
            trans_changed.add(node)
            pub_queue.append(node)
        mark_rebuilt(node)

    for d in reach_any:
        if d != module and d in graph.non_module_files:
            mark_trans_changed(d)
        for v in graph.public_meta_importers.get(d, ()):
            mark_trans_changed(v)
        for v in graph.meta_importers.get(d, ()):
            mark_rebuilt(v)

    while pub_queue or all_queue:
        while pub_queue:
            u = pub_queue.popleft()
            for v in graph.exported_importers.get(u, ()):
                mark_trans_changed(v)
            for x in graph.any_importers.get(u, ()):
                mark_rebuilt(x)
        while all_queue:
            u = all_queue.popleft()
            for w in graph.all_importers.get(u, ()):
                mark_rebuilt(w)
    return rebuilt


def transitive_importers(graph: ReverseGraph, module: str) -> int:
    """Count downstream modules rebuilt by Lake 5 when `module`'s public `.olean` changes."""
    return len(rebuilt_importers(graph, module))


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
    """Return `([(rel_path, direct, transitive), ...], total_modules)` meeting `threshold`."""
    modified = modified_library_modules(root, base)
    if not modified:
        return [], 0
    graph, total = build_reverse_graph(root)
    hits: list[tuple[str, int, int]] = []
    for rel in modified:
        mod = ".".join(Path(rel).with_suffix("").parts)
        direct = len(graph.any_importers.get(mod, ()))
        if direct == 0:
            continue
        trans = transitive_importers(graph, mod)
        if trans >= threshold:
            hits.append((rel, direct, trans))
    hits.sort(key=lambda row: (-row[2], -row[1], row[0]))
    return hits, total


def format_markdown(hits: list[tuple[str, int, int]], total: int, threshold: int) -> str:
    lines = [
        "### High-fan-in module impact (advisory)",
        "",
        f"This change modifies {len(hits)} module(s) with at least **{threshold}** transitive "
        f"importers rebuilt by Lake 5 on a public `.olean` change (out of {total:,} "
        "`CslibFrontier` / `CslibFrontierTests` modules, respecting `module` private-import "
        "cutoff, `[public] meta import`, `import all`, and non-`module` traces). Any public "
        "interface edit forces Lake to rebuild those dependents across concurrent PRs, merge "
        "groups, and contributor worktrees.",
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
