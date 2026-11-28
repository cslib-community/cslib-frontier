#!/usr/bin/env python3
# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Build the codebase visualization portfolio.

Usage:
  python3 tools/viz/build.py [--out DIR] [--only NAME ...] [--no-video] [--ref REF]

Writes every chart (PNG and SVG, a dark PNG and a CSV of its data), the two videos, and the
interactive pages (briefing, explorers, textbook map, agent activity) into `--out`
(default `tools/viz/_site`). See tools/viz/README.md.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import json
import sys
import time
from pathlib import Path
from typing import Callable

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import history as h  # noqa: E402
import plots_growth  # noqa: E402
import plots_structure  # noqa: E402
import evolution  # noqa: E402
import lean_census  # noqa: E402
import plots_lean  # noqa: E402
import plots_results  # noqa: E402
import pages  # noqa: E402
import atlas  # noqa: E402
import streams  # noqa: E402
import prs  # noqa: E402
import github_prs  # noqa: E402
import agent_activity  # noqa: E402
import style  # noqa: E402


@dataclasses.dataclass(frozen=True)
class Chart:
    name: str
    section: str
    title: str
    question: str
    reading: str
    render: Callable
    lean: bool = False  # needs the census of a build (`--lean-lib`)
    prs: bool = False  # needs pull request metadata (`--fetch-prs` or `--prs-json`)
    themed: bool = True  # rendered in light and dark; the video and poster are dark only
    wide: bool = False  # spans the gallery


CHARTS = [
    Chart("atlas", "Growth", "An atlas of the library, growing",
          "How did the library take shape, and how did its parts come to depend on each other?",
          "A map in which areas are countries and sub-areas are provinces: every point belongs to "
          "the sub-area of the nearest module. Modules keep their places for the whole video and "
          "glow when a commit changes them; when a commit adds imports between two provinces, "
          "comets fly from the importing one to the one it imports. Commits touching more than 150 "
          "library files, such as the module-root rename, are left dark.", atlas.video,
          themed=False, wide=True),
    Chart("evolution", "Growth", "The import graph, growing",
          "How did the library take shape, day by day?",
          "Each dot is a module, coloured by area and sized by its code. Lines are imports. Modules "
          "glow when a commit changes them; commits touching more than 150 library files, such as "
          "the module-root rename, are left dark. Every module keeps one position for the whole "
          "video, so new work appears where it belongs and the camera pulls back as the graph "
          "grows.", evolution.video, themed=False, wide=True),
    Chart("lifetime-streams", "Growth", "The library's lifetime, sub-area by sub-area",
          "Which parts of the library grew when?",
          "Lines of code in each sub-area every six hours, as a river centred on zero; streams "
          "keep their area's colour in different shades. Small sub-areas are folded into their "
          "area's \"other\".", streams.streamgraph, wide=True),
    Chart("growth-by-area", "Growth", "Code by area", "Which areas drove the growth?",
          "Stacked lines of code, excluding comments and blank lines, in each top-level area of "
          "CslibFrontier/ at the end of every UTC day. Areas past the seventh largest share the "
          "grey band.", plots_growth.growth_by_area),
    Chart("declarations", "Growth", "Declarations", "How many results are there, and how big?",
          "Top-level declaration headers counted from source text: theorems and lemmas, "
          "definitions and abbreviations, and types and instances. The lower panel divides code "
          "lines by theorems, a rough measure of how much each result costs.",
          plots_growth.declarations),
    Chart("lean-declarations", "Growth", "Declarations, as Lean sees them",
          "What does the library declare, exactly?",
          "Counted from the built library, so declarations that commands and macros generate are "
          "included and prose that looks like a header is not. Each nightly build adds a point to "
          "the series, which is exact from its first night onward; the chart above estimates the "
          "earlier history from source text.", plots_lean.declarations, lean=True),
    Chart("textbook-coverage", "Growth", "Textbook coverage",
          "How much of Arora–Barak and Goldreich does the library cover?",
          "Each numbered result of the 2007 drafts that the audits under results/ have checked, by "
          "the audit's disposition: covered, covered after correcting a source defect, partial, a "
          "source issue, or no endpoint located. Below, the same counts at every revision of the "
          "audit.", plots_results.coverage),
    Chart("churn", "Growth", "Daily churn", "Was a given day growth or rework?",
          "Lines added above the axis and removed below, per UTC day, for library files. A tall "
          "orange bar is a cleanup or a rewrite; a day with both tall is a migration.",
          plots_growth.churn),
    Chart("treemap", "Structure", "Where the code lives",
          "Where is the code, and which parts change most?",
          "Every module is a rectangle sized by lines of code, nested in its folder and area. "
          "Darker modules have been changed by more commits on main.", plots_structure.treemap),
    Chart("hotspots", "Structure", "Hotspots", "Which large modules keep changing?",
          "Size against change count, both on log scales. Modules up and to the right are big and "
          "edited often: the usual first candidates for splitting or stabilising.",
          plots_structure.hotspots),
    Chart("import-graph", "Dependencies", "The import graph today",
          "What does the whole module graph look like?",
          "The final frame of the video at 4K: every library module, laid out by its imports and "
          "its place in the folder tree.", evolution.poster, themed=False, wide=True),
    Chart("import-matrix", "Dependencies", "Who imports whom",
          "Which areas build on which?",
          "Import statements from the row sub-area into the column sub-area, for the largest "
          "sub-areas. Rows show what an area depends on; columns show who depends on it.",
          plots_structure.import_matrix),
    Chart("change-coupling", "Dependencies", "Change coupling", "What has to change together?",
          "How often two sub-areas change in the same commit (Jaccard index). Compare with the "
          "import matrix: bright coupling without imports is a hidden dependency.",
          plots_structure.change_coupling),
    Chart("hubs", "Dependencies", "Hub modules", "What does an edit force to rebuild?",
          "The share of the library that imports each module directly or transitively. Changing "
          "a module's exported API rebuilds all of it.", plots_structure.hubs),
    Chart("result-cones", "Dependencies", "What the headline results rest on",
          "How much of the library does each registered result depend on?",
          "For each result in the registry, the library declarations its theorems use, directly "
          "or transitively, coloured by area. A large cone is a deep result, or one routed "
          "through heavy machinery; the census also checks that no cone contains sorryAx.",
          plots_lean.result_cones, lean=True),
    Chart("load-bearing", "Dependencies", "Load-bearing declarations",
          "Which declarations does the rest of the library lean on most?",
          "Declarations ranked by how many other written declarations mention them. Changing the "
          "statement of one of these is expensive; they deserve the best names and docstrings.",
          plots_lean.load_bearing, lean=True),
    Chart("unused-definitions", "Dependencies", "Definitions nothing uses",
          "Which definitions has nothing in the library used?",
          "Definitions, abbreviations and types that no other library declaration mentions: "
          "candidates for the review question of what should not exist, or for a missing first "
          "property. The CSV lists every one.", plots_lean.unused_definitions, lean=True),
    Chart("import-depth", "Dependencies", "Import depth", "What bounds a parallel build?",
          "The longest import chain over time, and how deep each module sits today. However many "
          "cores a build has, it cannot finish faster than this chain elaborates one module after "
          "another.", plots_growth.import_depth),
    Chart("pr-growth-vs-cleanup", "Pull requests", "Growth and cleanup",
          "Does the project pause to consolidate?",
          "Lines changed by merged pull requests every six hours: new results (feat) above the "
          "axis, refactoring and performance below, and the share of that work that was cleanup.",
          prs.growth_vs_cleanup, prs=True, wide=True),
    Chart("pr-waterfall", "Pull requests", "Every pull request, from opened to merged",
          "How long does work wait, and how much is in flight?",
          "Each pull request is a line from opening to merge, close or now, in order of opening, "
          "coloured by kind. Below, how many were open at each moment and how many merged each "
          "hour.", prs.waterfall, prs=True, wide=True),
    Chart("atlas-poster", "Dependencies", "The atlas today",
          "What does the library look like as a map?",
          "The final frame of the atlas at 4K: countries are areas, provinces sub-areas, each "
          "laid out by its own imports.", atlas.poster, themed=False, wide=True),
    Chart("cadence", "Activity", "When work lands", "When do commits reach main?",
          "Commits that change Lean files, by UTC day and hour, with the daily total below.",
          plots_structure.cadence),
]
BY_NAME = {c.name: c for c in CHARTS}
SECTIONS = ["Growth", "Structure", "Dependencies", "Pull requests", "Activity"]


def _files(name: str, paths: list[Path]) -> dict[str, str]:
    out = {}
    for p in paths:
        kind = "dark" if p.stem.endswith("-dark") else p.suffix[1:]
        out[kind] = p.name
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--out", type=Path, default=HERE / "_site")
    ap.add_argument("--repo", type=Path, default=HERE)
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--only", nargs="*", choices=sorted(BY_NAME), default=None)
    ap.add_argument("--no-video", action="store_true", help="skip the two videos")
    ap.add_argument("--fetch-prs", action="store_true",
                    help="fetch pull request metadata from GitHub (GITHUB_TOKEN or GH_TOKEN)")
    ap.add_argument("--prs-json", type=Path, default=None,
                    help="reuse pull request metadata saved by an earlier run (prs.json)")
    ap.add_argument("--prs-previous", default=None,
                    help="with --fetch-prs: URL or file of the previously published prs.json; "
                         "only pull requests updated since are fetched")
    activity = ap.add_mutually_exclusive_group()
    activity.add_argument("--fetch-agent-activity", action="store_true",
                          help="read public agent disclosures (requires --fetch-prs and its token)")
    activity.add_argument("--agent-activity-json", type=Path,
                          help="reuse an aggregated report from an earlier build")
    ap.add_argument("--lean-lib", type=Path, default=None,
                    help="build outputs (.lake/build/lib/lean) of the commit being visualized; "
                         "enables the Lean census views")
    ap.add_argument("--lean-census", type=Path, default=None,
                    help="reuse a lean-census.json written by an earlier run (for page work)")
    ap.add_argument("--lean-history", default=None,
                    help="URL or file of the previously published lean-history.json to extend")
    ap.add_argument("--require-registry", action="store_true",
                    help="fail if the results registry cannot be exported (implied by --lean-history)")
    ap.add_argument("--repo-url", default="https://github.com/cslib-community/cslib-frontier",
                    help="links the commit in the report; empty to omit")
    args = ap.parse_args()

    if args.fetch_agent_activity and (not args.fetch_prs or args.prs_json or not github_prs.token()):
        ap.error("--fetch-agent-activity needs --fetch-prs with a GitHub token")

    t0 = time.time()
    H = h.History(args.repo, args.ref)
    print(f"history: {len(H.commits)} commits, {len(H.blobs.data)} blobs "
          f"({time.time() - t0:.1f}s)", flush=True)
    if args.require_registry:
        lean_census.registered_results(H.repo, require=True)
    census = None
    if args.lean_census:
        report = json.loads(args.lean_census.read_text())
        series = args.lean_census.with_name("lean-history.json")
        entries = json.loads(series.read_text())["entries"] if series.exists() else []
        census = (report, entries)
        print(f"lean census: reused {args.lean_census}", flush=True)
    elif args.lean_lib:
        t = time.time()
        census = lean_census.collect(H, args.lean_lib.resolve(), args.lean_history, args.out,
                                     require_registry=args.require_registry)
        print(f"lean census: {len(census[0]['modules'])} modules, series of {len(census[1])} "
              f"({time.time() - t:.1f}s)", flush=True)
    raw_prs = None
    if args.prs_json:
        raw_prs = json.loads(args.prs_json.read_text())
    elif args.fetch_prs:
        if github_prs.token():
            t = time.time()
            prev = github_prs.load_previous(args.prs_previous) if args.prs_previous else []
            raw_prs = github_prs.update(prev) if prev else github_prs.fetch()
            how = f"updated from {len(prev)} published" if prev else "fetched"
            print(f"pull requests: {len(raw_prs)} {how} ({time.time() - t:.1f}s)", flush=True)
        else:
            print("warning: no GITHUB_TOKEN or GH_TOKEN; pull request views are skipped",
                  file=sys.stderr, flush=True)
    pr_recs = None
    if raw_prs is not None:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "prs.json").write_text(json.dumps(raw_prs, separators=(",", ":")))
        pr_recs = prs.records(H, raw_prs)
    agents = None
    if args.agent_activity_json:
        agents = json.loads(args.agent_activity_json.read_text())
        if agents.get("metric") != "worker_ids":
            ap.error("--agent-activity-json needs a worker-ID report from the current generator")
    elif args.fetch_agent_activity:
        t = time.time()
        now = dt.datetime.now(dt.timezone.utc)
        events = agent_activity.fetch(github_prs.DEFAULT_REPO, github_prs.token(),
                                      raw_prs, now)
        agents = agent_activity.summarize(events, now)
        print(f"agent activity: {len(events)} records ({time.time() - t:.1f}s)", flush=True)
    if agents is not None:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "agent-activity.json").write_text(json.dumps(agents, separators=(",", ":")))

    videos = {"atlas", "evolution"}
    names = args.only or [c.name for c in CHARTS if not (args.no_video and c.name in videos)]
    built: dict[str, list[Path]] = {}
    for c in CHARTS:
        if c.name not in names:
            continue
        if c.lean and census is None:
            print(f"{c.name}: skipped (needs --lean-lib)", flush=True)
            continue
        if c.prs and pr_recs is None:
            print(f"{c.name}: skipped (needs --fetch-prs or --prs-json)", flush=True)
            continue
        t = time.time()
        paths: list[Path] = []
        for theme in ((style.LIGHT, style.DARK) if c.themed else (style.LIGHT,)):
            style.setup(theme)
            got = (c.render(H, args.out, census) if c.lean else
                   c.render(H, args.out, pr_recs) if c.prs else c.render(H, args.out))
            paths += [p for p in got if p not in paths]
        style.setup(style.LIGHT)
        built[c.name] = paths
        print(f"{c.name}: {', '.join(p.name for p in paths)} ({time.time() - t:.1f}s)", flush=True)
    # A partial rebuild (`--only`) keeps the views already in the output directory.
    for c in CHARTS:
        if c.name not in built and not (c.lean and census is None) and not (c.prs and pr_recs is None):
            kept = [args.out / f for f in (f"{c.name}.mp4", f"{c.name}.png", f"{c.name}-dark.png",
                                          f"{c.name}.svg", f"{c.name}.csv")
                    if (args.out / f).exists()]
            if kept:
                built[c.name] = kept
    charts = [{"name": c.name, "section": c.section, "title": c.title, "question": c.question,
               "reading": c.reading, "files": _files(c.name, built[c.name]), "wide": c.wide}
              for c in CHARTS if c.name in built]
    t = time.time()
    written = pages.build(args.out, H, census, charts, SECTIONS, args.repo_url, pr_recs, agents)
    print(f"pages: {', '.join(p.name for p in written)} ({time.time() - t:.1f}s)", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
