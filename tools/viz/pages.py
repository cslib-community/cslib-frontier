# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Write the interactive pages: each embeds its data, so it works from Pages and from a file."""

from __future__ import annotations

import html
import json
import shutil
from pathlib import Path

import history as h
import site_data as sd
import style

HERE = Path(__file__).resolve().parent
ASSETS = HERE / "site"

_SHELL = """<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<meta name="description" content="{description}">
<link rel="stylesheet" href="viz.css">
</head><body>
<main>
{body}
</main>
<script id="data" type="application/json">{data}</script>
<script src="viz.js"></script>
<script src="{script}"></script>
</body></html>
"""

_BODIES = {
    "index": ("Briefing", "What changed in cslib-frontier, and how it is growing.", """
<h1>cslib-frontier, at a glance</h1>
<p class="sub">How the library is growing and what changed lately, rebuilt nightly from <code>main</code>
together with the API documentation. Every number links onward: explore
<a href="modules.html">modules</a>, <a href="results.html">registered results</a>,
<a href="textbooks.html">textbook coverage</a> and <a href="areas.html">areas</a>.</p>
<div class="tiles" id="tiles"></div>
<h2>What changed</h2>
<div class="controls"><div class="seg" id="window" role="group" aria-label="Time window">
<button type="button" data-days="1" aria-pressed="true">Last 24 hours</button>
<button type="button" data-days="7" aria-pressed="false">Last 7 days</button></div></div>
<p class="lede" id="lede"></p>
<div class="digest" id="digest"></div>
<h2>Growth by area</h2>
<p class="sub">Library lines of code (not comments or blank) at the end of each UTC day. Hover for
values; click an area in the legend to hide or show it.</p>
<div class="card"><div id="growth"></div>
<p style="margin:10px 0 0"><button class="chip" id="growth-toggle" type="button">Show as table</button></p>
<div id="growth-table" hidden style="max-height:420px;overflow:auto;margin-top:10px"></div></div>
<h2 id="charts">Charts</h2>
<p class="sub">Each answers one question. Every chart has a dark version, and a CSV of the data
behind it.</p>
<div id="gallery"></div>
"""),
    "modules": ("Modules", "Every module of cslib-frontier: size, dependencies, history and use.", """
<h1>Modules</h1>
<p class="sub">Every library module, with how much rebuilds when it changes, how deep it sits, how
often it changes, and what nothing uses. Search by any part of the name.</p>
<div class="controls"><input type="search" id="q" placeholder="Search modules, e.g. cook levin, wordram dictionary" aria-label="Search modules" autofocus>
<select id="sort" aria-label="Sort by"></select></div>
<div class="controls"><div class="chips" id="areas"></div></div>
<p class="small" id="count"></p>
<div class="explorer"><div class="card list" id="list"></div><div class="card detail" id="detail"></div></div>
"""),
    "results": ("Results", "Every registered result of cslib-frontier and what it rests on.", """
<h1>Registered results</h1>
<p class="sub">Every entry of the results registry (<code>CslibFrontierResults</code>): its sources,
its theorems, the library it rests on and the textbook audit rows that cite it.</p>
<div class="controls"><input type="search" id="q" placeholder="Search titles, theorems, sources" aria-label="Search results" autofocus>
<select id="topic" aria-label="Topic"></select><select id="sort" aria-label="Sort by"></select></div>
<p class="small" id="count"></p>
<div class="explorer"><div class="card list" id="list"></div><div class="card detail" id="detail"></div></div>
"""),
    "textbooks": ("Textbooks", "How much of Arora–Barak and Goldreich cslib-frontier covers.", """
<h1>Textbook coverage</h1>
<p class="sub">The source-pinned audits under <code>results/</code> record a disposition for each
numbered result of the 2007 drafts. Click a bar or chapter number to list its results; each links
to its audit row and to the registered results that formalize it. The audits do not claim
book-wide coverage.</p>
<div id="books"></div>
"""),
    "areas": ("Areas", "Each area of cslib-frontier at a glance.", """
<h1>Areas</h1>
<p class="sub">One card per top-level area of <code>CslibFrontier/</code>; areas past the seventh
largest share "Other".</p>
<div class="areas" id="areas"></div>
"""),
}


_BODIES["prs"] = ("Pull requests", "Every pull request of cslib-frontier: when, where, how big and how long it waited.", """
<h1>Pull requests</h1>
<p class="sub">Every pull request, from GitHub, joined to its squash commit on <code>main</code> for
the areas it changed. Merged ones sit where they merged, in the lane of the library area with the
largest net code-line change; open and closed ones where they were opened. Hover for details; click
to open it on GitHub.</p>
<div class="tiles" id="tiles"></div>
<div class="controls" style="margin-top:16px"><input type="search" id="q" placeholder="Search titles, e.g. Cook-Levin, WordRAM, perf" aria-label="Search pull requests">
<span class="chips" id="kinds"></span><select id="author" aria-label="Author"></select><span class="small" id="stats"></span></div>
<div class="card" style="padding:8px"><canvas id="galaxy" aria-label="Pull requests over time by area"></canvas></div>
<div id="charts"></div>
<p class="small" style="margin-top:16px" id="data-note"></p>
""")


def _json(obj) -> str:
    # Safe inside <script>: escaping "<" prevents both "</script>" and HTML5 "<!-- <script>" breakouts.
    return json.dumps(obj, separators=(",", ":")).replace("<", "\\u003c")


def build(out: Path, H: h.History, census, charts: list[dict], sections: list[str],
          repo_url: str, pr_recs: list[dict] | None = None) -> list[Path]:
    """Write every page and its assets into `out`."""
    out.mkdir(parents=True, exist_ok=True)
    for f in ASSETS.iterdir():
        if f.suffix in (".css", ".js"):
            shutil.copy(f, out / f.name)
    head = H.commits[-1]
    report = census[0] if census else None
    meta = {"sha": head.sha, "time": head.time, "repoUrl": repo_url, "apiRoot": "../",
            "libRoot": "CslibFrontier", "areas": style.ALL_AREAS, "lean": bool(report),
            "prs": pr_recs is not None}
    daily = sd.daily(H)
    audit_rows = __import__("audits").load(H.repo)
    audit_daily = sd.audit_daily(H, daily["dates"])
    modules = sd.modules(H, census)
    results = sd.results(H, census, audit_rows)
    books = [{"key": k, "title": t, "path": p} for k, p, t in __import__("audits").BOOKS]
    titles = {r["id"]: r["title"] for r in results["results"]}
    changes = {"1": sd.changes(H, 1), "7": sd.changes(H, 7)}
    headline = {"theorems": None, "definitions": None, "unused_imports": None, "imports": None}
    if report:
        import lean_census as lc
        import plots_lean
        groups = {}
        for v in lc.summarize(report)["by_area"].values():
            for g, n in v.items():
                groups[g] = groups.get(g, 0) + n
        headline["theorems"] = groups.get("Theorems", 0)
        headline["definitions"] = groups.get("Definitions", 0)
        headline["imports"] = plots_lean.checked_imports(report)
        headline["unused_imports"] = sum(len(v) for v in plots_lean.unused_imports(report).values())
    payloads = {
        "index": {"daily": daily, "rolling": sd.rolling(H),
                  "audit_daily": {k: v for k, v in audit_daily.items() if "@" not in k},
                  "audit_at": {k: v for k, v in audit_daily.items() if "@" in k},
                  "audit_totals": {k: len(v) for k, v in audit_rows.items()},
                  "headline": headline, "changes": changes,
                  "census_changes": sd.census_changes(census[1], titles) if census else None,
                  "charts": charts, "sections": sections, "lean": bool(report)},
        "modules": {"modules": modules, "results": [[r["id"], r["title"]] for r in results["results"]]},
        "results": {"results": results, "books": books},
        "textbooks": {"textbooks": sd.textbooks(H, audit_rows, results, audit_daily),
                      "results": {"results": [{"id": r["id"], "title": r["title"]}
                                              for r in results["results"]]},
                      "daily": {"dates": daily["dates"]}},
        "areas": {"modules": modules, "daily": daily, "results": results, "changes": changes},
        "prs": {"prs": _pr_payload(pr_recs), "kinds": __import__("prs").KINDS,
                "charts": [c for c in charts if c["section"] == "Pull requests"]},
    }
    written = []
    for page, (title, description, body) in _BODIES.items():
        if page == "prs" and pr_recs is None:
            continue
        payload = {"meta": meta, **payloads[page]}
        p = out / f"{page}.html"
        p.write_text(_SHELL.format(
            title=html.escape(f"{title} · cslib-frontier views" if page != "index"
                              else "cslib-frontier views"),
            description=html.escape(description), body=body.strip(), data=_json(payload),
            script=f"{page}.js"))
        written.append(p)
    return written


def _pr_payload(recs):
    """Columns for the galaxy: number, title, kind, state, opened, merged, author, added, deleted,
    files, reviews, commits, area, sub-area."""
    if recs is None:
        return None
    keys = ["n", "title", "kind", "state", "created", "merged", "author", "add", "del", "files",
            "reviews", "commits", "area", "sub"]
    return {"fields": keys, "rows": [[r[k] for k in keys] for r in recs if r["created"]]}
