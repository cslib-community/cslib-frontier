# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""The data behind the interactive pages: the briefing, the explorers and the textbook map.

Everything here is computed from the replayed history (`history.py`), the textbook audits
(`audits.py`), the results registry and, when a build is available, the Lean census. Pages embed
their payload, so they work from a static host and from a local file alike.
"""

from __future__ import annotations

import datetime as dt
import subprocess
from collections import Counter, defaultdict

import audits
import history as h
import lean_census as lc

DAY = 86400


def _area(module: str) -> str:
    return h.area_of(module.replace(".", "/") + ".lean")


def _theorems(info: h.BlobInfo) -> int:
    return info.decls.get("theorem", 0) + info.decls.get("lemma", 0)


def _definitions(info: h.BlobInfo) -> int:
    return info.decls.get("def", 0) + info.decls.get("abbrev", 0)


# --------------------------------------------------------------------------------------------
# Daily series (source text; every past day)


def measures(H: h.History, tree: dict[str, str]) -> dict:
    """The headline measures of one snapshot of the tree."""
    lib = {p: H.blobs[b] for p, b in tree.items() if h.is_library(p)}
    area_code = Counter()
    for p, i in lib.items():
        area_code[h.area_of(p)] += i.code
    graph = h.import_graph(H.blobs, tree)
    return {
        "lean_lines": sum(H.blobs[b].lines for b in tree.values()),
        "lib_lines": sum(i.lines for i in lib.values()),
        "lib_code": sum(i.code for i in lib.values()),
        "modules": len(lib),
        "theorems": sum(_theorems(i) for i in lib.values()),
        "definitions": sum(_definitions(i) for i in lib.values()),
        "chain": h.longest_chain(graph)[0],
        "imports": sum(len(v) for v in graph.values()),
        "area_code": [area_code[a] for a in h.AREAS + [h.OTHER]],
    }


def rolling(H: h.History) -> dict:
    """The measures now, 24 hours ago and 7 days ago, so changes match the digest's windows."""
    end = H.commits[-1].time
    marks = {"1": end - DAY, "7": end - 7 * DAY}
    out: dict[str, dict] = {}
    tree: dict[str, str] = {}
    for c in H.commits:
        for key, t in marks.items():
            if key not in out and c.time > t:
                out[key] = measures(H, tree)
        for p, b in c.changes:
            if b is None:
                tree.pop(p, None)
            else:
                tree[p] = b
    out["0"] = measures(H, tree)
    for key in marks:
        out.setdefault(key, out["0"])
    out["commits"] = {k: sum(1 for c in H.commits if c.time > t) for k, t in marks.items()}
    return out


def daily(H: h.History) -> dict:
    """Headline measures at the end of every UTC day, from the replayed history."""
    dates, rows = [], []
    for d, _, tree in H.daily():
        rows.append(measures(H, tree))
        dates.append(d.isoformat())
    commits = Counter(c.date.isoformat() for c in H.commits)
    for d, r in zip(dates, rows):
        r["commits"] = commits[d]
    return {"dates": dates, "rows": rows}


def audit_daily(H: h.History, dates: list[str]) -> dict[str, list[int]]:
    """Covered audit rows per book at the end of each date (carried forward), and under the
    key `"<book>@<window>"` the count 24 hours and 7 days before the head commit."""
    out = {}
    end = H.commits[-1].time
    for key, path, _ in audits.BOOKS:
        log = subprocess.run(["git", "-C", str(H.repo), "log", "--first-parent", "--reverse",
                              "--format=%H %ct", "--", path], capture_output=True, text=True,
                             check=True).stdout.split()
        by_day: dict[str, int] = {}
        at = {"1": 0, "7": 0}
        for sha, ct in zip(log[::2], log[1::2]):
            text = subprocess.run(["git", "-C", str(H.repo), "show", f"{sha}:{path}"],
                                  capture_output=True, text=True).stdout
            day = dt.datetime.fromtimestamp(int(ct), dt.timezone.utc).date().isoformat()
            n = sum(1 for r in audits.parse(text) if r.cls.startswith("Covered"))
            by_day[day] = n
            for k, span in (("1", DAY), ("7", 7 * DAY)):
                if int(ct) <= end - span:
                    at[k] = n
        out[f"{key}@1"], out[f"{key}@7"] = at["1"], at["7"]
        series, last = [], 0
        for d in dates:
            last = by_day.get(d, last)
            series.append(last)
        out[key] = series
    return out


# --------------------------------------------------------------------------------------------
# What changed


def changes(H: h.History, days: int) -> dict:
    """What the commits of the last `days` days did, from git alone."""
    end = H.commits[-1].time
    start = end - days * DAY
    tree: dict[str, str] = {}
    before: dict[str, str] = {}
    prs = []
    area_code = Counter()
    for c in H.commits:
        if c.time <= start:
            for p, b in c.changes:
                if b is None:
                    tree.pop(p, None)
                else:
                    tree[p] = b
            continue
        if not before:
            before = dict(tree)
        code = thm = 0
        touched = 0
        for p, b in c.changes:
            old = tree.get(p)
            if h.is_library(p):
                touched += 1
                oi = H.blobs[old] if old else None
                ni = H.blobs[b] if b else None
                dc = (ni.code if ni else 0) - (oi.code if oi else 0)
                code += dc
                thm += (_theorems(ni) if ni else 0) - (_theorems(oi) if oi else 0)
                area_code[h.area_of(p)] += dc
            if b is None:
                tree.pop(p, None)
            else:
                tree[p] = b
        prs.append({"pr": c.pr, "subject": c.subject, "time": c.time, "code": code,
                    "theorems": thm, "files": touched})
    if not before:
        before = dict(tree)
    lib_before = {p for p in before if h.is_library(p)}
    lib_after = {p for p in tree if h.is_library(p)}
    added = sorted(lib_after - lib_before, key=lambda p: -H.blobs[tree[p]].code)
    removed = sorted(lib_before - lib_after, key=lambda p: -H.blobs[before[p]].code)
    grown = Counter()
    for p in lib_after & lib_before:
        if tree[p] != before[p]:
            grown[p] = H.blobs[tree[p]].code - H.blobs[before[p]].code
    return {
        "days": days,
        "commits": len(prs),
        "code": sum(x["code"] for x in prs),
        "theorems": sum(x["theorems"] for x in prs),
        "area_code": {a: area_code[a] for a in h.AREAS + [h.OTHER] if area_code[a]},
        "added": [[h.module_of(p), H.blobs[tree[p]].code] for p in added[:40]],
        "added_count": len(added),
        "removed": [[h.module_of(p), H.blobs[before[p]].code] for p in removed[:40]],
        "removed_count": len(removed),
        "grown": [[h.module_of(p), d] for p, d in grown.most_common(12) if d > 0],
        "shrunk": [[h.module_of(p), d] for p, d in sorted(grown.items(), key=lambda x: x[1])[:8]
                   if d < 0],
        "largest": sorted(prs, key=lambda x: -abs(x["code"]))[:12],
        "recent": prs[-15:][::-1],
    }


def census_changes(entries: list[dict], titles: dict[str, str]) -> dict | None:
    """What the Lean census saw change between the last two nightly runs."""
    if len(entries) < 2:
        return None
    a, b = entries[-2], entries[-1]

    def total(e, g):
        return sum(v.get(g, 0) for v in e["by_area"].values())

    out = {"since": a["date"], "sha": a["sha"],
           "theorems": total(b, "Theorems") - total(a, "Theorems"),
           "definitions": total(b, "Definitions") - total(a, "Definitions")}
    if "results" in a and "results" in b:
        ra, rb = set(a["results"]), set(b["results"])
        out["results_added"] = [[r, titles.get(r, r)] for r in sorted(rb - ra)]
        out["results_removed"] = sorted(ra - rb)
    if "audit" in a and "audit" in b:
        moved = []
        for book, rows in b["audit"].items():
            old = a["audit"].get(book, {})
            for rid, cls in rows.items():
                if old.get(rid) != cls:
                    moved.append([book, rid, old.get(rid), cls])
        out["audit"] = moved
    return out


# --------------------------------------------------------------------------------------------
# Modules


def modules(H: h.History, census) -> dict:
    """Everything the module explorer shows, as columns."""
    tree = H.head()
    lib = {h.module_of(p): (p, H.blobs[b]) for p, b in tree.items() if h.is_library(p)}
    graph = h.import_graph(H.blobs, tree)
    names = sorted(lib)
    idx = {m: i for i, m in enumerate(names)}
    importers: dict[str, list[str]] = defaultdict(list)
    for m, deps in graph.items():
        for d in deps:
            importers[d].append(m)
    depth = h.depths(graph)
    rch = h.reach(graph)
    touches, first, last, last_pr = Counter(), {}, {}, {}
    for c in H.commits:
        for p, b in c.changes:
            if not h.is_library(p):
                continue
            m = h.module_of(p)
            touches[m] += 1
            first.setdefault(m, c.time)
            last[m] = c.time
            last_pr[m] = c.pr
    report = census[0] if census else None
    unused = defaultdict(list)
    resting = Counter()
    declared = defaultdict(list)
    if report:
        for u in report["unused"]:
            unused[u["module"]].append(u["name"])
        for rid, cone in report["cones"].items():
            for m in cone["modules"]:
                resting[m] += 1
        for rid, r in report.get("results", {}).items():
            if r.get("module"):
                declared[r["module"]].append(rid)
    rows = []
    for m in names:
        p, info = lib[m]
        kinds = report["modules"].get(m, {}).get("kinds", {}) if report else None
        thm = kinds.get("theorem", 0) if kinds is not None else _theorems(info)
        dfn = (kinds.get("def", 0) + kinds.get("abbrev", 0) + kinds.get("opaque", 0)
               if kinds is not None else _definitions(info))
        types = (kinds.get("structure", 0) + kinds.get("class", 0) + kinds.get("inductive", 0)
                 if kinds is not None else 0)
        inst = kinds.get("instance", 0) if kinds is not None else 0
        rows.append([
            m.removeprefix("CslibFrontier."), _area(m), h.subarea_of(p), info.lines, info.code,
            thm, dfn, types, inst, len(graph.get(m, ())), len(importers[m]), rch.get(m, 0),
            depth.get(m, 0), touches[m], first.get(m, 0), last.get(m, 0), last_pr.get(m),
            unused.get(m, []), resting[m], declared.get(m, []),
        ])
    return {
        "fields": ["name", "area", "subarea", "lines", "code", "theorems", "definitions", "types",
                   "instances", "imports", "importers", "reach", "depth", "commits", "first",
                   "last", "last_pr", "unused", "results_resting", "results_declared"],
        "rows": rows,
        "imports": [sorted(idx[d] for d in graph.get(m, ()) if d in idx) for m in names],
        "lean": bool(report),
        "total": len(names),
    }


# --------------------------------------------------------------------------------------------
# Results and textbooks


def _audit_index(rows_by_book):
    by_name = defaultdict(list)
    for book, rows in rows_by_book.items():
        for r in rows:
            for n in r.theorems:
                by_name[n].append(r)
    return by_name


def _matches(audit_name: str, full: str) -> bool:
    return full == audit_name or full.endswith("." + audit_name)


def results(H: h.History, census, rows_by_book) -> dict:
    registry = lc.registered_results(H.repo)
    cones = census[0]["cones"] if census else {}
    audit_names = _audit_index(rows_by_book)
    out = []
    for r in registry:
        cone = cones.get(r["id"])
        thm_modules = {t["name"]: t["module"] for t in (cone or {}).get("theorems", [])}
        rows = []
        for t in r.get("theorems", []):
            for an, rs in audit_names.items():
                if _matches(an, t):
                    rows += [[x.book, x.id, x.cls, x.line] for x in rs]
        entry = {
            "id": r["id"], "title": r.get("title", r["id"]), "topic": r.get("topic", ""),
            "module": (r.get("module") or "").removeprefix("CslibFrontier."),
            "scope": r.get("scope", ""),
            "sources": [[s.get("bib_key", ""), s.get("source_theorem", ""), s.get("locator", "")]
                        for s in r.get("sources", [])],
            "theorems": [[t, (thm_modules.get(t) or r.get("module") or "")] for t in
                         r.get("theorems", [])],
            "audit": sorted({tuple(x) for x in rows}),
        }
        if cone:
            by_area = Counter()
            for m, n in cone["modules"].items():
                by_area[_area(m)] += n
            entry["cone"] = {
                "declarations": cone["declarations"], "modules": len(cone["modules"]),
                "sorry": cone["sorry"], "found": cone["found"], "requested": cone["requested"],
                "areas": [by_area[a] for a in h.AREAS + [h.OTHER]],
                "top": [[m.removeprefix("CslibFrontier."), n] for m, n in
                        sorted(cone["modules"].items(), key=lambda x: -x[1])[:12]],
            }
        out.append(entry)
    return {"results": out, "lean": bool(census), "registry": lc.registry_available()}


def textbooks(H: h.History, rows_by_book, results_payload, daily_audit) -> dict:
    by_theorem = defaultdict(list)
    for r in results_payload["results"]:
        for t, _ in r["theorems"]:
            by_theorem[t].append(r["id"])
    books = []
    for key, path, title in audits.BOOKS:
        rows = []
        for r in sorted(rows_by_book[key], key=lambda r: (r.chapter, r.line)):
            linked = sorted({rid for an in r.theorems for t, ids in by_theorem.items()
                             if _matches(an, t) for rid in ids})
            rows.append([r.id, r.chapter, r.title, r.cls, r.status, r.line, list(r.theorems),
                         linked])
        books.append({"key": key, "title": title, "path": path, "rows": rows,
                      "covered": daily_audit.get(key, [])})
    return {"books": books, "classes": audits.CLASSES}
