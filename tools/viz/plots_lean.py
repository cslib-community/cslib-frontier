# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Views built from the Lean declaration census (see `lean_census.py`)."""

from __future__ import annotations

import datetime as dt
from collections import Counter

import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import numpy as np

import history as h
import lean_census as lc
import style as s


def declarations(H: h.History, out, census):
    """What the library declares, by area and kind, as Lean sees it."""
    report, entries = census
    summary = lc.summarize(report)
    T = s.theme()
    areas = [a for a in s.ALL_AREAS if a in summary["by_area"]]
    groups = [g for g in lc.GROUPS if any(summary["by_area"][a].get(g) for a in areas)]
    colors = {g: T.series[i] for i, g in enumerate(groups)}
    series = len(entries) >= 2
    fig = plt.figure(figsize=(13, 7.2 if series else 6.4))
    ax = fig.add_axes([0.15, 0.40 if series else 0.1, 0.62, 0.45 if series else 0.68])
    ys = np.arange(len(areas))[::-1]
    left = np.zeros(len(areas))
    for g in groups:
        vals = np.array([summary["by_area"][a].get(g, 0) for a in areas])
        ax.barh(ys, vals, left=left, height=0.62, color=colors[g], label=g,
                edgecolor=T.surface, linewidth=1.5)
        left += vals
    xmax = float(left.max()) if len(left) else 0.0
    for y, tot in zip(ys, left):
        ax.text(tot + max(xmax, 1.0) * 0.01, y, s.human(tot), va="center", fontsize=9.5,
                color=T.ink2)
    ax.set_yticks(ys, areas)
    ax.xaxis.set_major_formatter(s.HUMAN)
    ax.set_xlim(0, max(xmax * 1.1, 1.0))
    if groups:
        ax.legend(loc="lower left", bbox_to_anchor=(0, 1.0), ncols=len(groups), borderaxespad=0.4)
    s.clean_axes(ax, grid_axis="x")
    ax.spines["bottom"].set_visible(False)
    # The text scanner's count for the same tree, for comparison.
    tree = H.head()
    text = Counter()
    for p, b in tree.items():
        if h.is_library(p):
            text.update(H.blobs[b].decls)
    lean_thm = sum(v.get("Theorems", 0) for v in summary["by_area"].values())
    text_thm = text["theorem"] + text["lemma"]
    note = (f"Theorems: Lean {lean_thm:,} · source text {text_thm:,}   "
            f"Generated declarations not shown: {summary['generated']:,}")
    fig.text(0.15, (0.33 if series else 0.035), note, fontsize=9.5, color=T.ink2)
    if series:
        ax2 = fig.add_axes([0.15, 0.07, 0.62, 0.2])
        dates = [dt.date.fromisoformat(e["date"]) for e in entries]
        for g in groups:
            vals = [sum(a.get(g, 0) for a in e["by_area"].values()) for e in entries]
            ax2.plot(dates, vals, color=colors[g], marker="o", ms=4)
        ax2.yaxis.set_major_formatter(s.HUMAN)
        ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
        ax2.set_title("Nightly census", loc="left", fontsize=11)
        s.clean_axes(ax2)
    series_note = (
        f"Census series: {len(entries)} nightly run{'s' if len(entries) != 1 else ''} since "
        f"{entries[0]['date']}" if entries else "Census series: single snapshot (no history file)"
    )
    s.titles(fig, ax, "What the library declares, as Lean sees it",
             f"Declarations in the built .olean files of CslibFrontier/, written ones only, by area "
             f"and kind · includes what commands and macros generate (enc_structure, deriving)\n"
             f"{series_note}")
    csv = s.write_csv(out, "lean-declarations", ["area"] + lc.GROUPS,
                      [[a] + [summary["by_area"].get(a, {}).get(g, 0) for g in lc.GROUPS]
                       for a in s.ALL_AREAS])
    return s.save(fig, out, "lean-declarations") + [csv]


def _candidate_imports(report: dict) -> list[tuple[int, list[int]]]:
    g = report["moduleGraph"]
    names, imports, used = g["names"], g["imports"], g["used"]
    declares = {m: sum(v["kinds"].values()) for m, v in report.get("modules", {}).items()}
    out: list[tuple[int, list[int]]] = []
    for i in range(len(used)):
        # A module that declares nothing is an umbrella: it imports in order to re-export.
        if declares.get(names[i], 1) == 0:
            continue
        out.append((i, [j for j in dict.fromkeys(imports[i]) if names[j] != "Init"]))
    return out


def checked_imports(report: dict) -> int:
    """How many distinct non-`Init` direct imports of non-umbrella modules are checked."""
    return sum(len(imps) for _, imps in _candidate_imports(report))


def unused_imports(report: dict) -> dict[str, list[str]]:
    """Direct imports of each library module that nothing it uses can come from.

    An import is needed when some constant the module's declarations mention is defined in the
    imported module or in anything that module imports, library or dependency alike. Modules
    that declare nothing are umbrellas that import to re-export, and are skipped; so is the core
    prelude `Init`, which every module imports implicitly."""
    g = report["moduleGraph"]
    names, imports, used = g["names"], g["imports"], g["used"]
    n = len(names)
    closure = [0] * n
    state = [0] * n
    for root in range(n):
        if state[root]:
            continue
        stack = [(root, iter(imports[root]))]
        state[root] = 1
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop()
                bits = 1 << node
                for d in imports[node]:
                    bits |= closure[d]
                closure[node] = bits
                state[node] = 2
            elif not state[nxt]:
                state[nxt] = 1
                stack.append((nxt, iter(imports[nxt])))
    out: dict[str, list[str]] = {}
    for i, imps in _candidate_imports(report):
        used_bits = 0
        for u in used[i]:
            used_bits |= 1 << u
        dead = [names[j] for j in imps if not closure[j] & used_bits]
        if dead:
            out[names[i]] = dead
    return out


def _area(module: str) -> str:
    return h.area_of(module.replace(".", "/") + ".lean")


def result_cones(H: h.History, out, census):
    """What does each registered result rest on, inside the library?"""
    report, _ = census
    cones = report["cones"]
    results = report.get("results", {})
    T = s.theme()
    colors = s.area_colors(T)
    ranked = sorted(cones, key=lambda k: -cones[k]["declarations"])
    top = ranked[:30]
    fig = plt.figure(figsize=(14, 11))
    ax = fig.add_axes([0.36, 0.30, 0.52, 0.58])
    ys = np.arange(len(top))[::-1]
    left = np.zeros(len(top))
    for a in s.ALL_AREAS:
        vals = np.array([sum(n for m, n in cones[k]["modules"].items() if _area(m) == a)
                         for k in top])
        if vals.sum():
            ax.barh(ys, vals, left=left, height=0.66, color=colors[a], label=a,
                    edgecolor=T.surface, linewidth=0.8)
        left += vals
    xmax = float(left.max()) if len(left) else 0.0
    for y, k, tot in zip(ys, top, left):
        ax.text(tot + max(xmax, 1.0) * 0.01, y, f"{int(tot):,}", va="center", fontsize=8.5,
                color=T.ink2)
    labels = []
    for k in top:
        title = (results.get(k) or {}).get("title") or k
        labels.append(title if len(title) <= 62 else title[:61] + "…")
    ax.set_yticks(ys, labels, fontsize=8.5)
    ax.xaxis.set_major_formatter(s.HUMAN)
    ax.set_xlim(0, max(xmax * 1.1, 1.0))
    ax.set_xlabel("Library declarations in the result's dependency cone")
    if not top:
        ax.text(0.5, 0.5, "No registered results available", transform=ax.transAxes,
                ha="center", va="center", color=T.ink2)
    elif ax.get_legend_handles_labels()[0]:
        ax.legend(loc="lower right", fontsize=9)
    s.clean_axes(ax, grid_axis="x")
    ax.spines["bottom"].set_visible(False)
    # Distribution of all results.
    ax2 = fig.add_axes([0.36, 0.06, 0.52, 0.15])
    sizes = np.array([cones[k]["declarations"] for k in ranked if cones[k]["found"]])
    if len(sizes):
        ax2.hist(sizes, bins=40, color=T.series[0], edgecolor=T.surface, linewidth=0.6)
    ax2.set_xlabel("Cone size (declarations), every registered result")
    ax2.set_ylabel("Results")
    ax2.xaxis.set_major_formatter(s.HUMAN)
    s.clean_axes(ax2)
    n_sorry = sum(1 for v in cones.values() if v["sorry"])
    missing = sum(1 for v in cones.values() if v["found"] < v["requested"])
    sorry_note = ("no result's cone contains sorryAx" if n_sorry == 0
                  else f"{n_sorry} results' cones contain sorryAx")
    s.titles(fig, ax, "What the headline results rest on",
             f"For each result in the registry (CslibFrontierResults), the written library "
             f"declarations its theorems depend on, directly or transitively, by area · "
             f"{len(cones)} results, median {int(np.median(sizes)) if len(sizes) else 0:,} "
             f"declarations\n{sorry_note}"
             + (f" · {missing} results name a theorem the build does not have" if missing else "")
             + " · Mathlib and core are outside the cone")
    csv = s.write_csv(out, "result-cones",
                      ["id", "title", "declarations", "modules", "contains_sorry"] + s.ALL_AREAS,
                      [[k, (results.get(k) or {}).get("title", ""), cones[k]["declarations"],
                        len(cones[k]["modules"]), cones[k]["sorry"]]
                       + [sum(n for m, n in cones[k]["modules"].items() if _area(m) == a)
                          for a in s.ALL_AREAS] for k in ranked])
    return s.save(fig, out, "result-cones") + [csv]


def load_bearing(H: h.History, out, census):
    """Which declarations does the rest of the library lean on most?"""
    report, _ = census
    top = report["top"][:30]
    T = s.theme()
    kinds = ["theorem", "def", "abbrev", "structure", "class", "inductive", "instance", "opaque"]
    present = [k for k in kinds if any(t["kind"] == k for t in top)]
    colors = {k: T.series[i] for i, k in enumerate(present)}
    fig, ax = plt.subplots(figsize=(13, 10))
    fig.subplots_adjust(left=0.42, right=0.95, top=0.88, bottom=0.06)
    ys = np.arange(len(top))[::-1]
    vals = [t["refs"] for t in top]
    if vals:
        vmax = max(vals)
        ax.barh(ys, vals, height=0.62, color=[colors.get(t["kind"], T.other) for t in top])
        for y, t in zip(ys, top):
            ax.text(t["refs"] + max(vmax, 1) * 0.01, y, f"{t['refs']:,}", va="center",
                    fontsize=8.5, color=T.ink2)
        ax.set_xlim(0, max(vmax * 1.1, 1.0))
    else:
        ax.set_xlim(0, 1.0)
        ax.text(0.5, 0.5, "No cross-declaration references", transform=ax.transAxes,
                ha="center", va="center", color=T.ink2)
    names = [t["name"] if len(t["name"]) <= 58 else "…" + t["name"][-57:] for t in top]
    ax.set_yticks(ys, names, fontsize=8.5)
    ax.xaxis.set_major_formatter(s.HUMAN)
    ax.set_xlabel("Written declarations that mention it")
    if present:
        from matplotlib.patches import Patch
        ax.legend([Patch(color=colors[k]) for k in present], present, loc="lower right")
    s.clean_axes(ax, grid_axis="x")
    ax.spines["bottom"].set_visible(False)
    s.titles(fig, ax, "Load-bearing declarations",
             "The declarations that the most other written declarations of the library mention "
             "directly\nLean-generated helpers (auxiliary proofs, matchers, equation lemmas) count "
             "for the declaration that owns them")
    csv = s.write_csv(out, "load-bearing", ["name", "kind", "module", "mentioned_by"],
                      [[t["name"], t["kind"], t["module"], t["refs"]] for t in report["top"]])
    return s.save(fig, out, "load-bearing") + [csv]


def unused_definitions(H: h.History, out, census):
    """Which definitions does nothing in the library mention?"""
    report, _ = census
    unused = report["unused"]
    T = s.theme()
    totals = Counter()
    for m, v in report["modules"].items():
        k = v["kinds"]
        totals[_area(m)] += sum(k.get(x, 0) for x in ("def", "abbrev", "structure", "inductive",
                                                         "class", "opaque"))
    per = Counter(_area(u["module"]) for u in unused)
    csv = s.write_csv(out, "unused-definitions", ["name", "kind", "module"],
                      [[u["name"], u["kind"], u["module"]]
                       for u in sorted(unused, key=lambda u: (u["module"], u["name"]))])
    fig = plt.figure(figsize=(14, 7.5))
    ax = fig.add_axes([0.12, 0.1, 0.33, 0.7])
    areas = [a for a in s.ALL_AREAS if totals[a]]
    ys = np.arange(len(areas))[::-1]
    vals = [per[a] for a in areas]
    ax.barh(ys, vals, height=0.62, color=T.series[1])
    for y, a, v in zip(ys, areas, vals):
        ax.text(v + max(vals + [1]) * 0.02, y, f"{v}  ({v / totals[a]:.1%} of {totals[a]:,})",
                va="center", fontsize=9, color=T.ink2)
    ax.set_yticks(ys, areas)
    ax.set_xlim(0, max(vals + [1]) * 1.7)
    ax.set_title("Unreferenced definitions by area", loc="left", fontsize=11.5)
    s.clean_axes(ax, grid_axis="x")
    ax.spines["bottom"].set_visible(False)
    by_mod = Counter(u["module"] for u in unused)
    fig.text(0.52, 0.80, "Modules with the most", fontsize=11.5, fontweight="bold", va="top")
    for k, (m, n) in enumerate(by_mod.most_common(15)):
        y = 0.75 - 0.043 * k
        name = m.removeprefix("CslibFrontier.")
        if len(name) > 72:
            name = "…" + name[-71:]
        fig.text(0.52, y, f"{n:>3}", fontsize=9.5, color=T.ink2, fontweight="bold",
                 va="center")
        fig.text(0.56, y, name, fontsize=9.5, va="center")
    s.titles(fig, ax, "Definitions nothing uses",
             f"Written definitions, abbreviations and types that no other declaration of the "
             f"library mentions · {len(unused):,} · full list in unused-definitions.csv\n"
             f"Candidates only: tests are not built here, and API meant for readers of a cited "
             f"result can be unused by design. Notation, tactics and extensions are excluded.")
    return s.save(fig, out, "unused-definitions") + [csv]
