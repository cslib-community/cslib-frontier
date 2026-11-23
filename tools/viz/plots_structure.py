# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Structure at head: treemap, hotspots, area matrices, hub modules, commit cadence."""

from __future__ import annotations

import datetime as dt
from collections import Counter, defaultdict

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LogNorm
from matplotlib.patches import Rectangle

import history as h
import style as s

# --------------------------------------------------------------------------------------------
# Squarified treemap layout (Bruls, Huizing & van Wijk 2000).


def squarify(values, x, y, w, hgt):
    """Lay out positive `values` (any order) in the rectangle; returns rects in input order."""
    idx = sorted(range(len(values)), key=lambda i: -values[i])
    total = sum(values)
    if total <= 0:
        return [(x, y, 0, 0)] * len(values)
    scale = w * hgt / total
    areas = [(i, values[i] * scale) for i in idx]
    rects = {}

    def worst(row, side):
        s_ = sum(a for _, a in row)
        mx = max(a for _, a in row)
        mn = min(a for _, a in row)
        return max(side * side * mx / (s_ * s_), (s_ * s_) / (side * side * mn))

    row: list = []
    while areas:
        side = min(w, hgt)
        item = areas[0]
        if not row or worst(row + [item], side) <= worst(row, side):
            row.append(item)
            areas.pop(0)
            if areas:
                continue
        # lay out the row along the shorter side
        rs = sum(a for _, a in row)
        if w >= hgt:
            cw = rs / hgt if hgt else 0
            cy = y
            for i, a in row:
                ch = a / cw if cw else 0
                rects[i] = (x, cy, cw, ch)
                cy += ch
            x += cw
            w -= cw
        else:
            ch = rs / w if w else 0
            cx = x
            for i, a in row:
                cw = a / ch if ch else 0
                rects[i] = (cx, y, cw, ch)
                cx += cw
            y += ch
            hgt -= ch
        row = []
    return [rects[i] for i in range(len(values))]


def _text_width(text: str, fontsize: float) -> float:
    """Rough rendered width in inches (treemap units are inches)."""
    return len(text) * fontsize * 0.56 / 72


def _log_ticks(axis, vmax):
    ticks = [v for v in (1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000) if v <= vmax * 1.01]
    axis.set_ticks(ticks, [s.human(v) for v in ticks])
    axis.set_minor_locator(plt.NullLocator())


def _head_library(H):
    tree = H.head()
    return {p: H.blobs[b] for p, b in tree.items() if h.is_library(p)}


def treemap(H: h.History, out):
    """Where does the code live, and which parts are changing most?"""
    files = _head_library(H)
    touches = H.touches()
    by_area: dict[str, dict[str, list[str]]] = defaultdict(lambda: defaultdict(list))
    for p, info in files.items():
        if info.code > 0:
            parts = p.split("/")
            area = parts[1] if len(parts) > 2 else "(root)"
            by_area[area][h.subarea_of(p)].append(p)
    T = s.theme()
    W, Hh = 16.0, 9.0
    fig = plt.figure(figsize=(W, Hh + 1.2))
    ax = fig.add_axes([0.005, 0.06, 0.99, Hh / (Hh + 1.2) - 0.06])
    ax.set_xlim(0, W)
    ax.set_ylim(Hh, 0)
    ax.axis("off")
    cmap = s.sequential_cmap(T)
    vmax = max(touches[p] for p in files)
    norm = LogNorm(vmin=1, vmax=vmax)
    areas = sorted(by_area, key=lambda a: -sum(files[p].code for sub in by_area[a].values() for p in sub))
    a_vals = [sum(files[p].code for sub in by_area[a].values() for p in sub) for a in areas]
    for a, (ax0, ay0, aw, ah) in zip(areas, squarify(a_vals, 0, 0, W, Hh)):
        subs = sorted(by_area[a])
        s_vals = [sum(files[p].code for p in by_area[a][sb]) for sb in subs]
        pad_top = 0.22 if ah > 0.6 and aw > 0.9 else 0.0
        for sb, (sx, sy, sw, sh) in zip(subs, squarify(s_vals, ax0 + 0.03, ay0 + pad_top + 0.03,
                                                       aw - 0.06, ah - pad_top - 0.06)):
            ps = by_area[a][sb]
            for p, (fx, fy, fw, fh) in zip(ps, squarify([files[p].code for p in ps], sx, sy, sw, sh)):
                ax.add_patch(Rectangle((fx, fy), fw, fh, facecolor=cmap(norm(max(touches[p], 1))),
                                       edgecolor=T.surface, linewidth=0.15))
            ax.add_patch(Rectangle((sx, sy), sw, sh, fill=False, edgecolor=T.surface, linewidth=1.2))
            label = sb.split("/", 1)[-1]
            fs = min(9.5, max(6.5, sw * 6))
            if sh > 0.3 and _text_width(label, fs) + 0.12 < sw:
                ax.text(sx + 0.05, sy + 0.05, label, va="top", ha="left", fontsize=fs,
                        color="#ffffff", fontweight="bold", clip_on=True,
                        bbox=dict(boxstyle="square,pad=0.15", fc=(0, 0, 0, 0.35), ec="none"))
        ax.add_patch(Rectangle((ax0, ay0), aw, ah, fill=False, edgecolor=T.surface, linewidth=3))
        if pad_top:
            ax.add_patch(Rectangle((ax0, ay0), aw, pad_top, facecolor=T.surface, edgecolor="none"))
            for head in (f"{a}  ·  {s.human(sum(s_vals))} lines", a):
                if _text_width(head, 10.5) + 0.1 < aw:
                    ax.text(ax0 + 0.06, ay0 + pad_top / 2 + 0.01, head, va="center", ha="left",
                            fontsize=10.5, fontweight="bold", color=T.ink)
                    break
    cax = fig.add_axes([0.62, 0.025, 0.2, 0.014])
    cb = fig.colorbar(plt.cm.ScalarMappable(norm=norm, cmap=cmap), cax=cax, orientation="horizontal")
    cb.outline.set_visible(False)
    _log_ticks(cb.ax.xaxis, vmax)
    cb.ax.tick_params(labelsize=9, colors=T.ink2)
    fig.text(0.61, 0.032, "Commits that changed the module", ha="right", va="center",
             fontsize=9.5, color=T.ink2)
    fig.text(0.005, 0.975, "Where the code lives — and where it churns", fontsize=16,
             fontweight="bold", va="top")
    fig.text(0.005, 0.94, f"Each rectangle is one module of CslibFrontier/, sized by lines of code "
             f"and shaded by how many commits on main have changed it · {len(files)} modules",
             fontsize=10.5, color=T.ink2, va="top")
    return s.save(fig, out, "treemap")


def hotspots(H: h.History, out):
    """Which large files are also edited constantly? (Size × change frequency.)"""
    files = _head_library(H)
    touches = H.touches()
    paths = [p for p, i in files.items() if i.code > 0]
    x = np.array([files[p].code for p in paths], dtype=float)
    y = np.array([touches[p] for p in paths], dtype=float)
    score = x * y
    top = np.argsort(score)[-14:][::-1]
    T = s.theme()
    fig = plt.figure(figsize=(14, 7.5))
    ax = fig.add_axes([0.065, 0.09, 0.5, 0.76])
    rng = np.random.default_rng(0)
    yj = y * np.exp(rng.uniform(-0.12, 0.12, len(y)))  # jitter the integer touch counts
    ax.scatter(x, yj, s=9, color=T.series[0], alpha=0.25, linewidths=0)
    ax.scatter(x[top], yj[top], s=150, color=T.series[1], edgecolors=T.surface, linewidths=1.5,
               zorder=4)
    for rank, i in enumerate(top, 1):
        ax.text(x[i], yj[i], str(rank), ha="center", va="center", fontsize=7, color="#ffffff",
                fontweight="bold", zorder=5)
    ax.set_xscale("log")
    ax.set_yscale("log")
    _log_ticks(ax.yaxis, y.max())
    xt = [v for v in (1, 10, 100, 1000, 10000) if v <= x.max() * 2]
    ax.set_xticks(xt, [s.human(v) for v in xt])
    ax.xaxis.set_minor_locator(plt.NullLocator())
    ax.set_xlabel("Lines of code in the module (log)")
    ax.set_ylabel("Commits on main that changed it (log)")
    s.clean_axes(ax, grid_axis="both")
    ax.spines["left"].set_visible(True)
    ax.spines["left"].set_color(T.axis)
    fig.text(0.6, 0.85, "Top hotspots", fontsize=11.5, fontweight="bold", va="top")
    fig.text(0.975, 0.85, "lines · commits", fontsize=9.5, color=T.ink2, va="top", ha="right")
    for rank, i in enumerate(top, 1):
        yy = 0.85 - 0.052 * rank
        name = paths[i].removeprefix("CslibFrontier/").removesuffix(".lean")
        if len(name) > 52:
            name = "…" + name[-51:]
        fig.text(0.6, yy, f"{rank:>2}", fontsize=9.5, color=T.ink2, fontweight="bold",
                 va="center")
        fig.text(0.62, yy, name, fontsize=9.5, va="center")
        fig.text(0.975, yy, f"{int(x[i]):,} · {int(y[i])}", fontsize=9.5, color=T.ink2,
                 va="center", ha="right")
    s.titles(fig, ax, "Hotspots: big modules that keep changing",
             f"One dot per module · orange: the 14 largest by size × change count, the usual first "
             f"candidates for splitting or stabilising · {len(paths)} modules")
    csv = s.write_csv(out, "hotspots", ["module", "code_lines", "commits"],
                      sorted(([p.removesuffix(".lean").replace("/", "."), int(a), int(b)]
                              for p, a, b in zip(paths, x, y)), key=lambda r: -r[1] * r[2]))
    return s.save(fig, out, "hotspots") + [csv]


def _top_subareas(files, n=26):
    code = Counter()
    for p, i in files.items():
        code[h.subarea_of(p)] += i.code
    top = [sb for sb, _ in code.most_common(n)]
    area_rank = {a: k for k, a in enumerate(s.ALL_AREAS)}
    top.sort(key=lambda sb: (area_rank.get(sb.split("/")[0], len(area_rank)), -code[sb]))
    return top


def _matrix_plot(M, labels, title, subtitle, cbar_label, name, out, diag_note, fmt):
    T = s.theme()
    n = len(labels)
    fig, ax = plt.subplots(figsize=(13, 13))
    fig.subplots_adjust(left=0.25, right=0.88, top=0.79, bottom=0.1)
    cmap = s.sequential_cmap(T)
    cmap.set_bad(T.surface)
    data = np.where(M > 0, M, np.nan)
    pos = data[~np.isnan(data)]
    norm = LogNorm(vmin=max(pos.min(), 1e-3), vmax=pos.max())
    im = ax.imshow(data, cmap=cmap, norm=norm, interpolation="nearest")
    for k in range(n):
        ax.add_patch(Rectangle((k - 0.5, k - 0.5), 1, 1, fill=False, edgecolor=T.ink2, lw=0.8,
                               hatch="////", alpha=0.35))
    ax.set_xticks(range(n), [l.split("/", 1)[-1] for l in labels], rotation=90, fontsize=9)
    ax.set_yticks(range(n), labels, fontsize=9)
    ax.xaxis.tick_top()
    ax.set_xticks(np.arange(-0.5, n), minor=True)
    ax.set_yticks(np.arange(-0.5, n), minor=True)
    ax.grid(which="minor", color=T.surface, linewidth=1.5)
    ax.tick_params(which="both", length=0)
    for sp in ax.spines.values():
        sp.set_visible(False)
    # Area separators.
    areas = [l.split("/")[0] for l in labels]
    for k in range(1, n):
        if areas[k] != areas[k - 1]:
            ax.axhline(k - 0.5, color=T.ink2, lw=1)
            ax.axvline(k - 0.5, color=T.ink2, lw=1)
    cax = fig.add_axes([0.9, 0.2, 0.015, 0.45])
    cb = fig.colorbar(im, cax=cax)
    cb.outline.set_visible(False)
    cb.set_label(cbar_label, color=T.ink2)
    cb.ax.yaxis.set_major_formatter(s.FuncFormatter(lambda v, _: fmt(v)))
    cb.ax.yaxis.set_minor_formatter(plt.NullFormatter())
    fig.text(0.012, 0.985, title, fontsize=16, fontweight="bold", va="top")
    # Area names over each column group.
    start = 0
    for k in range(1, n + 1):
        if k == n or areas[k] != areas[start]:
            mid = (start + k - 1) / 2
            ax.text(mid, n - 0.3, areas[start], ha="center" if k - start >= 3 else "center",
                    va="top", fontsize=9.5, fontweight="bold", color=T.ink,
                    rotation=0 if k - start >= 3 else 90)
            start = k
    fig.text(0.012, 0.955, subtitle + "\n" + diag_note, fontsize=10.5, color=T.ink2, va="top")
    csv = s.write_csv(out, name, ["from", "to", "value"],
                      [[labels[i], labels[j], round(float(M[i, j]), 6)]
                       for i in range(n) for j in range(n) if M[i, j]])
    return s.save(fig, out, name) + [csv]


def import_matrix(H: h.History, out):
    """Which sub-areas import which?"""
    files = _head_library(H)
    labels = _top_subareas(files)
    k = {sb: i for i, sb in enumerate(labels)}
    mod_sub = {h.module_of(p): h.subarea_of(p) for p in files}
    M = np.zeros((len(labels), len(labels)))
    for p, info in files.items():
        r = k.get(h.subarea_of(p))
        if r is None:
            continue
        for imp in info.imports:
            c = k.get(mod_sub.get(imp, ""))
            if c is not None:
                M[r, c] += 1
    return _matrix_plot(
        M, labels, "Who imports whom",
        f"Import statements from modules of the row sub-area into modules of the column sub-area · "
        f"the {len(labels)} largest sub-areas, grouped by area",
        "Import statements (log scale)", "import-matrix", out,
        "Read a row to see what an area builds on, a column to see who depends on it. "
        "Hatched diagonal: imports within a sub-area.", s.human)


def change_coupling(H: h.History, out):
    """Which sub-areas change together (logical coupling), whether or not they import each other?"""
    files = _head_library(H)
    labels = _top_subareas(files)
    k = {sb: i for i, sb in enumerate(labels)}
    n = len(labels)
    co = np.zeros((n, n))
    cnt = np.zeros(n)
    used = 0
    for c in H.commits:
        paths = [p for p, _ in c.changes if h.is_library(p)]
        if not paths or len(paths) > 40:  # skip sweeping refactors that touch everything
            continue
        subs = sorted({k[sb] for sb in map(h.subarea_of, paths) if sb in k})
        if not subs:
            continue
        used += 1
        for i in subs:
            cnt[i] += 1
            for j in subs:
                if j != i:
                    co[i, j] += 1
    J = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j and co[i, j]:
                J[i, j] = co[i, j] / (cnt[i] + cnt[j] - co[i, j])
    return _matrix_plot(
        J, labels, "Change coupling: what moves together",
        f"Share of commits touching either sub-area that touch both (Jaccard index) · {used} commits "
        f"on main changing at most 40 library files",
        "Jaccard index (log scale)", "change-coupling", out,
        "Bright cells far from the diagonal, especially where the import matrix is dark, are hidden "
        "dependencies: code that has to change in step without importing each other.",
        lambda v: f"{v:.0%}" if v >= 0.01 else f"{v:.1%}")


def hubs(H: h.History, out):
    """Which modules would rebuild the most of the library if they changed?"""
    tree = H.head()
    g = h.import_graph(H.blobs, tree)
    mods = list(g)
    reach = h.reach(g)
    top = sorted(mods, key=lambda m: -reach[m])
    top = [m for m in top if m != "CslibFrontier.Init"][:28]
    T = s.theme()
    fig, ax = plt.subplots(figsize=(12, 10))
    fig.subplots_adjust(left=0.45, right=0.93, top=0.89, bottom=0.05)
    ys = np.arange(len(top))[::-1]
    vals = [reach[m] / len(mods) for m in top]
    ax.barh(ys, vals, height=0.62, color=T.series[0])
    for y, m, v in zip(ys, top, vals):
        ax.text(v + 0.005, y, f"{v:.0%}  ·  {s.human(reach[m])}", va="center", fontsize=9,
                color=T.ink2)
    ax.set_yticks(ys, [m.removeprefix("CslibFrontier.") for m in top], fontsize=9)
    ax.set_xlim(0, max(vals) * 1.18)
    ax.xaxis.set_major_formatter(s.FuncFormatter(lambda v, _: f"{v:.0%}"))
    ax.set_xlabel("Share of library modules that import it, directly or transitively")
    s.clean_axes(ax, grid_axis="x")
    ax.spines["bottom"].set_visible(False)
    s.titles(fig, ax, "Hub modules: the blast radius of an edit",
             f"Changing one of these forces a rebuild of the share shown · {len(mods)} modules "
             f"(CslibFrontier.Init, imported by everything, omitted)")
    csv = s.write_csv(out, "hubs", ["module", "dependent_modules", "share"],
                      [[m, reach[m], round(reach[m] / len(mods), 4)]
                       for m in sorted(mods, key=lambda m: -reach[m])])
    return s.save(fig, out, "hubs") + [csv]


def cadence(H: h.History, out):
    """When does work land on main? (UTC.)"""
    days = sorted({c.date for c in H.commits})
    d0 = days[0]
    nd = (days[-1] - d0).days + 1
    M = np.zeros((24, nd))
    for c in H.commits:
        t = dt.datetime.fromtimestamp(c.time, dt.timezone.utc)
        M[t.hour, (t.date() - d0).days] += 1
    T = s.theme()
    fig, (ax, axb) = plt.subplots(2, 1, figsize=(13, 7.5), height_ratios=[3, 1], sharex=True)
    fig.subplots_adjust(left=0.07, right=0.9, top=0.86, bottom=0.08, hspace=0.06)
    cmap = s.sequential_cmap(T)
    cmap.set_bad(T.surface)
    data = np.where(M > 0, M, np.nan)
    im = ax.imshow(data, aspect="auto", cmap=cmap, interpolation="nearest",
                   extent=(-0.5, nd - 0.5, 23.5, -0.5))
    ax.set_yticks([0, 6, 12, 18, 23], ["00:00", "06:00", "12:00", "18:00", "23:00"])
    ax.set_ylabel("Hour (UTC)")
    for sp in ax.spines.values():
        sp.set_visible(False)
    cax = fig.add_axes([0.915, 0.42, 0.012, 0.4])
    cb = fig.colorbar(im, cax=cax)
    cb.outline.set_visible(False)
    cb.set_label("Commits in the hour", color=T.ink2)
    per_day = M.sum(axis=0)
    axb.bar(np.arange(nd), per_day, width=0.8, color=T.series[0])
    axb.set_ylabel("Per day")
    s.clean_axes(axb)
    ticks = [i for i in range(nd) if (d0 + dt.timedelta(days=i)).weekday() == 0]
    axb.set_xticks(ticks, [f"{d0 + dt.timedelta(days=i):%b %-d}" for i in ticks])
    s.titles(fig, ax, "When work lands",
             f"Commits on main that change Lean files, by UTC day and hour · {len(H.commits)} commits,"
             f" busiest day {int(per_day.max())}")
    csv = s.write_csv(out, "cadence", ["date", "hour_utc", "commits"],
                      [[(d0 + dt.timedelta(days=j)).isoformat(), i, int(M[i, j])]
                       for j in range(nd) for i in range(24) if M[i, j]])
    return s.save(fig, out, "cadence") + [csv]
