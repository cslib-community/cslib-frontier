# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Growth over time: code by area, declarations, daily churn, import depth."""

from __future__ import annotations

import subprocess
from collections import Counter, defaultdict

import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import matplotlib.transforms as transforms
import numpy as np

import history as h
import style as s


def _date_axis(ax):
    ax.xaxis.set_major_locator(mdates.WeekdayLocator(byweekday=mdates.MO))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))


def _spread(ys, gap):
    """Nudge label positions apart (keeping order) so that neighbours are at least `gap` apart."""
    order = sorted(range(len(ys)), key=lambda i: ys[i])
    out = list(ys)
    for k in range(1, len(order)):
        i, j = order[k - 1], order[k]
        out[j] = max(out[j], out[i] + gap)
    return out


def _end_label(ax, x, y, text, color, pad=10):
    """A coloured square key and an ink label just right of the plot at data height `y`."""
    base = transforms.offset_copy(ax.transData, fig=ax.figure, x=pad, y=0, units="points")
    ax.plot([x], [y], marker="s", ms=8, color=color, transform=base, clip_on=False, zorder=6)
    txt = transforms.offset_copy(ax.transData, fig=ax.figure, x=pad + 9, y=0, units="points")
    ax.text(x, y, text, transform=txt, va="center", fontsize=10, color=s.theme().ink)


def growth_by_area(H: h.History, out):
    """Which areas drove the library's growth?"""
    snaps = H.daily()
    dates = [d for d, _, _ in snaps]
    series = {a: [] for a in s.ALL_AREAS}
    for _, _, tree in snaps:
        tot = Counter()
        for p, b in tree.items():
            if h.is_library(p):
                tot[h.area_of(p)] += H.blobs[b].code
        for a in s.ALL_AREAS:
            series[a].append(tot[a])
    colors = s.area_colors()
    fig, ax = plt.subplots(figsize=(12, 6.5))
    fig.subplots_adjust(left=0.07, right=0.83, top=0.86, bottom=0.08)
    ys = [series[a] for a in s.ALL_AREAS]
    stacks = ax.stackplot(dates, ys, colors=[colors[a] for a in s.ALL_AREAS],
                          edgecolor=s.theme().surface, linewidth=0.8)
    del stacks
    # Direct labels at the right edge, centred in each band.
    cum = np.cumsum(np.array(ys), axis=0)
    last = cum[:, -1]
    lows = np.concatenate([[0], last[:-1]])
    total = last[-1]
    ys_lab = _spread([(lo + hi) / 2 for lo, hi in zip(lows, last)], total * 0.04)
    for a, lo, hi, y in zip(s.ALL_AREAS, lows, last, ys_lab):
        _end_label(ax, dates[-1], y, f"{a}  {s.human(hi - lo)}", colors[a])
    ax.yaxis.set_major_formatter(s.HUMAN)
    ax.set_xlim(dates[0], dates[-1])
    ax.set_ylim(0, total * 1.03)
    ax.set_ylabel("Lines of code (excluding comments and blanks)")
    _date_axis(ax)
    s.clean_axes(ax)
    s.titles(fig, ax, "Library code by area",
             f"CslibFrontier/, daily snapshots along main · {dates[0]:%b %-d} – {dates[-1]:%b %-d, %Y}"
             f" · {s.human(total)} lines of code")
    csv = s.write_csv(out, "growth-by-area", ["date"] + s.ALL_AREAS,
                      [[d.isoformat()] + [series[a][i] for a in s.ALL_AREAS]
                       for i, d in enumerate(dates)])
    return s.save(fig, out, "growth-by-area") + [csv]


def declarations(H: h.History, out):
    """How many results and definitions exist, and how big is a typical one?"""
    snaps = H.daily()
    dates = [d for d, _, _ in snaps]
    thm, dfn, other, code = [], [], [], []
    for _, _, tree in snaps:
        c = Counter()
        loc = 0
        for p, b in tree.items():
            if h.is_library(p):
                info = H.blobs[b]
                c.update(info.decls)
                loc += info.code
        thm.append(c["theorem"] + c["lemma"])
        dfn.append(c["def"] + c["abbrev"])
        other.append(c["structure"] + c["inductive"] + c["class"] + c["instance"])
        code.append(loc)
    T = s.theme()
    fig, (ax, ax2) = plt.subplots(2, 1, figsize=(12, 8), height_ratios=[2.2, 1], sharex=True)
    fig.subplots_adjust(left=0.08, right=0.87, top=0.88, bottom=0.07, hspace=0.18)
    lines = [("Theorems", thm, T.series[0]), ("Definitions", dfn, T.series[1]),
             ("Types & instances", other, T.series[2])]
    for label, ys, col in lines:
        ax.plot(dates, ys, color=col, label=label)
        ax.plot(dates[-1], ys[-1], "o", ms=8, color=col, mec=T.surface, mew=2, zorder=5)
        ax.annotate(f"{label}  {s.human(ys[-1])}", (dates[-1], ys[-1]), xytext=(10, 0),
                    textcoords="offset points", va="center", fontsize=10, annotation_clip=False)
    ax.yaxis.set_major_formatter(s.HUMAN)
    ax.set_ylim(0, max(thm) * 1.05)
    ax.set_ylabel("Declarations")
    ax.legend(loc="upper left")
    s.clean_axes(ax)
    ratio = [c / t if t else np.nan for c, t in zip(code, thm)]
    ax2.plot(dates, ratio, color=T.series[0])
    ax2.set_ylabel("Code lines\nper theorem")
    ax2.set_ylim(0, np.nanmax(ratio) * 1.2)
    ax2.annotate(f"{ratio[-1]:.1f}", (dates[-1], ratio[-1]), xytext=(10, 0),
                 textcoords="offset points", va="center", fontsize=10, annotation_clip=False)
    s.clean_axes(ax2)
    _date_axis(ax2)
    ax2.set_xlim(dates[0], dates[-1])
    s.titles(fig, ax, "Declarations over time",
             "Top-level theorem/lemma, def/abbrev and structure/inductive/class/instance headers in "
             "CslibFrontier/ · counted from source text")
    csv = s.write_csv(out, "declarations",
                      ["date", "theorems", "definitions", "types_and_instances", "code_lines"],
                      [[d.isoformat(), a, b, c, e] for d, a, b, c, e
                       in zip(dates, thm, dfn, other, code)])
    return s.save(fig, out, "declarations") + [csv]


def churn(H: h.History, out):
    """Is a given day growth, or rework?"""
    log = subprocess.run(
        ["git", "-C", str(H.repo), "log", "--first-parent", "--diff-merges=first-parent",
         "--no-renames", "--numstat", "--format=C %ct", "--", "*.lean"],
        check=True, capture_output=True, text=True).stdout
    add, rem = defaultdict(int), defaultdict(int)
    import datetime as dt

    def flush(day, per_path):
        # A file moved by the rename shows up under both spellings; net the pair so a pure move
        # counts as no change.
        for rows in per_path.values():
            a, r = sum(x for x, _ in rows), sum(y for _, y in rows)
            if len(rows) > 1:
                a, r = max(0, a - r), max(0, r - a)
            add[day] += a
            rem[day] += r

    day, per_path = None, {}
    for line in log.splitlines():
        if line.startswith("C "):
            if day is not None:
                flush(day, per_path)
            day = dt.datetime.fromtimestamp(int(line[2:]), dt.timezone.utc).date()
            per_path = {}
        elif line and line[0].isdigit():
            a, r, p = line.split("\t", 2)
            q = h.normalize_path(p)
            if h.is_library(q):
                per_path.setdefault(q, []).append((int(a), int(r)))
    if day is not None:
        flush(day, per_path)
    days = sorted(add)
    A = np.array([add[d] for d in days])
    R = np.array([rem[d] for d in days])
    T = s.theme()
    fig, ax = plt.subplots(figsize=(12, 6))
    fig.subplots_adjust(left=0.08, right=0.97, top=0.86, bottom=0.08)
    ax.bar(days, A, width=0.8, color=T.series[0], label="Lines added")
    ax.bar(days, -R, width=0.8, color=T.series[1], label="Lines removed")
    ax.axhline(0, color=T.axis, linewidth=1)
    ax.yaxis.set_major_formatter(s.FuncFormatter(lambda v, _: s.human(abs(v))))
    ax.set_ylabel("Lines changed per day (library)")
    big = np.argsort(R)[-3:]
    for i in big:
        ax.annotate(f"−{s.human(R[i])}", (days[i], -R[i]), xytext=(0, -12),
                    textcoords="offset points", ha="center", fontsize=9, color=T.ink2)
    ax.legend(loc="upper left")
    _date_axis(ax)
    s.clean_axes(ax)
    rework = R.sum() / A.sum()
    s.titles(fig, ax, "Daily churn",
             f"Lines added and removed in CslibFrontier/ per UTC day · {rework * 100:.0f} lines "
             "removed for every 100 added · files moved by the rename of Complexity to CslibFrontier "
             "count only their edits")
    csv = s.write_csv(out, "churn", ["date", "lines_added", "lines_removed"],
                      [[d.isoformat(), int(a), int(r)] for d, a, r in zip(days, A, R)])
    return s.save(fig, out, "churn") + [csv]


def import_depth(H: h.History, out):
    """How deep is the import DAG — the floor on any parallel build's critical path?"""
    snaps = H.daily()
    dates, depth, mods = [], [], []
    for d, _, tree in snaps:
        g = h.import_graph(H.blobs, tree)
        n, chain = h.longest_chain(g)
        dates.append(d)
        depth.append(n)
        mods.append(len(g))
    head = snaps[-1][2]
    g = h.import_graph(H.blobs, head)
    n, chain = h.longest_chain(g)
    T = s.theme()
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(13, 6), width_ratios=[1.4, 1])
    fig.subplots_adjust(left=0.06, right=0.98, top=0.82, bottom=0.12, wspace=0.18)
    ax.plot(dates, depth, color=T.series[0])
    ax.plot(dates[-1], depth[-1], "o", ms=8, color=T.series[0], mec=T.surface, mew=2)
    ax.annotate(f"{depth[-1]} modules", (dates[-1], depth[-1]), xytext=(-8, 10),
                textcoords="offset points", ha="right", fontsize=10)
    ax.set_ylim(0, max(depth) * 1.15)
    ax.set_title("Longest import chain over time", loc="left", fontsize=11.5)
    ax.set_ylabel("Modules on the longest chain")
    _date_axis(ax)
    s.clean_axes(ax)
    vals = np.array(list(h.depths(g).values()))
    ax2.hist(vals, bins=np.arange(0.5, vals.max() + 1.5), color=T.series[0],
             edgecolor=T.surface, linewidth=0.6)
    ax2.set_title("Depth of each module today", loc="left", fontsize=11.5)
    ax2.set_xlabel("Longest import chain beneath the module")
    ax2.set_ylabel("Modules")
    s.clean_axes(ax2)
    short = [m.removeprefix("CslibFrontier.") for m in (chain[0], chain[len(chain) // 2], chain[-1])]
    s.titles(fig, ax, "Import depth",
             f"A build can never be shorter than its longest import chain · today: {n} modules, "
             f"from {short[0]}\nthrough {short[1]} down to {short[2]}")
    csv = s.write_csv(out, "import-depth", ["date", "longest_chain_modules", "modules"],
                      [[d.isoformat(), n, m] for d, n, m in zip(dates, depth, mods)])
    return s.save(fig, out, "import-depth") + [csv]
