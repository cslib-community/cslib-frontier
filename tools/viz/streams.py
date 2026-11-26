# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""The library's lifetime as a streamgraph: one stream per sub-area, every six hours."""

from __future__ import annotations

import colorsys
import datetime as dt
from collections import Counter
from pathlib import Path

import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import numpy as np
from scipy.ndimage import gaussian_filter1d

import history as h
import style as s

STEP = 6 * 3600


def _shade(hexcol, dl):
    r, g, b = (int(hexcol[i:i + 2], 16) / 255 for i in (1, 3, 5))
    hh, ll, ss = colorsys.rgb_to_hls(r, g, b)
    return colorsys.hls_to_rgb(hh, max(0.05, min(0.92, ll + dl)), ss)


def series(H: h.History):
    """Library code per sub-area at every STEP, from the replayed history."""
    if not H.commits:
        return [], []
    t0, t1 = H.commits[0].time, H.commits[-1].time
    start = t0 - t0 % STEP + STEP
    times = list(range(start, max(t1 + STEP, start + 1), STEP))
    code: dict[str, int] = {}  # path -> code lines
    sub_total: Counter = Counter()
    rows = []
    ci = 0
    for t in times:
        while ci < len(H.commits) and H.commits[ci].time <= t:
            for p, b in H.commits[ci].changes:
                if not h.is_library(p):
                    continue
                sb = h.subarea_of(p)
                sub_total[sb] -= code.pop(p, 0)
                if b:
                    code[p] = H.blobs[b].code
                    sub_total[sb] += code[p]
            ci += 1
        rows.append(dict(sub_total))
    return [dt.datetime.fromtimestamp(t, dt.timezone.utc) for t in times], rows


def streamgraph(H: h.History, out: Path, min_share=0.006, size=(19.2, 10.8)):
    """The library's lifetime, one stream per sub-area, every six hours."""
    T = s.theme()
    dates, rows = series(H)
    final = rows[-1] if rows else {}
    peak = Counter()
    for r in rows:
        for k, v in r.items():
            peak[k] = max(peak[k], v)
    total_final = sum(final.values())
    area_of = lambda sb: h.area_of("CslibFrontier/" + sb + "/x.lean")
    keep = {sb for sb, v in peak.items() if total_final > 0 and v >= min_share * total_final}
    # Streams: kept sub-areas, then the rest of each area folded into "<Area>, other".
    streams: dict[str, np.ndarray] = {}
    for a in s.ALL_AREAS:
        subs = sorted((sb for sb in peak if area_of(sb) == a and sb in keep),
                      key=lambda sb: -final.get(sb, 0))
        for sb in subs:
            streams[sb] = np.array([r.get(sb, 0) for r in rows], float)
        rest = [sb for sb in peak if area_of(sb) == a and sb not in keep]
        if rest:
            streams[f"{a}/…"] = np.array([sum(r.get(sb, 0) for sb in rest) for r in rows], float)
    names = list(streams)
    fig, ax = plt.subplots(figsize=size)
    fig.subplots_adjust(left=0.02, right=0.98, top=0.86, bottom=0.07)
    ax.yaxis.set_visible(False)
    for sp_ in ("left", "right", "top"):
        ax.spines[sp_].set_visible(False)
    ax.spines["bottom"].set_color(T.axis)
    if not dates or not names:
        ax.text(0.5, 0.5, "No library code history available", transform=ax.transAxes,
                ha="center", va="center", color=T.ink2)
        subtitle = (f"0 lines of library code from {dates[0]:%b %-d} to {dates[-1]:%b %-d, %Y}"
                    if dates else "No commits available")
        s.titles(fig, ax, "The library's lifetime, sub-area by sub-area", subtitle)
        csv = s.write_csv(out, "lifetime-streams", ["time"], [[d.isoformat()] for d in dates])
        return s.save(fig, out, "lifetime-streams") + [csv]
    Y = np.array([gaussian_filter1d(np.maximum(streams[n], 0), 1.2) for n in names])
    # Symmetric baseline (silhouette): the river is centred on zero.
    base = -Y.sum(axis=0) / 2
    lows = base + np.vstack([np.zeros(Y.shape[1]), np.cumsum(Y, axis=0)[:-1]])
    highs = lows + Y
    colors = s.area_colors(T)
    steps = [0.0, 0.09, -0.07, 0.16, -0.12, 0.05, -0.03, 0.12, -0.10, 0.20]
    rank = Counter()
    x = mdates.date2num(dates)
    for k, n in enumerate(names):
        a = n.split("/")[0] if n.endswith("/…") else area_of(n)
        col = _shade(colors[a], steps[rank[a] % len(steps)] - (0.05 if n.endswith("…") else 0))
        rank[a] += 1
        ax.fill_between(x, lows[k], highs[k], color=col, linewidth=0.6, edgecolor=T.surface)
    # Labels where each stream is thickest among the places the whole label fits, sized by
    # that thickness.
    yspan = float(highs.max() - lows.min())
    nbin = Y.shape[1]
    axes_w_in = size[0] * 0.96
    if yspan > 0:
        for k, n in enumerate(names):
            if n == f"{h.OTHER}/…":
                label = "Other areas"
            elif n.endswith("/…"):
                label = f"{n.split('/')[0]}, other"
            elif "/" in n:
                label = n.split("/", 1)[1]
            else:
                label = f"{n}, top level"
            th = Y[k] / yspan
            best = None
            for i in np.argsort(th)[::-1][:60]:
                thick = th[i]
                if thick < 0.012:
                    break
                fs = max(6.5, min(15, 380 * thick))
                half = int(np.ceil(len(label) * fs * 0.55 / 72 / axes_w_in * nbin / 2)) + 1
                if i - half < 0 or i + half >= nbin:
                    continue
                if th[i - half] < thick * 0.55 or th[i + half] < thick * 0.55:
                    continue  # the stream narrows under the label's ends
                best = (i, fs, thick)
                break
            if not best:
                continue
            i, fs, thick = best
            ax.text(x[i], (lows[k][i] + highs[k][i]) / 2, label, ha="center", va="center",
                    fontsize=fs, color="#ffffff",
                    fontweight="bold" if thick > 0.03 else "normal", clip_on=True)
    ax.set_xlim(x[0] - 0.125, x[0] + 0.125) if len(x) == 1 else ax.set_xlim(x[0], x[-1])
    if yspan > 0:
        ax.set_ylim(lows.min() * 1.04, highs.max() * 1.04)
    else:
        ax.set_ylim(-1, 1)
    ax.yaxis.set_visible(False)
    for sp_ in ("left", "right", "top"):
        ax.spines[sp_].set_visible(False)
    ax.spines["bottom"].set_color(T.axis)
    ax.xaxis.set_major_locator(mdates.WeekdayLocator(byweekday=mdates.MO))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
    # Scale bar instead of a y-axis: the river's height is the library's code.
    if total_final > 0:
        ref = 10 ** int(np.log10(total_final / 4))
        ref = ref * (5 if total_final / 4 >= 5 * ref else 2 if total_final / 4 >= 2 * ref else 1)
        xb = x[int(len(x) * 0.04)]
        ax.plot([xb, xb], [-ref / 2, ref / 2], color=T.ink2, linewidth=2, solid_capstyle="butt")
        ax.text(xb, ref / 2, f"  {s.human(ref)} lines of code", va="bottom", ha="left", fontsize=10,
                color=T.ink2)
    s.titles(fig, ax, "The library's lifetime, sub-area by sub-area",
             f"Lines of code (not comments or blank) in each sub-area of CslibFrontier/, every six "
             f"hours from {dates[0]:%b %-d} to {dates[-1]:%b %-d, %Y} · {len(names)} streams, "
             f"coloured by area; sub-areas below {min_share:.1%} of today's code are folded into "
             f"their area's \"other\"")
    csv = s.write_csv(out, "lifetime-streams", ["time"] + names,
                      [[d.isoformat()] + [int(streams[n][i]) for n in names]
                       for i, d in enumerate(dates)])
    return s.save(fig, out, "lifetime-streams") + [csv]
