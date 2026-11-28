# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Pull requests over the library's lifetime: metadata from GitHub, areas from git."""

from __future__ import annotations

import datetime as dt
import re
from collections import Counter

import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D

import history as h
import style as s

# Three kinds, so that every pair of colours stays distinguishable even in a scatter.
KINDS = ["New results", "Refactoring and performance", "Fixes, docs, tests and CI"]


def _num(t):
    """Matplotlib date numbers are days since the Unix epoch."""
    return np.asarray(t, dtype=float) / 86400.0


def kind(title: str) -> int:
    """0 for `feat`, 1 for `refactor` and `perf`, 2 for everything else (by title prefix)."""
    m = re.match(r"^\s*(\w+)", title or "")
    t = m.group(1).lower() if m else ""
    if t == "feat":
        return 0
    if t in ("refactor", "perf"):
        return 1
    return 2


def _t(iso):
    return dt.datetime.fromisoformat(iso.replace("Z", "+00:00")).timestamp() if iso else None


def records(H: h.History, raw: list[dict]) -> list[dict]:
    """One record per pull request. A merged one is joined, by the `(#N)` in its squash commit's
    subject, to that commit on main, which gives the library areas with positive net code-line
    changes."""
    by_pr = {}
    tree: dict[str, str] = {}
    for c in H.commits:
        area, sub = Counter(), Counter()
        for p, b in c.changes:
            if h.is_library(p):
                old = H.blobs[tree[p]].code if p in tree else 0
                new = H.blobs[b].code if b else 0
                delta = abs(new - old)
                if delta:
                    area[h.area_of(p)] += delta
                    sub[h.subarea_of(p)] += delta
            if b is None:
                tree.pop(p, None)
            else:
                tree[p] = b
        if c.pr:
            by_pr[c.pr] = (area, sub)
    out = []
    for p in raw:
        area, sub = by_pr.get(p["number"], (Counter(), Counter()))
        out.append({
            "n": p["number"], "title": p["title"], "kind": kind(p["title"]), "state": p["state"],
            "created": _t(p["createdAt"]), "merged": _t(p["mergedAt"]),
            "closed": _t(p["closedAt"]), "author": (p.get("author") or {}).get("login", "ghost"),
            "add": p["additions"], "del": p["deletions"], "files": p["changedFiles"],
            "reviews": p["reviews"]["totalCount"], "commits": p["commits"]["totalCount"],
            "area": area.most_common(1)[0][0] if area else None,
            "sub": sub.most_common(1)[0][0] if sub else None,
        })
    return out


def wip(recs: list[dict], times: np.ndarray) -> np.ndarray:
    """How many pull requests were open at each of `times`."""
    live = [r for r in recs if r.get("created") is not None]
    if not live:
        return np.zeros(len(times), dtype=int)
    opened = np.searchsorted(np.sort([r["created"] for r in live]), times, side="right")
    ends = np.sort([r["merged"] or r["closed"] or np.inf for r in live])
    return opened - np.searchsorted(ends, times, side="right")


def waterfall(H: h.History, out, recs: list[dict]):
    """Every pull request as a line from opened to merged (or closed, or now)."""
    T = s.theme()
    now = H.commits[-1].time if H.commits else 0
    recs = sorted([r for r in recs if r["created"] and r["created"] <= now],
                  key=lambda r: r["created"])
    colors = [T.series[0], T.series[1], T.series[2]]
    fig = plt.figure(figsize=(19.2, 12))
    ax = fig.add_axes([0.05, 0.30, 0.93, 0.58])
    ax2 = fig.add_axes([0.05, 0.16, 0.93, 0.11], sharex=ax)
    ax3 = fig.add_axes([0.05, 0.05, 0.93, 0.09], sharex=ax)
    handles = [Line2D([], [], color=c, lw=3) for c in colors] + [
        Line2D([], [], color=T.neutral, lw=3), Line2D([], [], color=T.ink, lw=3)]
    ax.legend(handles, KINDS + ["Closed without merging", "Still open"], loc="lower left",
              ncols=5, fontsize=10)
    ax.set_ylabel("Pull requests, in order of opening")
    s.clean_axes(ax, grid_axis="x")
    ax.tick_params(labelbottom=False)
    ax2.set_ylabel("Open at once")
    s.clean_axes(ax2)
    ax2.tick_params(labelbottom=False)
    ax3.set_ylabel("Merged per hour")
    s.clean_axes(ax3)
    ax3.xaxis.set_major_locator(mdates.DayLocator(interval=2))
    ax3.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
    if not recs:
        t0 = now - 3600
        ax.set_xlim(_num(t0 - 6 * 3600), _num(now + 6 * 3600))
        ax.set_ylim(1, -1)
        ax.text(0.5, 0.5, "No pull requests in range", transform=ax.transAxes,
                ha="center", va="center", color=T.ink2)
        s.titles(fig, ax, "Every pull request, from opened to merged", "0 pull requests in range")
        csv = s.write_csv(out, "pr-waterfall",
                          ["number", "kind", "state", "opened", "merged", "closed", "lines_changed"],
                          [])
        return s.save(fig, out, "pr-waterfall") + [csv]
    segs, cols, widths = [], [], []
    for i, r in enumerate(recs):
        end = min(r["merged"] or r["closed"] or now, now)
        segs.append([(_num(r["created"]), i), (_num(end), i)])
        if r["merged"] and r["merged"] <= now:
            cols.append(colors[r["kind"]])
        elif r["state"] == "OPEN" or (r["merged"] or r["closed"] or now) > now:
            cols.append(T.ink)
        else:
            cols.append(T.neutral)
        widths.append(0.35 + 1.1 * min(1.0, np.log10(1 + r["add"] + r["del"]) / 5))
    ax.add_collection(LineCollection(segs, colors=cols, linewidths=widths, alpha=0.9))
    t0 = recs[0]["created"]
    ax.set_xlim(_num(t0 - 6 * 3600), _num(max(now, t0 + 1800.0) + 6 * 3600))
    ax.set_ylim(len(recs), -10)
    grid = np.arange(t0, max(now, t0 + 1800.0), 1800.0)
    w = wip(recs, grid)
    gx = _num(grid)
    ax2.fill_between(gx, 0, w, color=T.series[0], alpha=0.35, linewidth=0)
    ax2.plot(gx, w, color=T.series[0], linewidth=1.2)
    imax = int(np.argmax(w))
    ax2.annotate(f"peak {w[imax]} open", (gx[imax], w[imax]), xytext=(6, -2),
                 textcoords="offset points", fontsize=9, color=T.ink2, va="top")
    h0 = t0 - t0 % 3600
    hours = np.arange(h0, max(now + 3600, h0 + 7200), 3600)
    merged = [r for r in recs if r["merged"] and r["merged"] <= now]
    merged_t = [r["merged"] for r in merged]
    counts, _ = np.histogram(merged_t, bins=hours)
    ax3.bar(_num(hours[:-1]), counts, width=1 / 24, color=T.series[2], linewidth=0, align="edge")
    lat = np.array([(r["merged"] - r["created"]) / 3600 for r in merged])
    lat_note = (f"median time to merge {np.median(lat):.1f} h, 90% within {np.percentile(lat, 90):.0f} h"
                if len(lat) else "no merged pull requests")
    s.titles(fig, ax, "Every pull request, from opened to merged",
             f"{len(recs):,} pull requests since "
             f"{dt.datetime.fromtimestamp(t0, dt.timezone.utc):%b %-d} · each line runs from "
             f"opening to merge (or close); thicker lines changed more · {lat_note}")
    csv = s.write_csv(out, "pr-waterfall",
                      ["number", "kind", "state", "opened", "merged", "closed", "lines_changed"],
                      [[r["n"], KINDS[r["kind"]], r["state"], _iso(r["created"]), _iso(r["merged"]),
                        _iso(r["closed"]), r["add"] + r["del"]] for r in recs])
    return s.save(fig, out, "pr-waterfall") + [csv]


def _iso(t):
    return dt.datetime.fromtimestamp(t, dt.timezone.utc).isoformat() if t else ""


def growth_vs_cleanup(H: h.History, out, recs: list[dict]):
    """Per six hours: lines merged by new-result PRs above the axis, by refactoring and
    performance PRs below it, and the share of that work that was cleanup."""
    T = s.theme()
    now = H.commits[-1].time if H.commits else 0
    m = [r for r in recs if r["merged"] and r["merged"] <= now]
    if not m:
        fig = plt.figure(figsize=(19.2, 9))
        ax = fig.add_axes([0.06, 0.36, 0.92, 0.5])
        ax2 = fig.add_axes([0.06, 0.08, 0.92, 0.2], sharex=ax)
        ax.text(0.5, 0.5, "No merged pull requests yet", transform=ax.transAxes,
                ha="center", va="center", color=T.ink2)
        ax.set_ylabel("Lines changed per six hours")
        s.clean_axes(ax)
        ax.tick_params(labelbottom=False)
        ax2.set_ylim(0, 1)
        ax2.set_ylabel("Cleanup share\n(1-day average)")
        s.clean_axes(ax2)
        ax2.xaxis.set_major_locator(mdates.DayLocator(interval=2))
        ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
        ax.set_xlim(_num(now - 24 * 3600), _num(now + 3600))
        s.titles(fig, ax, "Growth and cleanup", "No merged pull requests yet")
        csv = s.write_csv(out, "pr-growth-vs-cleanup",
                          ["period_start", "new_result_lines", "cleanup_lines", "cleanup_share_1d"],
                          [])
        return s.save(fig, out, "pr-growth-vs-cleanup") + [csv]
    t0 = min(r["merged"] for r in m)
    t_max = max(r["merged"] for r in m)
    step = 6 * 3600
    t_start = t0 - t0 % step
    edges = np.arange(t_start, max(t_max + step, t_start + 2 * step), step)

    def hist(k):
        sel = [r for r in m if r["kind"] == k]
        return np.histogram([r["merged"] for r in sel], bins=edges,
                            weights=[r["add"] + r["del"] for r in sel])[0]

    grow, clean = hist(0), hist(1)
    x = _num(edges[:-1])
    fig = plt.figure(figsize=(19.2, 9))
    ax = fig.add_axes([0.06, 0.36, 0.92, 0.5])
    ax2 = fig.add_axes([0.06, 0.08, 0.92, 0.2], sharex=ax)
    ax.bar(x, grow, width=0.25 * 0.86, align="edge", color=T.series[0], linewidth=0,
           label="New results")
    ax.bar(x, -clean, width=0.25 * 0.86, align="edge", color=T.series[1], linewidth=0,
           label="Refactoring and performance")
    ax.axhline(0, color=T.axis, linewidth=1)
    ax.yaxis.set_major_formatter(s.FuncFormatter(lambda v, _: s.human(abs(v))))
    ax.set_ylabel("Lines changed per six hours")
    ax.legend(loc="upper left")
    s.clean_axes(ax)
    ax.tick_params(labelbottom=False)
    win = min(4, len(grow))
    k = np.ones(win) / win
    g = np.convolve(grow, k, "same")[:len(grow)]
    c = np.convolve(clean, k, "same")[:len(clean)]
    share = np.where(g + c > 0, c / np.maximum(g + c, 1), np.nan)
    ax2.fill_between(x, 0, share, color=T.series[1], alpha=0.35, linewidth=0, step="post")
    ax2.step(x, share, where="post", color=T.series[1], linewidth=1.4)
    ax2.set_ylim(0, 1)
    ax2.yaxis.set_major_formatter(s.FuncFormatter(lambda v, _: f"{v:.0%}"))
    ax2.set_ylabel("Cleanup share\n(1-day average)")
    s.clean_axes(ax2)
    ax2.xaxis.set_major_locator(mdates.DayLocator(interval=2))
    ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
    ax.set_xlim(x[0], x[-1] + 0.25)
    tot = max(1, grow.sum() + clean.sum())
    s.titles(fig, ax, "Growth and cleanup",
             f"Lines changed by merged pull requests, by kind: new results above the axis, "
             f"refactoring and performance below · cleanup is {clean.sum() / tot:.0%} of all "
             f"lines changed by these {sum(1 for r in m if r['kind'] < 2):,} pull requests")
    csv = s.write_csv(out, "pr-growth-vs-cleanup",
                      ["period_start", "new_result_lines", "cleanup_lines", "cleanup_share_1d"],
                      [[_iso(t), int(a), int(b), "" if np.isnan(v) else round(float(v), 4)]
                       for t, a, b, v in zip(edges[:-1], grow, clean, share)])
    return s.save(fig, out, "pr-growth-vs-cleanup") + [csv]
