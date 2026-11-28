# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Textbook coverage: the Arora–Barak and Goldreich audits, now and over their git history."""

from __future__ import annotations

import datetime as dt
import subprocess
from collections import Counter

import matplotlib.dates as mdates
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
import numpy as np

import audits
import history as h
import style as s

BOOKS = [(path, title) for _, path, title in audits.BOOKS]
CLASSES = audits.CLASSES
classify = audits.classify


def parse(text: str) -> list[tuple[int, str]]:
    """(chapter, class) for every audited result; a result recorded twice keeps its last row."""
    return [(r.chapter, r.cls) for r in audits.parse(text)]


def _revisions(repo, path):
    out = subprocess.run(["git", "-C", str(repo), "log", "--first-parent", "--reverse",
                          "--format=%H %ct", "--", path], capture_output=True, text=True,
                         check=True).stdout.split("\n")
    return [(sha, int(ct)) for sha, ct in (l.split() for l in out if l)]


def _show(repo, sha, path) -> str:
    return subprocess.run(["git", "-C", str(repo), "show", f"{sha}:{path}"], capture_output=True,
                          text=True).stdout


def coverage(H: h.History, out):
    """How much of each textbook's results does the library cover, and how fast is it growing?"""
    T = s.theme()
    colors = {c: (T.other if c == "Other" else T.series[i]) for i, c in enumerate(CLASSES)}
    colors["Not located"] = T.neutral  # absence reads as neutral, not as a hue
    fig = plt.figure(figsize=(14, 10.5))
    axes = []
    table = []
    for b, (path, title) in enumerate(BOOKS):
        rows = parse((H.repo / path).read_text())
        for (ch, cl), n in sorted(Counter(rows).items()):
            table.append((title, ch, cl, n))
        chapters = sorted({c for c, _ in rows})
        ax = fig.add_axes([0.06 + b * 0.49, 0.47, 0.42, 0.38])
        axes.append(ax)
        x = np.arange(len(chapters))
        bottom = np.zeros(len(chapters))
        for cl in CLASSES:
            vals = np.array([sum(1 for c, k in rows if c == ch and k == cl) for ch in chapters])
            if vals.sum():
                ax.bar(x, vals, bottom=bottom, width=0.72, color=colors[cl], label=cl,
                       edgecolor=T.surface, linewidth=1)
            bottom += vals
        ax.set_xticks(x, [str(c) for c in chapters], fontsize=9)
        ax.set_xlabel("Chapter")
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))
        ax.set_ylabel("Audited results")
        done = sum(1 for _, k in rows if k.startswith("Covered"))
        ax.set_title(f"{title}: {done} of {len(rows)} audited results covered", loc="left",
                     fontsize=11.5)
        s.clean_axes(ax)
        # Over time: covered results per revision of the audit.
        ax2 = fig.add_axes([0.06 + b * 0.49, 0.07, 0.42, 0.27])
        dates, stacks = [], {cl: [] for cl in CLASSES}
        for sha, ct in _revisions(H.repo, path):
            got = Counter(k for _, k in parse(_show(H.repo, sha, path)))
            dates.append(dt.datetime.fromtimestamp(ct, dt.timezone.utc))
            for cl in CLASSES:
                stacks[cl].append(got[cl])
        if dates:
            dates.append(dt.datetime.fromtimestamp(H.commits[-1].time, dt.timezone.utc))
            for cl in CLASSES:
                stacks[cl].append(stacks[cl][-1])
            ys = [stacks[cl] for cl in CLASSES]
            ax2.stackplot(dates, ys, colors=[colors[cl] for cl in CLASSES], step="post",
                          edgecolor=T.surface, linewidth=0.5)
            ax2.xaxis.set_major_locator(mdates.DayLocator(interval=2))
            ax2.xaxis.set_major_formatter(mdates.DateFormatter("%b %-d"))
            ax2.set_xlim(dates[0], dates[-1])
        ax2.set_title("Audited results over time", loc="left", fontsize=11)
        s.clean_axes(ax2)
    handles, labels = [], []
    for ax in axes:
        for hd, lb in zip(*ax.get_legend_handles_labels()):
            if lb not in labels:
                handles.append(hd)
                labels.append(lb)
    order = sorted(range(len(labels)), key=lambda i: CLASSES.index(labels[i]))
    fig.legend([handles[i] for i in order], [labels[i] for i in order], loc="upper left",
               bbox_to_anchor=(0.06, 0.915), ncols=len(labels), frameon=False)
    fig.suptitle("Textbook coverage", x=0.012, y=0.985, ha="left", va="top", fontsize=16,
                 fontweight="bold")
    fig.text(0.012, 0.955, "Dispositions recorded in the source-pinned audits under results/, by "
             "chapter, and their history · an audit row is a numbered result of the draft; the "
             "audits do not claim book-wide coverage", fontsize=10.5, color=T.ink2, va="top")
    csv = s.write_csv(out, "textbook-coverage", ["book", "chapter", "disposition", "results"],
                      [[title, ch, cl, n] for title, ch, cl, n in table])
    return s.save(fig, out, "textbook-coverage") + [csv]
