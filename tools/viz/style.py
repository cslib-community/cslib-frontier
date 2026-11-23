# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Shared colours and Matplotlib styling for the codebase visualizations.

Colours are the validated reference palette of the data-viz guidelines this portfolio follows:
categorical slots are assigned to areas in the fixed order of `history.AREAS` (identity, never
rank), with "Other" in neutral grey. The eight slots pass the adjacent-pair colour-vision checks,
which covers stacked areas and bars. Forms where every pair of colours can meet (graphs,
scatters) do not pass with eight areas, so those plots also label each area directly.
"""

from __future__ import annotations

from dataclasses import dataclass

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.colors import LinearSegmentedColormap  # noqa: E402
from matplotlib.ticker import FuncFormatter  # noqa: E402

from history import AREAS, OTHER  # noqa: E402


@dataclass(frozen=True)
class Theme:
    name: str
    surface: str
    ink: str
    ink2: str
    muted: str
    grid: str
    axis: str
    series: tuple[str, ...]
    other: str
    sequential: tuple[str, ...]
    neutral: str  # a recessive fill for "absent" categories


_SEQ = ("#cde2fb", "#9ec5f4", "#6da7ec", "#3987e5", "#256abf", "#184f95", "#0d366b")

LIGHT = Theme("light", "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7",
              ("#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6",
               "#e34948"), "#a8a7a0", _SEQ, "#c3c2b7")
DARK = Theme("dark", "#1a1a19", "#f0efec", "#c3c2b7", "#898781", "#2c2c2a", "#383835",
             ("#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#0ca30c", "#9085e9",
              "#e66767"), "#6b6a64", tuple(reversed(_SEQ)), "#55544f")

ALL_AREAS = AREAS + [OTHER]

# The theme charts are drawn in; `setup` switches it. Charts read it through `theme()`, so each
# static chart is rendered once per theme and the page picks the one matching the reader's.
_current = LIGHT


def theme() -> Theme:
    return _current


def area_colors(t: Theme | None = None) -> dict[str, str]:
    t = t or _current
    colors = {a: t.series[i] for i, a in enumerate(AREAS)}
    colors[OTHER] = t.other
    return colors


def sequential_cmap(t: Theme | None = None) -> LinearSegmentedColormap:
    t = t or _current
    return LinearSegmentedColormap.from_list(f"seq-{t.name}", list(t.sequential))


def human(v: float, _pos=None) -> str:
    a = abs(v)

    def trim(x: str) -> str:
        return x.rstrip("0").rstrip(".") if "." in x else x

    if a >= 1e6:
        return trim(f"{v / 1e6:.2f}") + "M"
    if a >= 1e4:
        return f"{v / 1e3:.0f}K"
    if a >= 1e3:
        return trim(f"{v / 1e3:.1f}") + "K"
    return f"{v:.0f}"


HUMAN = FuncFormatter(human)


def setup(t: Theme = LIGHT) -> None:
    global _current
    _current = t
    theme = t
    plt.rcParams.update({
        # A list, so glyphs missing from the first face (⊄, →) fall back to DejaVu Sans.
        "font.family": ["Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"],
        "font.size": 11,
        "figure.facecolor": theme.surface,
        "axes.facecolor": theme.surface,
        "savefig.facecolor": theme.surface,
        "axes.edgecolor": theme.axis,
        "axes.labelcolor": theme.ink2,
        "axes.titlecolor": theme.ink,
        "text.color": theme.ink,
        "xtick.color": theme.ink2,
        "ytick.color": theme.ink2,
        "xtick.major.size": 0,
        "ytick.major.size": 0,
        "xtick.major.pad": 6,
        "ytick.major.pad": 6,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": False,
        "grid.color": theme.grid,
        "grid.linewidth": 1,
        "legend.frameon": False,
        "lines.linewidth": 2,
        "svg.fonttype": "none",
    })


def clean_axes(ax, theme: Theme | None = None, grid_axis: str = "y") -> None:
    theme = theme or _current
    for side in ("left",):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(theme.axis)
    if grid_axis:
        ax.grid(axis=grid_axis, color=theme.grid, linewidth=1)
    ax.set_axisbelow(True)


def titles(fig, ax, title: str, subtitle: str, theme: Theme | None = None) -> None:
    theme = theme or _current
    fig.suptitle(title, x=0.012, y=0.985, ha="left", va="top", fontsize=16, fontweight="bold",
                 color=theme.ink)
    fig.text(0.012, 0.935, subtitle, ha="left", va="top", fontsize=10.5, color=theme.ink2)


def save(fig, out, name: str) -> list:
    """Save the light PNG and SVG, or in the dark theme a `-dark` PNG alone."""
    out.mkdir(parents=True, exist_ok=True)
    paths = []
    exts = ("png",) if _current is DARK else ("png", "svg")
    suffix = "-dark" if _current is DARK else ""
    for ext in exts:
        p = out / f"{name}{suffix}.{ext}"
        fig.savefig(p, dpi=200 if ext == "png" else None)
        paths.append(p)
    plt.close(fig)
    return paths


def write_csv(out, name: str, header: list[str], rows) -> "Path":
    """The data behind a chart, so every value can be read without hovering or squinting."""
    import csv
    out.mkdir(parents=True, exist_ok=True)
    p = out / f"{name}.csv"
    if _current is DARK and p.exists():
        return p
    with open(p, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)
    return p
