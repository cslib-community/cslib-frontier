# Codebase views

The nightly **API documentation** workflow builds these views from the same checkout of `main`
as the API docs and publishes them at <https://www.cslib.io/cslib-frontier/viz/>, so the two
always describe the same commit; every page names it. Nothing generated is committed. The
[Codebase visualizations](../../.github/workflows/viz.yml) workflow tests pull requests that
change this directory and uploads the built site as an artifact.

## Pages

| Page | What it is for |
|---|---|
| `index.html` | **Briefing.** Headline numbers with 24-hour and 7-day changes and daily trend lines; what changed (largest changes, new modules, growth by area, the Lean census night over night); interactive growth by area; and the chart gallery |
| `modules.html` | **Module explorer.** Search and filter all library modules; each has its size, declarations, imports and importers, how much rebuilds when it changes, depth, change history, results resting on it, unused definitions, and links to its API page and source |
| `results.html` | **Result explorer.** Every registered result: sources, theorems linked to their API entries, the library it rests on by area and module, and the audit rows citing it |
| `textbooks.html` | **Textbook map.** The audits' dispositions by chapter; click through to each audited result, its audit row and the registered results that formalize it |
| `areas.html` | **Areas.** One card per area: growth, size, declarations, results, unused definitions, and its most rebuilt and most changed modules |

Pages embed their data and need no remote scripts, so they also work opened from disk. They
follow the reader's light or dark preference (with a toggle), keep their state in the URL so a
selection can be linked, and work at phone width. Every chart in the gallery has a dark version
and a CSV of the data behind it.

## Charts

| View | Question it answers |
|---|---|
| `evolution` | How did the import graph grow, day by day? (MP4) |
| `growth-by-area` | Which areas drove the growth? |
| `declarations` | How many theorems and definitions exist, and how much code each costs |
| `lean-declarations` | What the library declares, exactly, by area and kind (Lean census) |
| `textbook-coverage` | How much of Arora–Barak and Goldreich the audits under `results/` record as covered |
| `churn` | Was a given day growth or rework? |
| `treemap` | Where is the code, and which parts change most? |
| `hotspots` | Which large modules keep changing? |
| `import-graph` | The whole module import graph today (4K poster) |
| `import-matrix` | Which sub-areas import which? |
| `change-coupling` | Which sub-areas change in the same commits? |
| `hubs` | How much of the library rebuilds when a module changes? |
| `result-cones` | What each registered result depends on inside the library (Lean census) |
| `load-bearing` | Which declarations the most others mention (Lean census) |
| `unused-definitions` | Which definitions nothing in the library mentions, with a CSV (Lean census) |
| `import-depth` | How long is the longest import chain, the floor on build time? |
| `cadence` | When does work land on `main`? |

## Building locally

Needs Python 3.11+, full Git history, Graphviz (`sfdp`) and `ffmpeg`, plus the pinned packages:

```sh
python3 -m venv /tmp/viz-venv && /tmp/viz-venv/bin/pip install -r tools/viz/requirements.txt
/tmp/viz-venv/bin/python -m unittest discover -s tools/viz -p 'test_*.py'
/tmp/viz-venv/bin/python tools/viz/build.py              # everything, about 3 minutes cold
/tmp/viz-venv/bin/python tools/viz/build.py --only treemap hubs --no-video
# With the Lean census, from a checkout whose library is built at the same commit:
/tmp/viz-venv/bin/python tools/viz/build.py --lean-lib .lake/build/lib/lean
# When working on pages, reuse the census an earlier run wrote instead of recomputing it:
/tmp/viz-venv/bin/python tools/viz/build.py --only cadence --lean-census tools/viz/_site/lean-census.json
```

Without `--lean-lib` the census views are skipped; the pull-request workflow builds no Lean, so
it checks everything else.

Output goes to `tools/viz/_site/`: the pages, and per chart a PNG, a dark PNG, an SVG and a CSV
(the video is an MP4). Serve the directory or open `index.html` directly.

## What is counted

`history.py` replays first-parent history of `main` (merges count when they reach it). For each
commit touching a `.lean` file it records the new blob of each changed file; every blob is read
once with `git cat-file` and reduced to line counts, imports and declaration counts, cached in
`.cache/` by blob SHA. Paths and module names from before the `Complexity` → `CslibFrontier`
rename are rewritten to the current spelling, so a module keeps one identity across it.

These are **source-text** measures, chosen because they can be computed for every past commit
without elaborating it:

* *Lines of code* are non-blank lines outside comments; docstrings count as comments.
* *Declarations* are unindented `theorem`, `lemma`, `def`, `abbrev`, `instance`, `structure`,
  `inductive` and `class` headers, optionally after an attribute and modifiers. Declarations that
  commands or macros generate (`enc_structure`, `deriving`, structure projections) are not seen.
* *Imports* are the module header's `import` lines; the graphs use only imports between library
  modules, and leave out `CslibFrontier.Init`, which every module imports.

## The Lean census

`LeanDecls.lean` reads the built `.olean` files of every library module without importing them
(as `scripts/ParallelDefs.lean` does), and the constant and import headers of every module they
depend on. It reports each module's declarations by kind, which modules' constants its
declarations mention (so an import counts as used through Mathlib too), how many written
declarations mention each declaration, the definitions nothing mentions, and the dependency cone
of each result in the registry (`scripts/results_registry.py`). `lean_census.py` compiles it with
the workspace's own `lean` and `leanc`, cached by source hash; the interpreter behind
`lean --run` is far too slow for the cones. It counts what elaboration produced, so declarations
generated by commands and macros are included, prose that looks like a header is not, and new
surface syntax needs no change here. It runs in the nightly docs job, after the library build.

A past commit cannot be counted this way without building it, so the census keeps its own
series: each run fetches the previously published `lean-history.json`, adds the current commit
(one entry per UTC day) and publishes the result, failing rather than publishing a truncated
series if the fetch fails for any reason but a 404. The history views above stay on source text
because they must cover every past commit.

The `tools/stats` dashboard is the reference for exact line counts over time (Tokei, code,
comments and blanks); these views trade some exactness for structure.

The census also checks imports: one is unused when no declaration of the importing module
mentions a constant defined in it or in anything it imports, Mathlib included. Umbrella modules,
which declare nothing and import to re-export, are skipped. The count heads the report page
rather than getting a chart, since it is zero today; notation, attributes and tactics leave no
constants behind, so a nonzero count lists candidates, not certainties.

## How it fits together

* `history.py` replays git history; `audits.py` reads the textbook audits; `lean_census.py` and
  `LeanDecls.lean` read the built library.
* `plots_*.py` and `evolution.py` draw the charts with Matplotlib and Pillow; `style.py` holds the
  palette, the light and dark themes and the CSV writer.
* `site_data.py` computes the pages' data; `pages.py` writes the pages from `site/` (one stylesheet,
  one shared script with the tooltip, trend line and stacked-area chart, and one script per page).

## Adding a view

For a chart, write a function `(history: History, out: Path) -> list[Path]` that draws with
`style.theme()` and saves through `style.save` and `style.write_csv`; `build.py` calls it once per
theme. Add a `Chart` entry with the question it answers and how to read it, list it in the table
above, and test any new data logic in `test_viz.py`. For a page, add its data to `site_data.py`, its
body to `pages.py` and its script to `site/`. Use `style.py` for colours: areas take
fixed palette slots (identity, never rank), at most eight including "Other", and a chart in which
every pair of colours can meet labels its areas directly.
