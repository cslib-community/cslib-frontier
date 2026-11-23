# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Declaration census from the built library, and its nightly time series.

`LeanDecls.lean` reads the `.olean` files of a build of the commit being visualized and reports,
per module, its declarations by kind and the library modules its declarations mention. Because
it reads what elaboration produced, it is exact where the source-text scanner of `history.py`
can only approximate (declarations made by commands and macros, prose lines that look like
headers), and it needs no change when the surface syntax evolves.

A past commit cannot be counted this way without rebuilding it, so the census also keeps a
series: each run fetches the previously published `lean-history.json`, adds the current commit,
and publishes the result. The series is exact from its first nightly run onward.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import subprocess
import sys
import urllib.error
import urllib.request
from collections import Counter
from pathlib import Path

import history as h

HERE = Path(__file__).resolve().parent
KIND_GROUPS = {
    "theorem": "Theorems",
    "def": "Definitions",
    "abbrev": "Definitions",
    "opaque": "Definitions",
    "instance": "Instances",
    "structure": "Types",
    "class": "Types",
    "inductive": "Types",
    "axiom": "Axioms",
    "syntax": None,  # notation and tactic parsers are not counted as declarations
    "meta": None,  # nor are tactics, elaborators and extensions
}
GROUPS = ["Theorems", "Definitions", "Instances", "Types", "Axioms"]


_registry: list[dict] | None = None
_registry_ok: bool = False


def registered_results(repo: Path, *, require: bool = False) -> list[dict]:
    """The results registry (`scripts/results_registry.py --json`), or `[]` when it cannot be
    exported (unless `require` is set): the exporter needs a current build of
    `CslibFrontierResults`, which pull-request and local builds without Lean do not have.
    `registry_available` says which happened."""
    global _registry, _registry_ok
    if _registry is None:
        proc = subprocess.run(["python3", "-B", "scripts/results_registry.py", "--json"],
                              cwd=repo, capture_output=True, text=True)
        if proc.returncode:
            if require:
                raise SystemExit(
                    f"the results registry could not be exported:\n{proc.stderr or proc.stdout}")
            print("warning: the results registry could not be exported (build "
                  "CslibFrontierResults first); registry views are left empty", file=sys.stderr)
            _registry = []
            _registry_ok = False
        else:
            _registry = json.loads(proc.stdout)["results"]
            _registry_ok = True
    elif require and not _registry_ok:
        raise SystemExit("the results registry could not be exported")
    return _registry


def registry_available() -> bool:
    return _registry_ok


def compile_census(repo: Path, lake: str = "lake") -> Path:
    """Compile `LeanDecls.lean` with the workspace's toolchain, cached by source and toolchain.

    The interpreter behind `lean --run` is far too slow for the dependency cones."""
    prefix = subprocess.run([lake, "env", "lean", "--print-prefix"], cwd=repo, check=True,
                            capture_output=True, text=True).stdout.strip()
    src = HERE / "LeanDecls.lean"
    key = hashlib.sha256(src.read_bytes() + prefix.encode()).hexdigest()[:16]
    exe = HERE / ".cache" / "bin" / f"viz_census-{key}"
    if exe.exists():
        return exe
    exe.parent.mkdir(parents=True, exist_ok=True)
    c_file = exe.with_suffix(".c")
    subprocess.run([lake, "env", "lean", "-c", str(c_file), str(src)], cwd=repo, check=True)
    subprocess.run([str(Path(prefix) / "bin" / "leanc"), "-O2", "-o", str(exe), str(c_file)],
                   check=True)
    for old in exe.parent.glob("viz_census-*"):
        if old != exe:
            old.unlink(missing_ok=True)
    return exe


def run(repo: Path, lib_dir: Path, modules: list[str], results: list[dict],
        lake: str = "lake") -> dict:
    """Run the compiled census under `lake env` in `repo` and parse its report."""
    requests = list(modules) + [f"headline {r['id']} {' '.join(r['theorems'])}"
                                for r in results if r.get("theorems")]
    exe = compile_census(repo, lake)
    proc = subprocess.run(
        [lake, "env", str(exe), str(lib_dir)],
        input="\n".join(requests) + "\n", capture_output=True, text=True, cwd=repo)
    if proc.returncode:
        raise SystemExit(f"the Lean census failed:\n{proc.stderr or proc.stdout}")
    # `lean --run` may print elaboration messages before the report; the report is the last line.
    report = json.loads(proc.stdout.strip().splitlines()[-1])
    if report["missing"]:
        raise SystemExit(f"{len(report['missing'])} modules have no build outputs under {lib_dir} "
                         f"(first: {report['missing'][0]}); build the commit being visualized")
    return report


def summarize(report: dict) -> dict:
    """Totals by area and kind group, as stored in the series."""
    by_area: dict[str, Counter] = {}
    generated = 0
    for m, v in report["modules"].items():
        area = h.area_of(m.replace(".", "/") + ".lean")
        c = by_area.setdefault(area, Counter())
        for k, n in v["kinds"].items():
            group = KIND_GROUPS.get(k, "Definitions")
            if group:
                c[group] += n
        generated += v["generated"]
    return {"by_area": {a: dict(c) for a, c in sorted(by_area.items())}, "generated": generated,
            "modules": len(report["modules"])}


def load_previous(source: str | None) -> list[dict]:
    """The published series; empty when it does not exist yet (HTTP 404 or a missing file).

    Any other failure stops the build, so a transient error never publishes a truncated series."""
    if not source:
        return []
    if source.startswith(("http://", "https://")):
        try:
            with urllib.request.urlopen(source, timeout=30) as r:
                return json.load(r)["entries"]
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return []
            raise
    p = Path(source)
    return json.loads(p.read_text())["entries"] if p.exists() else []


def extend(entries: list[dict], commit: h.Commit, summary: dict) -> list[dict]:
    """Add this commit's census, replacing an entry for the same commit or UTC day."""
    day = commit.date.isoformat()
    kept = [e for e in entries if e["sha"] != commit.sha and e["date"] != day]
    kept.append({"date": day, "sha": commit.sha, "time": commit.time, **summary})
    kept.sort(key=lambda e: e["time"])
    return kept


def collect(H: h.History, lib_dir: Path, previous: str | None, out: Path, lake: str = "lake",
            require_registry: bool = False):
    """Run the census for the head of `H`, write the report and the extended series."""
    tree = H.head()
    modules = sorted(h.module_of(p) for p in tree if h.is_library(p))
    # Run Lake in the workspace that owns the build outputs, so its toolchain and packages apply.
    workspace = lib_dir.parents[3] if lib_dir.parts[-4:] == (".lake", "build", "lib", "lean") \
        else H.repo
    results = registered_results(H.repo, require=require_registry or bool(previous))
    report = run(workspace, lib_dir, modules, results, lake)
    report["results"] = {r["id"]: {k: r.get(k) for k in ("title", "topic", "module", "theorems")}
                         for r in results}
    summary = summarize(report)
    # Enough of tonight's state for tomorrow's briefing to say what changed.
    summary["results"] = sorted(r["id"] for r in results)
    import audits
    summary["audit"] = {book: {r.id: r.cls for r in rows}
                        for book, rows in audits.load(H.repo).items()}
    entries = extend(load_previous(previous), H.commits[-1], summary)
    out.mkdir(parents=True, exist_ok=True)
    (out / "lean-census.json").write_text(json.dumps(
        {"sha": H.commits[-1].sha, "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
         **report}, separators=(",", ":")))
    (out / "lean-history.json").write_text(json.dumps({"entries": entries}, indent=1))
    return report, entries
