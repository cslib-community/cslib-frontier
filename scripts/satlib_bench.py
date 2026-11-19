#!/usr/bin/env python3
"""Benchmark the verified CDCL solver against MiniSat on SATLIB random 3-SAT.

Runs `lake exe cdcl` (build it first with `lake build cdcl`) and MiniSat on the SATLIB `uf`
(satisfiable) and `uuf` (unsatisfiable) uniform random 3-SAT families at the threshold ratio,
downloading them from SATLIB if needed. Every answer is checked independently of both solvers:
a model of `cdcl`, here in Python, for its final `0`, the header's bounds, consistency (no variable
with both signs) and every clause of the file, and a certificate of `cdcl` with an external LRAT
checker (`lrat-check` of drat-trim) when one is given. The run fails (exit code `1`) if either
solver answers wrongly or exits other than with an answer, if a model or certificate is not
accepted, or if a family has no instances; a timeout is reported, not a failure. Both solvers read the same
files, with the SATLIB trailer (a line `%` and a line `0`, which MiniSat rejects) removed.

Prints a CSV row per run and, at the end, a Markdown table per family: instances solved within the
timeout, median and total wall time, and median conflicts. Times are wall-clock times of the whole
process, parsing included; the CSV also has the time `cdcl` reports for solving alone, without the
startup of the Lean runtime (about 40 ms) and the parsing.

Example, with MiniSat and drat-trim from nixpkgs:

    nix-build '<nixpkgs>' -A minisat -o /tmp/minisat
    nix-build '<nixpkgs>' -A drat-trim -o /tmp/drat-trim
    lake build cdcl
    python3 scripts/satlib_bench.py --minisat /tmp/minisat/bin/minisat_core \\
        --lrat-check /tmp/drat-trim/bin/lrat-check --per-family 100 --timeout 60
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import io
import os
import re
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path

SATLIB = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT"
FAMILIES = [
    "uf20-91", "uf50-218", "uuf50-218", "uf75-325", "uuf75-325", "uf100-430", "uuf100-430",
    "uf125-538", "uuf125-538", "uf150-645", "uuf150-645", "uf175-753", "uuf175-753",
    "uf200-860", "uuf200-860", "uf225-960", "uuf225-960", "uf250-1065", "uuf250-1065",
]


def fetch(cache: Path, family: str) -> list[Path]:
    """The instances of a family, downloaded and unpacked into `cache` if needed."""
    target = cache / family
    if not target.exists():
        url = f"{SATLIB}/{family}.tar.gz"
        print(f"downloading {url}", file=sys.stderr)
        data = urllib.request.urlopen(url, timeout=120).read()
        target.mkdir(parents=True)
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
            for member in tar.getmembers():
                if member.isfile() and member.name.endswith(".cnf"):
                    member.name = Path(member.name).name
                    tar.extract(member, target, filter="data")
    return sorted(target.rglob("*.cnf"))


def clean(src: Path, dst: Path) -> tuple[int, list[list[int]]]:
    """Copies `src` without the SATLIB trailer, and returns its number of variables (from the
    header) and its clauses."""
    lines, clauses, cur, nvars = [], [], [], None
    for line in src.read_text().splitlines():
        if line.strip().startswith("%"):
            break
        lines.append(line)
        if line.strip().startswith("p"):
            nvars = int(line.split()[2])
            continue
        if line.strip().startswith("c") or not line.strip():
            continue
        for tok in line.split():
            lit = int(tok)
            if lit == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(lit)
    if nvars is None or cur:
        raise ValueError(f"{src}: no header, or an unterminated clause")
    dst.write_text("\n".join(lines) + "\n")
    return nvars, clauses


@dataclass
class Run:
    answer: str = "TIMEOUT"
    ms: float = 0.0
    conflicts: int | None = None
    solve_ms: int | None = None
    model: list[int] = field(default_factory=list)


def run(cmd: list[str], timeout: float) -> tuple[Run, str]:
    start = time.monotonic()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return Run(ms=timeout * 1000), ""
    r = Run(ms=(time.monotonic() - start) * 1000)
    out = p.stdout + p.stderr
    if p.returncode == 10:
        r.answer = "SAT"
    elif p.returncode == 20:
        r.answer = "UNSAT"
    else:
        r.answer = f"ERROR({p.returncode})"
    return r, out


def run_cdcl(cdcl: str, cnf: Path, proof: Path | None, timeout: float) -> Run:
    r, out = run([cdcl, str(cnf)] + ([str(proof)] if proof else []), timeout)
    if m := re.search(r"c conflicts (\d+)", out):
        r.conflicts = int(m.group(1))
    if m := re.search(r"c solve time (\d+) ms", out):
        r.solve_ms = int(m.group(1))
    r.model = [int(t) for line in out.splitlines() if line.startswith("v ")
               for t in line.split()[1:]]
    return r


def run_minisat(minisat: str, cnf: Path, timeout: float) -> Run:
    r, out = run([minisat, "-verb=1", str(cnf)], timeout)
    if m := re.search(r"conflicts\s*:\s*(\d+)", out):
        r.conflicts = int(m.group(1))
    return r


def satisfies(model: list[int], nvars: int, clauses: list[list[int]]) -> bool:
    """Whether the `v` literals `model` are a model: ended by a single `0`, every other literal
    within the header's `nvars` variables, no variable with both signs, and every clause with a
    literal of the model."""
    if not model or model[-1] != 0:
        return False
    lits = model[:-1]
    if any(lit == 0 or abs(lit) > nvars for lit in lits):
        return False
    true = set(lits)
    if any(-lit in true for lit in true):
        return False
    return all(any(lit in true for lit in c) for c in clauses)


def lrat_ok(lrat_check: str, cnf: Path, proof: Path, timeout: float) -> bool:
    try:
        p = subprocess.run([lrat_check, str(cnf), str(proof)], capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return False
    return re.search(r"^c VERIFIED", p.stdout + p.stderr, re.M) is not None


def bench_one(args, family: str, src: Path, work: Path) -> dict:
    cnf = work / f"{family}-{src.name}"
    nvars, clauses = clean(src, cnf)
    expected = "UNSAT" if family.startswith("uuf") else "SAT"
    proof = work / f"{cnf.name}.lrat" if args.lrat_check else None
    c = run_cdcl(args.cdcl, cnf, proof, args.timeout)
    m = run_minisat(args.minisat, cnf, args.timeout)
    checked = ""
    if c.answer == "SAT":
        checked = "model ok" if satisfies(c.model, nvars, clauses) else "MODEL WRONG"
    elif c.answer == "UNSAT" and proof is not None:
        checked = "lrat ok" if lrat_ok(args.lrat_check, cnf, proof, 10 * args.timeout) \
            else "LRAT REJECTED"
    for f in (cnf, proof):
        if f is not None and f.exists():
            f.unlink()
    return {"family": family, "instance": src.name, "expected": expected,
            "cdcl": c.answer, "cdcl_ms": round(c.ms), "cdcl_solve_ms": c.solve_ms,
            "cdcl_conflicts": c.conflicts,
            "checked": checked, "minisat": m.answer, "minisat_ms": round(m.ms),
            "minisat_conflicts": m.conflicts}


def summary(rows: list[dict], timeout: float) -> str:
    out = ["| family | instances | cdcl solved | MiniSat solved | cdcl median | MiniSat median "
           "| cdcl total | MiniSat total | cdcl / MiniSat (median) | median conflicts, cdcl "
           "| median conflicts, MiniSat |",
           "|" + "---|" * 11]
    for fam in dict.fromkeys(r["family"] for r in rows):
        rs = [r for r in rows if r["family"] == fam]
        solved = lambda k: [r for r in rs if r[k] in ("SAT", "UNSAT")]
        cm = statistics.median(r["cdcl_ms"] for r in rs)
        mm = statistics.median(r["minisat_ms"] for r in rs)
        cc = [r["cdcl_conflicts"] for r in solved("cdcl") if r["cdcl_conflicts"] is not None]
        mc = [r["minisat_conflicts"] for r in solved("minisat")
              if r["minisat_conflicts"] is not None]
        out.append(
            f"| {fam} | {len(rs)} | {len(solved('cdcl'))} | {len(solved('minisat'))} "
            f"| {cm / 1000:.3f} s | {mm / 1000:.3f} s "
            f"| {sum(r['cdcl_ms'] for r in rs) / 1000:.1f} s "
            f"| {sum(r['minisat_ms'] for r in rs) / 1000:.1f} s | {cm / max(mm, 1e-3):.0f}× "
            f"| {statistics.median(cc) if cc else '–'} | {statistics.median(mc) if mc else '–'} |")
    out.append(f"\nTimeout {timeout:g} s per run; a timeout counts as {timeout:g} s.")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--cdcl", default=".lake/build/bin/cdcl")
    ap.add_argument("--minisat", required=True, help="MiniSat binary, e.g. minisat_core")
    ap.add_argument("--lrat-check", help="drat-trim's lrat-check, to check the certificates")
    ap.add_argument("--cache", default=".lake/satlib", help="where SATLIB is downloaded")
    ap.add_argument("--families", nargs="*", default=FAMILIES)
    ap.add_argument("--per-family", type=int, default=100)
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 4))
    ap.add_argument("--csv", help="also write the rows here")
    args = ap.parse_args()
    cache = Path(args.cache)
    rows: list[dict] = []
    empty: list[str] = []
    writer = csv.DictWriter(sys.stdout, fieldnames=[
        "family", "instance", "expected", "cdcl", "cdcl_ms", "cdcl_solve_ms", "cdcl_conflicts",
        "checked",
        "minisat", "minisat_ms", "minisat_conflicts"])
    writer.writeheader()
    with tempfile.TemporaryDirectory() as tmp, \
            concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for fam in args.families:
            files = fetch(cache, fam)[:args.per_family]
            if not files:
                print(f"FAILED: no instances of {fam} in {cache / fam}", file=sys.stderr)
                empty.append(fam)
            for row in pool.map(lambda f: bench_one(args, fam, f, Path(tmp)), files):
                writer.writerow(row)
                sys.stdout.flush()
                rows.append(row)
    if args.csv:
        with open(args.csv, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=writer.fieldnames)
            w.writeheader()
            w.writerows(rows)
    print(summary(rows, args.timeout), file=sys.stderr)
    wrong = [r for r in rows if failed(r)]
    for r in wrong:
        print(f"FAILED: {r}", file=sys.stderr)
    return 1 if wrong or empty else 0


def failed(r: dict) -> bool:
    """Whether a row is a failure: a solver exiting other than with an answer or a timeout, or a
    wrong answer from either solver, or a model or certificate of `cdcl` not checked. A timeout is
    not a failure."""
    for k in ("cdcl", "minisat"):
        if r[k] != "TIMEOUT" and r[k] != r["expected"]:
            return True
    if r["cdcl"] == "SAT":
        return r["checked"] != "model ok"
    return "REJECTED" in r["checked"]


if __name__ == "__main__":
    sys.exit(main())
