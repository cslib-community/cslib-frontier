/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Algorithms.Lean.CDCL.Watched
import CslibFrontier.Logics.Propositional.Pigeonhole

/-!
# Benchmarks of the CDCL solver

Runs the CDCL solver with its default options, with each heuristic turned off in turn (VSIDS,
phase saving, restarts, minimization and reduction of the learned clauses), with geometric instead
of Luby restarts, and with every option off (`none`; the deletion of learned clauses satisfied at
the root still runs), on pigeonhole formulas, seeded random 3-SAT at the
threshold ratio 4.26, and the `n`-queens problem. For each run it prints the answer, the conflicts,
decisions, propagations (literals taken from the propagation queue, as MiniSat counts them) and
restarts, the literals of the learned clauses, the learned clauses forgotten, the time to solve
(`solve_ms`), and separately the time to check the answer (`check_ms`). It checks every answer: a
model must satisfy the formula, a certificate must be accepted by the verified LRAT checker, and
every configuration must agree.

Conflicts and decisions measure the heuristics independently of the machine; times are those of
Lean's interpreter, so they compare runs with each other only.

Run it with

```
lake env lean --run scripts/CdclBench.lean [quick]
```
-/

open Cslib.Logic.PL Cslib.Algorithms.Lean Cslib.Algorithms.Lean.CDCL

namespace CdclBench

/-- The pigeonhole formula PHP(n + 1, n), with pigeon `i` in hole `j` as `n * i + j`. -/
def php (n : ℕ) : CNF ℕ := (CNF.pigeonhole (n + 1) n).relabel fun x => n * x.1.val + x.2.val

/-- A step of a 64-bit linear congruential generator (Knuth's MMIX constants). -/
def lcg (x : ℕ) : ℕ := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A random 3-CNF with `n` variables and `m` clauses of three distinct variables, from `seed`. -/
def random3 (n m seed : ℕ) : CNF ℕ := Id.run do
  let mut x := lcg (seed + 1)
  let mut φ : CNF ℕ := []
  for _ in [0:m] do
    let mut c : Clause ℕ := []
    while c.length < 3 do
      x := lcg x
      let v := (x >>> 33) % n
      x := lcg x
      if !(c.any (·.1 == v)) then c := (v, (x >>> 40) % 2 == 0) :: c
    φ := c :: φ
  return φ

/-- The `n`-queens problem, with a queen on row `r` and column `c` as `n * r + c`. -/
def queens (n : ℕ) : CNF ℕ := Id.run do
  let q (r c : ℕ) : Literal ℕ := (n * r + c, true)
  let nq (r c : ℕ) : Literal ℕ := (n * r + c, false)
  let mut φ : CNF ℕ := []
  for r in [0:n] do
    φ := ((List.range n).map (q r)) :: φ
  for r₁ in [0:n] do
    for c₁ in [0:n] do
      for r₂ in [0:n] do
        for c₂ in [0:n] do
          if n * r₁ + c₁ < n * r₂ + c₂ &&
              (r₁ == r₂ || c₁ == c₂ || r₁ + c₂ == r₂ + c₁ || r₁ + c₁ == r₂ + c₂) then
            φ := [nq r₁ c₁, nq r₂ c₂] :: φ
  return φ

/-- The default options, each heuristic off in turn, basic minimization, and all heuristics off. -/
def configs : List (String × Options) :=
  [("default", {}), ("no-vsids", { vsids := false }), ("no-phase", { phaseSaving := false }),
    ("no-restarts", { restarts := false }), ("geometric", { luby := false, restartInc := 2 }),
    ("no-minimize", { ccminMode := .none }), ("ccmin-1", { ccminMode := .basic }),
    ("no-reduce", { reduce := false }), ("keep-input", { removeSatisfied := false }),
    ("none",
      { vsids := false, phaseSaving := false, restarts := false, ccminMode := .none
        reduce := false, removeSatisfied := false })]

/-- Runs every configuration on `φ`, checks the answers, and prints a line for each. -/
def bench (name : String) (φ : CNF ℕ) : IO Unit := do
  let mut answers : List Bool := []
  for (cname, o) in configs do
    let t₀ ← IO.monoMsNow
    let (r, s) ← (pure (solveWith o φ) : IO _)
    -- Read the answer before stopping the clock, so the solve is not deferred past it.
    let isSat := r.isSat
    let t₁ ← IO.monoMsNow
    let ok := match r with
      | .sat σ => φ.eval σ
      | .unsat cert => φ.checkLRAT cert
    let t₂ ← IO.monoMsNow
    unless ok do throw <| IO.userError s!"{name} {cname}: answer rejected"
    answers := isSat :: answers
    IO.println s!"{name},{cname},{if isSat then "SAT" else "UNSAT"},{s.conflicts},\
      {s.decisions},{s.propagations},{s.restarts},{s.literals},{s.removed},{s.simplified},\
      {t₁ - t₀},{t₂ - t₁}"
    (← IO.getStdout).flush
  unless answers.all (· == answers.head!) do
    throw <| IO.userError s!"{name}: the configurations disagree"

end CdclBench

open CdclBench in
def main (args : List String) : IO Unit := do
  let quick := args.contains "quick"
  IO.println <| "instance,options,answer,conflicts,decisions,propagations,restarts,literals," ++
    "removed,simplified,solve_ms,check_ms"
  -- PHP(7, 6) takes over an hour in the interpreter.
  for n in [4, 5] do
    bench s!"php-{n + 1}-{n}" (php n)
  for n in (if quick then [30] else [40, 50]) do
    for seed in [0:(if quick then 2 else 5)] do
      bench s!"rand3-{n}-{seed}" (random3 n (n * 426 / 100) seed)
  for n in (if quick then [6] else [8]) do
    bench s!"queens-{n}" (queens n)
