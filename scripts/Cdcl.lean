/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Algorithms.Lean.CDCL.Dimacs
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

/-!
# The CDCL solver on DIMACS files

`lake exe cdcl [options] INPUT.cnf [PROOF.lrat]` reads a DIMACS CNF file, runs the verified CDCL
solver on the formula with its variables renamed to `0, …, k - 1`, and prints the answer of
`Cslib.Algorithms.Lean.CDCL.answerFor` in the format of the SAT competitions: `s SATISFIABLE` with
the model on `v` lines, one literal for each variable occurring in the formula, or
`s UNSATISFIABLE`, and the statistics on `c` lines. Like MiniSat, it exits with `10` on a
satisfiable formula and `20` on an unsatisfiable one. Given `PROOF.lrat`, it writes the LRAT
certificate there, with the input clauses numbered from `1` in file order, as external LRAT
checkers expect. With `--check`, it also checks the certificate with Lean core's checker
(`Std.Tactic.BVDecide.LRAT.check`).

The answer is correct by the solver's theorems: a model satisfies the formula read
(`Cslib.Algorithms.Lean.CDCL.solveCompactWith_sat`), and a certificate is accepted by the library's
LRAT checker (`Cslib.Algorithms.Lean.CDCL.solveCompactWith_unsat`). The DIMACS parser
(`Cslib.Logic.PL.CNF.ofDIMACS`) is not verified.

Options, as `Cslib.Algorithms.Lean.CDCL.Options`: `--no-vsids`, `--no-phase`, `--no-restarts`,
`--no-reduce`, `--ccmin=N` (MiniSat's `ccmin_mode`: `0`, `1` or `2`), `--keep-input` (MiniSat's
`remove_satisfied` off), and `--check`.
-/

open Cslib.Logic.PL Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- The options set by the command-line flags, and whether to check the certificate. -/
def parseFlags : List String → CDCL.Options × Bool → Except String (CDCL.Options × Bool)
  | [], acc => .ok acc
  | f :: fs, (o, c) =>
    match f with
    | "--no-vsids" => parseFlags fs ({ o with vsids := false }, c)
    | "--no-phase" => parseFlags fs ({ o with phaseSaving := false }, c)
    | "--no-restarts" => parseFlags fs ({ o with restarts := false }, c)
    | "--no-reduce" => parseFlags fs ({ o with reduce := false }, c)
    | "--keep-input" => parseFlags fs ({ o with removeSatisfied := false }, c)
    | "--check" => parseFlags fs (o, true)
    | _ =>
      if f.startsWith "--ccmin=" then
        match (f.drop 8).toString with
        | "0" => parseFlags fs ({ o with ccminMode := .none }, c)
        | "1" => parseFlags fs ({ o with ccminMode := .basic }, c)
        | "2" => parseFlags fs ({ o with ccminMode := .recursive }, c)
        | _ => .error s!"bad flag {f}: ccmin_mode is 0, 1 or 2"
      else .error s!"unknown flag {f}"

def main (args : List String) : IO UInt32 := do
  let (flags, files) := args.partition (·.startsWith "--")
  let (opts, check) ← match parseFlags flags ({}, false) with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 1
  let (input, proof?) ← match files with
    | [i] => pure (i, none)
    | [i, p] => pure (i, some p)
    | _ =>
      IO.eprintln "usage: cdcl [options] INPUT.cnf [PROOF.lrat]"
      return 1
  let text ← IO.FS.readFile input
  let φ ← match CNF.ofDIMACS text with
    | .ok φ => pure φ
    | .error e => IO.eprintln e; return 1
  let t₀ ← IO.monoMsNow
  let a ← (pure (CDCL.answerFor opts φ) : IO _)
  let t₁ ← IO.monoMsNow
  let stats := a.stats
  IO.println s!"c variables {(CDCL.occurringVars φ).length} occurring, clauses {φ.length}"
  IO.println s!"c conflicts {stats.conflicts}, decisions {stats.decisions}, \
    propagations {stats.propagations}, restarts {stats.restarts}"
  IO.println s!"c learned literals {stats.literals} ({stats.maxLiterals} before minimization), \
    forgotten {stats.removed}, simplified {stats.simplified}"
  IO.println s!"c solve time {t₁ - t₀} ms"
  if let some cert := a.cert then
    if let some p := proof? then
      IO.FS.writeFile p (LRAT.lratProofToString cert)
    if check then
      unless LRAT.check cert φ.toStdSat do
        IO.eprintln "c Lean core's LRAT checker rejected the certificate"
        return 1
      IO.println "c certificate accepted by Lean core's LRAT checker"
  IO.print a.output
  return a.code
