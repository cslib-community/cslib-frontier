/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Logics.Propositional.CNF.LRATFile

/-!
# The LRAT checker on files

`lake exe lrat_check FORMULA.cnf PROOF.lrat` reads a DIMACS CNF file and an LRAT proof, text or
binary, and checks the proof with `Cslib.Logic.PL.CNF.checkDIMACSLRAT`: Lean core's LRAT parser
and the array checker `Cslib.Logic.PL.CNF.checkLRATFast`, which checks RUP and RAT steps and
deletions. It prints `s VERIFIED UNSAT`, as `cake_lpr` does, and exits with `0` when the proof
is accepted, and prints `s REJECTED` with the reason and exits with `1` otherwise; `c` lines give
the time spent reading the files and checking.

The verdict is correct by `Cslib.Logic.PL.CNF.not_satisfiable_of_checkDIMACSLRAT`: an accepted
proof shows that the formula `Cslib.Logic.PL.CNF.ofDIMACS` reads from the file is unsatisfiable.
The DIMACS parser is trusted to read the file as intended; the LRAT parser is not trusted.
-/

open Cslib.Logic.PL

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args
    | IO.eprintln "usage: lrat_check FORMULA.cnf PROOF.lrat"; return 2
  let t₀ ← IO.monoMsNow
  let cnf ← IO.FS.readFile cnfPath
  let proof ← IO.FS.readBinFile proofPath
  let t₁ ← IO.monoMsNow
  let verdict := CNF.checkDIMACSLRAT cnf proof
  match verdict with
  | .ok () =>
    let t₂ ← IO.monoMsNow
    IO.println s!"c read {t₁ - t₀} ms, parse and check {t₂ - t₁} ms"
    IO.println "s VERIFIED UNSAT"
    return 0
  | .error e =>
    let t₂ ← IO.monoMsNow
    IO.println s!"c read {t₁ - t₀} ms, parse and check {t₂ - t₁} ms"
    IO.println s!"s REJECTED {e}"
    return 1
