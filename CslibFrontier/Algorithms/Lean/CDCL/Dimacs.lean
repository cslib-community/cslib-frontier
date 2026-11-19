/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Watched
public import CslibFrontier.Logics.Propositional.CNF.Dimacs

/-! # The CDCL solver on DIMACS text

What the executable `lake exe cdcl` prints, apart from the statistics and times:
`Cslib.Algorithms.Lean.CDCL.answerDIMACS` reads a DIMACS CNF formula, solves it on renamed
variables (`Cslib.Algorithms.Lean.CDCL.solveCompactWith`), and gives the answer in the format of
the SAT competitions with MiniSat's exit code: `s SATISFIABLE` and the model on `v` lines, exit
code `10`, or `s UNSATISFIABLE` and the certificate, exit code `20`.

The model lists one literal for each variable occurring in the formula, in increasing order, and
ends with `0`: a formula without variables gets `v 0`, and a formula over the single DIMACS
variable `10⁶` gets one literal, not one for each smaller name.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.occurringVars`: the distinct variables of a formula.
* `Cslib.Algorithms.Lean.CDCL.modelLines`: the `v` lines of a model.
* `Cslib.Algorithms.Lean.CDCL.answerFor`, `Cslib.Algorithms.Lean.CDCL.answerDIMACS`: the answer
  for a formula, and for DIMACS text.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- The variables occurring in `φ`, each once, in increasing order. -/
def occurringVars (φ : CNF ℕ) : List ℕ := (φ.vars.mergeSort (· ≤ ·)).eraseReps

/-- The model `σ` on the variables `vs` as DIMACS literals on `v` lines of at most 80 characters,
the variable `v` as `v + 1`, negated where `σ` is false, and the final `0`. -/
def modelLines (σ : ℕ → Bool) (vs : List ℕ) : String := Id.run do
  let mut out := ""
  let mut line := "v"
  for v in vs do
    let lit := if σ v then s!" {v + 1}" else s!" -{v + 1}"
    if line.length + lit.length > 78 then
      out := out ++ line ++ "\n"
      line := "v"
    line := line ++ lit
  return out ++ line ++ " 0\n"

/-- The answer of the solver for a DIMACS formula. -/
structure DimacsAnswer where
  /-- The formula read. -/
  formula : CNF ℕ
  /-- The `s` line, and for a satisfiable formula the `v` lines. -/
  output : String
  /-- MiniSat's exit code: `10` for satisfiable, `20` for unsatisfiable. -/
  code : UInt32
  /-- The statistics of the solver. -/
  stats : Stats
  /-- The certificate, for an unsatisfiable formula. -/
  cert : Option (Array Std.Tactic.BVDecide.LRAT.IntAction)

/-- **The answer for a formula**, solved with the options `o` on renamed variables. -/
def answerFor (o : Options) (φ : CNF ℕ) : DimacsAnswer :=
  match solveCompactWith o φ with
  | (.sat σ, st) => ⟨φ, "s SATISFIABLE\n" ++ modelLines σ (occurringVars φ), 10, st, none⟩
  | (.unsat cert, st) => ⟨φ, "s UNSATISFIABLE\n", 20, st, some cert⟩

/-- **The answer for a DIMACS formula**, read by `Cslib.Logic.PL.CNF.ofDIMACS`; an error if the
text is not a DIMACS formula. -/
def answerDIMACS (o : Options) (text : String) : Except String DimacsAnswer :=
  return answerFor o (← CNF.ofDIMACS text)

end Cslib.Algorithms.Lean.CDCL
