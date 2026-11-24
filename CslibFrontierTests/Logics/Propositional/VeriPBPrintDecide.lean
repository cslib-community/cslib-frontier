/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontierTests.Logics.Propositional.VeriPBPrint
-- `import all`: the kernel evaluates `printOPB` and its private word builders in `Print`, the
-- parsers and checkers of `Text` and the step `stepTop` of `Redundance`, whose bodies are not
-- exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Instances built in Lean, printed, re-parsed and checked by the kernel, and the end-to-end
soundness theorems applied to the result: the conclusion is about the Lean value, with no
statement about parsing left to trust.

* `cover` and `mixed` are printed, and printed and re-parsed, and so is a CNF formula, by
  `decide +kernel`, independently of the round-trip theorems.
* The optimality proof of `cover` (elaborated by VeriPB 3.0.2, as in
  `CslibFrontierTests.Logics.Propositional.VeriPBText`) is accepted against `printOPB cover` with
  `BOUNDS 1 : 6 1`, so the optimum of `cover` is `1`.
* The instance `x1 >= 1`, `~x1 >= 1` is refuted by one `pol` step, so it has no solution.
* The formula `x1`, `¬x1` is refuted against its DIMACS text.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBPrint

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text

example : printOPB cover = "* #variable= 3 #constraint= 2 \nmin: 1 x1 1 x2 1 x3 ; \n\
    1 x1 1 x2 >= 1 ; \n1 x2 1 x3 >= 1 ; \n" := by
  decide +kernel
example : printOPB mixed = "* #variable= 5 #constraint= 2 \nmin: -2 x5 0 x1 7 ; \n\
    preserved: x5 x1 ; \n2 x1 3 ~x5 >= 3 ; \n>= 0 ; \n" := by
  decide +kernel
example : parseOPB (printOPB cover) = some cover := by decide +kernel
example : parseOPB (printOPB mixed) = some mixed := by decide +kernel
example : parseDIMACS (CNF.toDIMACS φ) = some φ := by decide +kernel

/-- The optimality proof of `cover`, elaborated by VeriPB 3.0.2. -/
def coverProof : String := "pseudo-Boolean proof version 3.0
f 2;
red 1 ~x1 >= 1 : x1 -> 0 x2 -> 1 : subproof
qed;
soli ~x1 x2 ~x3;
rup >= 1 : 5 1;
output NONE ;
conclusion BOUNDS 1 : 6 1;
end pseudo-Boolean proof;
"

theorem cover_accepted :
    checkOPB (printOPB cover) coverProof = some (.bounds (some 1) 6 (some 1) none) := by
  decide +kernel

/-- **The optimum of `cover` is `1`**, from the acceptance of the proof against its printed text. -/
example : ∃ f, cover.objective = some f ∧
    (∀ σ : ℕ → Bool, (∀ c ∈ cover.constraints, c.Holds σ) → 1 ≤ f.eval σ) ∧
    ∃ σ : ℕ → Bool, (∀ c ∈ cover.constraints, c.Holds σ) ∧ f.eval σ ≤ 1 := by
  obtain ⟨f, hf, hlb, hub⟩ := bounds_of_checkOPB_printOPB (stdNames_covers _) (out := none)
    (show (checkOPBOutput (printOPB cover) coverProof).map (·.1) = _ from cover_accepted)
  refine ⟨f, hf, fun σ hσ => ?_, hub 1 rfl⟩
  obtain ⟨l, hl, hle⟩ := hlb σ hσ
  cases hl
  exact hle

/-- `x1 >= 1` and `~x1 >= 1`. -/
def contra : Instance := ⟨[⟨[(1, (0, true))], 1⟩, ⟨[(1, (0, false))], 1⟩], none, none⟩

/-- Their sum `x1 + ~x1 >= 2` is a contradiction. -/
def contraProof : String := "pseudo-Boolean proof version 3.0
f 2;
pol 1 2 +;
output NONE;
conclusion UNSAT : 3;
end pseudo-Boolean proof;
"

theorem contra_accepted : checkOPB (printOPB contra) contraProof = some (.unsat 3) := by
  decide +kernel

/-- **`contra` has no solution**, from the acceptance of the refutation against its printed text. -/
example : ∀ σ : ℕ → Bool, ¬ ∀ c ∈ contra.constraints, c.Holds σ :=
  not_satisfiable_of_checkOPB_printOPB (stdNames_covers _) (out := none)
    (show (checkOPBOutput (printOPB contra) contraProof).map (·.1) = _ from contra_accepted)

/-- The formula `x1`, `¬x1`. -/
def contraCNF : CNF ℕ := [[(0, true)], [(0, false)]]

theorem contraCNF_accepted : checkDIMACS contraCNF.toDIMACS contraProof = some (.unsat 3) := by
  decide +kernel

/-- **`contraCNF` is unsatisfiable**, from the refutation of its DIMACS text. -/
example : ¬ contraCNF.Satisfiable := not_satisfiable_of_checkDIMACS_toDIMACS contraCNF_accepted

end CslibFrontierTests.Logics.Propositional.VeriPBPrint
