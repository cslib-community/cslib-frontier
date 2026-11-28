/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (formula-to-equation regression tests)

import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
import CslibFrontier.Logics.RealArithmetic.FormulaEquation

/-! Real zeros for a mixed Boolean formula and rejection of malformed input. -/

namespace CslibFrontierTests.FormulaEquation

open Cslib.Logic.RealArithmetic Cslib.Complexity

private def mixed : Formula 1 :=
  .and (.not (.ltZero (.var 0))) (.or (.eqZero (.const 1)) (.ltZero (.const (-1))))

example : ∃ y, (formulaWordEquation (encFormula 1 mixed)).eval y = 0 := by
  have hmem : encFormula 1 mixed ∈ ETR := (encFormula_mem_ETR _).mpr
    ⟨fun _ => 0, by simp [mixed, Formula.solutionSet, Term.eval]⟩
  obtain ⟨x, hx⟩ := (mem_ETR_iff_ofWord _).mp hmem
  obtain ⟨y, _, hy⟩ := (formulaWordEquation_eval_zero_iff _ x).mpr hx
  exact ⟨y, hy⟩

example : ¬ ∃ y, (formulaWordEquation []).eval y = 0 := by
  rintro ⟨y, hy⟩
  have h := (formulaWordEquation_eval_zero_iff [] _).mp ⟨y, rfl, hy⟩
  have hinvalid : validFormulaWord [] ≠ true := by
    intro hvalid
    obtain ⟨p, hp⟩ := validFormulaWord_eq_true_iff.mp hvalid
    cases p <;> simp [encFormula_apply, encFormula_tokens] at hp
  rw [Formula.ofWord_of_not_valid hinvalid, Formula.solutionSet] at h
  exact h

end CslibFrontierTests.FormulaEquation
