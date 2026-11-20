/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.ApproximationSchemes

/-! # Checked maximization and minimization schemes -/

set_option linter.privateModule false

namespace CslibFrontierTests.ApproximationSchemes

open Cslib.Complexity Turing.MultiTapeTM

private def twoChoices (goal : OptimizationGoal) : NPOptimizationProblem encBool encBool where
  Feasible _ _ := True
  exists_feasible _ := ⟨false, trivial⟩
  feasible_mem_P := univ_mem_P
  solution_length_bound := ⟨1, by
    intro a b _
    rw [Polynomial.eval_one]
    exact Nat.le_refl 1⟩
  value ab := ab.2.toNat
  computableInPolyTime_value := ComputableInPolyTime.of_finite _
  goal := goal

example : (twoChoices .maximize).FPTAS := by
  refine ⟨fun _ => true, ComputableInPolyTime.const true, fun k _ a => ⟨trivial, ?_⟩⟩
  intro b _
  cases b <;> simp [twoChoices]

example : (twoChoices .minimize).PTAS := by
  apply NPOptimizationProblem.FPTAS.toPTAS
  refine ⟨fun _ => false, ComputableInPolyTime.const false, fun k _ a => ⟨trivial, ?_⟩⟩
  intro b _
  simp [twoChoices]

end CslibFrontierTests.ApproximationSchemes
