/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Reduction.LinearApproximation

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

private theorem minPTAS : (twoChoices .minimize).PTAS := by
  apply NPOptimizationProblem.FPTAS.toPTAS
  refine ⟨fun _ => false, ComputableInPolyTime.const false, fun k _ a => ⟨trivial, ?_⟩⟩
  intro b _
  simp [twoChoices]

private theorem minOptimum (a : Bool) : (twoChoices .minimize).optimum a = 0 :=
  Nat.le_zero.mp ((twoChoices .minimize).optimum_le_value (b := false) rfl trivial)

private theorem maxOptimum (a : Bool) : (twoChoices .maximize).optimum a = 1 := by
  apply Nat.le_antisymm
  · obtain ⟨b, _, h⟩ := (twoChoices .maximize).exists_optimum a
    rw [← h]
    cases a <;> cases b <;> decide
  · exact (twoChoices .maximize).value_le_optimum (b := true) rfl trivial

/-- Negating the Boolean solution recovers a maximizer from a minimizer with the same error. -/
private def recoverMaximum : LReduction (twoChoices .maximize) (twoChoices .minimize) where
  mapInstance := id
  recover p := !p.2
  computableInPolyTime_mapInstance := ComputableInPolyTime.id'
  computableInPolyTime_recover := ComputableInPolyTime.of_finite _
  optimumFactor := 1
  optimumFactor_pos := Nat.one_pos
  errorFactor := 1
  errorFactor_pos := Nat.one_pos
  feasible_recover _ _ _ := trivial
  optimum_bound a := by rw [minOptimum, maxOptimum]; decide
  error_bound a b _ := by
    rw [minOptimum, maxOptimum]
    cases a <;> cases b <;> decide

example : (twoChoices .maximize).PTAS :=
  (recoverMaximum.trans (LReduction.refl _)).ptas minPTAS

end CslibFrontierTests.ApproximationSchemes
