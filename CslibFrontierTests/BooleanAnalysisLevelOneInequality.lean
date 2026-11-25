/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.LevelOneInequality
public import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Tests for the Level-1 Inequality and Hoeffding's bound for signs

The conjunction of two bits, read as `0` or `1`, takes values in `[0, 1]` and has mean
`𝔼 |f| = 1 / 4`, so the Level-1 Inequality for `[-1, 1]`-valued functions bounds its degree-one
weight by `16 (1 / 4) ^ 2 ln 4 = ln 4`; its actual weight is
`2 (1 / 4) ^ 2 = 1 / 8`. This instance only exercises the statement, since `ln 4` exceeds the
trivial bound `α (1 - α)`; for `{0, 1}`-valued functions the sharp Level-1 Inequality and its
seven-bit client are in `CslibFrontierTests.BooleanAnalysisLevelK`. Minus half the two-bit
conjunction takes values in `[-1 / 2, 0]` and has `𝔼 |f| = 1 / 8`, so the `[-1, 1]` form bounds
its weight by `ln 8 / 4`. Hoeffding's bound for four unweighted signs bounds the strings with
`|x₀ + x₁ + x₂ + x₃| ≥ 4`, of which there are two, by
`32 exp (-2) ≈ 4.3`. -/

public section

namespace CslibFrontierTests.BooleanAnalysisLevelOneInequality

open Cslib BitString Finset Real
open scoped BigOperators

/-- The conjunction of two bits, read as `0` or `1`, has mean `1 / 4`. -/
theorem expect_bitVal_and₂ : 𝔼 x : Fin 2 → Bool, bitVal ℝ (x 0 && x 1) = 1 / 4 := by
  simp only [Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num

/-- A bit read as `0` or `1` is its own absolute value. -/
theorem abs_bitVal (b : Bool) : |bitVal ℝ b| = bitVal ℝ b := by
  cases b <;> simp

/-- A bit read as `0` or `1` lies in `[-1, 1]`. -/
theorem abs_bitVal_le_one (b : Bool) : |bitVal ℝ b| ≤ 1 := by
  cases b <;> simp

/-- The Level-1 Inequality for the conjunction of two bits: `W¹ ≤ ln 4`. -/
example : levelWeight 1 (fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1)) ≤ log 4 := by
  have h := levelWeight_one_le_of_abs_le_one
    (f := fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1)) (fun x => abs_bitVal_le_one _)
    (by simp only [abs_bitVal, expect_bitVal_and₂]; norm_num)
  simp only [abs_bitVal, expect_bitVal_and₂] at h
  norm_num at h
  exact h

/-- Minus half the conjunction of two bits has `𝔼 |f| = 1 / 8`. -/
theorem expect_abs_neg_half_bitVal_and₂ :
    𝔼 x : Fin 2 → Bool, |-bitVal ℝ (x 0 && x 1) / 2| = 1 / 8 := by
  simp only [Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num

/-- The `[-1, 1]` form for minus half the conjunction of two bits: `W¹ ≤ ln 8 / 4`. -/
example : levelWeight 1 (fun x : Fin 2 → Bool => -bitVal ℝ (x 0 && x 1) / 2) ≤ log 8 / 4 := by
  have h := levelWeight_one_le_of_abs_le_one
    (f := fun x : Fin 2 → Bool => -bitVal ℝ (x 0 && x 1) / 2)
    (fun x => by cases x 0 <;> cases x 1 <;> norm_num)
    (by rw [expect_abs_neg_half_bitVal_and₂]; norm_num)
  rw [expect_abs_neg_half_bitVal_and₂] at h
  norm_num at h
  linarith

/-- Hoeffding's bound for four unweighted signs: at most `32 exp (-2)` strings have
`|x₀ + x₁ + x₂ + x₃| ≥ 4`. -/
example : (#{x : Fin 4 → Bool | 4 ≤ |∑ i, signVal (x i)|} : ℝ) ≤ 32 * exp (-2) := by
  have h := card_filter_le_abs_sum_mul_signVal_le (fun _ : Fin 4 => (1 : ℝ)) (t := 4)
    (by norm_num)
  norm_num at h
  exact h

end CslibFrontierTests.BooleanAnalysisLevelOneInequality
