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

The conjunction of two bits, read as `0` or `1`, has mean `1 / 4`, so the Level-1 Inequality
bounds its degree-one weight by `16 (1 / 4) ^ 2 ln 4 = ln 4`; its actual weight is
`2 (1 / 4) ^ 2 = 1 / 8`. This instance only exercises the statement, since `ln 4` exceeds the
trivial bound `α (1 - α)`. The conjunction of seven bits has mean `α = 1 / 128`, where the
inequality's `7 ln 2 / 1024` is below the trivial `127 / 16384`. Minus half the two-bit
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

/-- The Level-1 Inequality for the conjunction of two bits: `W¹ ≤ ln 4`. -/
example : levelWeight 1 (fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1)) ≤ log 4 := by
  have h := levelWeight_one_bitVal_le (fun x : Fin 2 → Bool => x 0 && x 1)
    (by rw [expect_bitVal_and₂]; norm_num)
  rw [expect_bitVal_and₂] at h
  norm_num at h
  exact h

/-- The conjunction of seven bits. -/
def and₇ (x : Fin 7 → Bool) : Bool :=
  decide (x = fun _ => true)

/-- The conjunction of seven bits, read as `0` or `1`, has mean `1 / 128`. -/
theorem expect_bitVal_and₇ : 𝔼 x, bitVal ℝ (and₇ x) = 1 / 128 := by
  have h (x : Fin 7 → Bool) : bitVal ℝ (and₇ x) = if (fun _ => true) = x then 1 else 0 := by
    by_cases hx : x = fun _ => true <;> simp [and₇, hx, eq_comm]
  simp only [h]
  norm_num

/-- At `α = 1 / 128` the Level-1 Inequality beats the trivial bound `W¹[f] ≤ α (1 - α)`: it gives
`16 α ^ 2 ln (1 / α) = 7 ln 2 / 1024 < 7 / 1024 < 127 / 16384`. -/
example : levelWeight 1 (fun x => bitVal ℝ (and₇ x)) < 1 / 128 * (1 - 1 / 128) := by
  have h := levelWeight_one_bitVal_le and₇ (by rw [expect_bitVal_and₇]; norm_num)
  rw [expect_bitVal_and₇, inv_div, div_one, show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow] at h
  have := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
  push_cast at h
  generalize levelWeight 1 (fun x => bitVal ℝ (and₇ x)) = W at h ⊢
  linarith

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
