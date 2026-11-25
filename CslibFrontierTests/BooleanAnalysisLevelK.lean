/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.LevelK
public import CslibFrontierTests.BooleanAnalysisSmallSetExpansion
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The Level-`k` Inequalities on small cubes

On one bit, the subcube `A = {x | x () = true}` (the fixture of the Small-Set Expansion and
Reverse Small-Set Expansion clients) has volume `α = 1 / 2`, degree-one weight
`W¹[1_A] = 1 / 4` and weight `W^{≤1}[1_A] = 1 / 2` up to degree one. Then:

* `ρ W^{≤1}[1_A] = 1 / 4 ≤ 3 / 8 = Stab_{1/2}[1_A]` at `ρ = 1 / 2`;
* inequality (9.7) at `k = 1`: `W^{≤1}[1_A] = 1 / 2 ≤ 3 (1 / 2) ^ (3 / 2)`;
* `1 ≤ 2 ln 2`, so the Level-`1` Inequality applies: `W^{≤1}[1_A] = 1 / 2 ≤ 2e ln 2 / 4`;
* Exercise 9.18(a) at `ρ = 1` is attained: `W¹[1_A] = α - α ^ 2 = 1 / 4`;
* the sharp Level-1 Inequality gives `W¹[1_A] = 1 / 4 ≤ 2 (1 / 2) ^ 2 ln 2`.

On three bits, the all-`true` point (the Small-Set Expansion clients' `top₃`) has volume `1 / 8`,
and `2 ≤ 2 ln 8`, so the Level-`2` Inequality applies with the bound `(e ln 8) ^ 2 / 64`. On
seven bits, the all-`true` point has volume `α = 1 / 128`; there the sharp Level-1 Inequality
beats the trivial `W¹[1_A] ≤ α (1 - α)`, and the Level-`1` Inequality beats the trivial
`W^{≤1}[1_A] ≤ α`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisLevelK

open Cslib Cslib.BitString Finset Real
open CslibFrontierTests.BooleanAnalysisReverseHypercontractivity (subcube mem_subcube
  expect_indicator_subcube)
open CslibFrontierTests.BooleanAnalysisSmallSetExpansion (noiseStability_indicator_subcube top₃
  expect_indicator_top₃)
open scoped BigOperators

/-- The subcube's degree-one weight is `1 / 4`: its coefficient on the bit is `-1 / 2`. -/
theorem levelWeight_one_indicator_subcube : levelWeight 1 ((subcube true).indicator 1) = 1 / 4 := by
  rw [levelWeight_one, Fintype.sum_unique, fourierCoeff, Fintype.expect_unique_bool]
  simp [mem_subcube, Set.indicator, chi_singleton]
  norm_num

/-- Up to degree one the subcube carries all of its weight `𝔼 1_A ^ 2 = 1 / 2`. -/
theorem sum_filter_card_le_one_indicator_subcube :
    ∑ S with #S ≤ 1, fourierCoeff ((subcube true).indicator 1) S ^ 2 = 1 / 2 := by
  rw [filter_true_of_mem fun S _ => (card_le_univ S).trans_eq Fintype.card_unit,
    ← expect_sq_eq_sum_fourierCoeff_sq, Fintype.expect_unique_bool]
  simp [mem_subcube, Set.indicator]

-- `ρ ^ k W^{≤k} ≤ Stab_ρ` at `ρ = 1 / 2`, `k = 1`: `(1 / 2) W^{≤1}[1_A] = 1 / 4 ≤ 3 / 8`.
example :
    (1 / 2 : ℝ) ^ 1 * ∑ S with #S ≤ 1, fourierCoeff ((subcube true).indicator 1) S ^ 2 ≤ 3 / 8 := by
  have h := pow_mul_sum_filter_card_le_le_noiseStability (ρ := 1 / 2) (by norm_num) (by norm_num)
    1 ((subcube true).indicator 1)
  rw [noiseStability_indicator_subcube] at h
  linarith

-- Inequality (9.7) at `k = 1`: `W^{≤1}[1_A] = 1 / 2 ≤ 3 (1 / 2) ^ (3 / 2)`.
example : ∑ S with #S ≤ 1, fourierCoeff ((subcube true).indicator 1) S ^ 2 ≤
    3 ^ 1 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by
  have h := sum_filter_card_le_fourierCoeff_indicator_sq_le_three_pow (subcube true) 1
  rwa [expect_indicator_subcube] at h

/-- `1 ≤ 2 ln 2`, so the Level-`1` Inequality applies to the subcube. -/
theorem one_le_two_mul_log_two : (1 : ℝ) ≤ 2 * log 2 := by
  linarith [log_two_gt_d9]

-- The Level-`1` Inequality on the subcube: `W^{≤1}[1_A] = 1 / 2 ≤ (2e ln 2) (1 / 2) ^ 2`.
example : ∑ S with #S ≤ 1, fourierCoeff ((subcube true).indicator 1) S ^ 2 ≤
    (2 * exp 1 / (1 : ℕ) * log 2) ^ 1 * (1 / 2) ^ 2 := by
  have h := sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow (k := 1) one_pos (subcube true)
    (by rw [expect_indicator_subcube true, one_div, inv_inv]; exact_mod_cast one_le_two_mul_log_two)
  rw [expect_indicator_subcube true] at h
  simpa only [one_div, inv_inv] using h

-- Exercise 9.18(a) at `ρ = 1` bounds `W¹[1_A]` by `α - α ^ 2`, and the subcube attains it.
example : levelWeight 1 ((subcube true).indicator 1) ≤ 1 / 2 - (1 / 2) ^ 2 ∧
    levelWeight 1 ((subcube true).indicator 1) = 1 / 2 - (1 / 2) ^ 2 := by
  have h := levelWeight_one_indicator_le_rpow zero_lt_one le_rfl (subcube true)
  rw [expect_indicator_subcube true] at h
  refine ⟨h.trans_eq (by norm_num), ?_⟩
  rw [levelWeight_one_indicator_subcube]
  norm_num

-- The sharp Level-1 Inequality on the subcube: `W¹[1_A] = 1 / 4 ≤ 2 (1 / 2) ^ 2 ln 2`.
example : levelWeight 1 ((subcube true).indicator 1) ≤ 2 * (1 / 2) ^ 2 * log 2 := by
  have h := levelWeight_one_indicator_le (subcube true)
  rw [expect_indicator_subcube true] at h
  simpa only [one_div, inv_inv] using h

/-- `2 ≤ 2 ln 8`, so the Level-`2` Inequality applies to the point of volume `1 / 8`. -/
theorem two_le_two_mul_log_eight : (2 : ℝ) ≤ 2 * log 8 := by
  have h : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  linarith [log_two_gt_d9]

-- The Level-`2` Inequality on the point of volume `1 / 8`.
example : ∑ S with #S ≤ 2, fourierCoeff (top₃.indicator 1) S ^ 2 ≤
    (2 * exp 1 / (2 : ℕ) * log 8) ^ 2 * (1 / 8) ^ 2 := by
  have h := sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow (k := 2) two_pos top₃
    (by rw [expect_indicator_top₃, one_div, inv_inv]; exact_mod_cast two_le_two_mul_log_eight)
  rw [expect_indicator_top₃] at h
  simpa only [one_div, inv_inv] using h

/-- The all-`true` point of the seven-bit cube. -/
def top₇ : Set (Fin 7 → Bool) := {fun _ => true}

/-- The all-`true` point of the seven-bit cube has volume `1 / 128`. -/
theorem expect_indicator_top₇ : 𝔼 x, top₇.indicator (1 : (Fin 7 → Bool) → ℝ) x = 1 / 128 := by
  simp [top₇, Set.indicator_apply]

/-- `log 128 = 7 log 2`. -/
theorem log_one_hundred_twenty_eight : log 128 = 7 * log 2 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
  norm_num

-- At `α = 1 / 128` the sharp Level-1 Inequality beats the trivial `W¹[1_A] ≤ α (1 - α)`:
-- `2 α ^ 2 ln (1 / α) = 14 ln 2 / 16384 < 127 / 16384`.
example : levelWeight 1 (top₇.indicator 1) < 1 / 128 * (1 - 1 / 128) := by
  have h := levelWeight_one_indicator_le top₇
  rw [expect_indicator_top₇, one_div (128 : ℝ), inv_inv, log_one_hundred_twenty_eight] at h
  linarith [log_two_lt_d9]

-- At `α = 1 / 128` the Level-`1` Inequality beats the trivial `W^{≤1}[1_A] ≤ α`:
-- `(2e ln 128) α ^ 2 = 14 e ln 2 / 16384 < 128 / 16384`.
example : ∑ S with #S ≤ 1, fourierCoeff (top₇.indicator 1) S ^ 2 < 1 / 128 := by
  have h := sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow (k := 1) one_pos top₇
    (by
      rw [expect_indicator_top₇, one_div, inv_inv, log_one_hundred_twenty_eight]
      push_cast
      linarith [log_two_gt_d9])
  rw [expect_indicator_top₇, one_div (128 : ℝ), inv_inv, log_one_hundred_twenty_eight] at h
  push_cast at h
  have he := exp_one_lt_d9
  have hl := log_two_lt_d9
  have hl0 := log_two_gt_d9
  nlinarith [exp_pos 1]

end CslibFrontierTests.BooleanAnalysisLevelK
