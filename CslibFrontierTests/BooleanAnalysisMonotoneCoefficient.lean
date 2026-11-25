/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial
public import CslibFrontier.Foundations.BooleanAnalysis.Variance

/-! # Tests for the large degree-one coefficient of a monotone function

The conjunction of two bits is monotone and nonconstant. Read as signs, its variance is `3 / 4`
and its total influence is at most `2`, so `I / Var ≤ 8 / 3`. Since the conjunction is monotone,
some degree-one coefficient has square at least `exp(-10 · 8 / 3) ≥ exp(-27)` (O'Donnell,
Exercise 9.33). Variance positivity also supplies the hypothesis of the KKL Edge-Isoperimetric
Theorem. -/

public section

namespace CslibFrontierTests.BooleanAnalysisMonotoneCoefficient

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- The conjunction is monotone. -/
theorem monotone_and₂ : Monotone and₂ :=
  fun _ _ h => inf_le_inf (h 0) (h 1)

/-- The conjunction is nonconstant: it is `true` at the all-`true` point and `false` at the
all-`false` point. -/
theorem exists_and₂_ne : ∃ x y, and₂ x ≠ and₂ y :=
  ⟨fun _ => true, fun _ => false, by decide⟩

/-- The conjunction, read as signs, has positive variance. -/
theorem variance_and₂_pos : 0 < 𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 :=
  expect_sub_expect_sq_signVal_pos exists_and₂_ne

-- `BooleanAnalysisVariance.lean` has the same computation but is not a module, so it cannot be
-- imported here.
/-- The conjunction, read as signs, has variance `3 / 4`: it is at relative distance `1 / 4`
from `false` and `3 / 4` from `true`. -/
theorem variance_and₂ : 𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 = 3 / 4 := by
  have h₀ : hammingDist and₂ (fun _ => false) = 1 := by decide
  have h₁ : hammingDist and₂ (fun _ => true) = 3 := by decide
  rw [expect_sub_expect_sq_signVal_eq_four_mul, h₀, h₁, Fintype.card_fin]
  norm_num

/-- The conjunction has total influence at most `2`, the number of bits. -/
theorem totalInfluence_and₂_le : totalInfluence (fun x => signVal (and₂ x)) ≤ 2 := by
  have h := totalInfluence_le_mul_expect_sq (fun x => signVal (and₂ x))
  simp only [sq, signVal_mul_self, Fintype.card_fin, Nat.cast_ofNat] at h
  rw [expect_const univ_nonempty] at h
  linarith

/-- `exp(-27) ≤ exp(-10 I / Var)` for the conjunction, as `I / Var ≤ 8 / 3`. -/
theorem exp_neg_twenty_seven_le_and₂ :
    Real.exp (-27) ≤ Real.exp (-(10 * totalInfluence (fun x => signVal (and₂ x)) /
      𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2)) := by
  rw [Real.exp_le_exp, variance_and₂, neg_le_neg_iff, div_le_iff₀ (by norm_num)]
  linarith [totalInfluence_and₂_le]

/-- **Exercise 9.33 for the conjunction**: some degree-one coefficient has square at least
`exp(-27)`. -/
theorem exists_exp_neg_twenty_seven_le_fourierCoeff_singleton_sq_and₂ :
    ∃ i, Real.exp (-27) ≤ fourierCoeff (fun x => signVal (and₂ x)) {i} ^ 2 := by
  obtain ⟨i, hi⟩ :=
    exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone monotone_and₂ exists_and₂_ne
  exact ⟨i, exp_neg_twenty_seven_le_and₂.trans hi⟩

/-- Variance positivity supplies the hypothesis of the KKL Edge-Isoperimetric Theorem: some
coordinate of the conjunction has influence at least `(9 / Ĩ²) 9^{-Ĩ}`. -/
theorem exists_nine_div_sq_mul_one_ninth_rpow_le_influence_and₂ :
    ∃ i, 9 / (totalInfluence (fun x => signVal (and₂ x)) /
          𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2) ^ 2 *
        (1 / 9 : ℝ) ^ (totalInfluence (fun x => signVal (and₂ x)) /
          𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2) ≤
      influence i fun x => signVal (and₂ x) :=
  exists_nine_div_sq_mul_one_ninth_rpow_le_influence and₂ variance_and₂_pos

end CslibFrontierTests.BooleanAnalysisMonotoneCoefficient
