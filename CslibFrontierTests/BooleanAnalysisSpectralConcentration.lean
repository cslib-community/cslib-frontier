/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.SpectralConcentration
public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.SignApproximation
import CslibFrontier.Foundations.BooleanAnalysis.HammingFourier
import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for spectral concentration on collections of sets

On two bits, write `χ₀` and `χ₀₁` for the characters of `{0}` and `{0, 1}`. Bessel's inequality
bounds the weight of `χ₀ + χ₀₁` on `{{0}}` by its squared norm `2`. Approximating `χ₀ + χ₀₁` by
the degree-one `χ₀` bounds its weight above degree one by `‖χ₀₁‖₂ ^ 2 = 1`. The character `χ₀₁`
is `0`-concentrated on `{{0, 1}}`, and `χ₀₁ + χ₀ / 2` is at squared distance `1 / 4` from it, so
Exercise 3.17 makes `χ₀₁ + χ₀ / 2` `1 / 2`-concentrated there. Its coefficient on `{0}` is
`1 / 2`, so its weight on `{{0}}` is at most `1 / 2` times its spectral `1`-norm. Exercise 3.16
concentrates a character of three bits on at most `1 / ε` sets.

For arbitrary inputs: a Boolean function `δ`-close to one of degree at most `t` has weight at most
`4 δ` above degree `t`; Exercise 3.17 in the book's `ε₁`, `ε₂` form; and the collection of
Exercise 3.16 feeds the sign-rounding bound behind the low-degree algorithm. -/

public section

namespace CslibFrontierTests.BooleanAnalysisSpectralConcentration

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The squared norm of `χ₀ + χ₀₁` on two bits is `2`, since the characters are orthonormal. -/
theorem expect_sq_chi_add_chi :
    𝔼 x, (chi ℝ ({0} : Finset (Fin 2)) x + chi ℝ {0, 1} x) ^ 2 = 2 := by
  have h01 := expect_chi_mul_chi (ι := Fin 2) {0} {0, 1}
  rw [ite_eq_right (by decide)] at h01
  simp only [add_sq, mul_assoc] at h01 ⊢
  simp only [sq, chi_mul_self, expect_add_distrib, ← mul_expect, h01, Fintype.expect_const]
  norm_num

/-- Bessel's inequality: the weight of `χ₀ + χ₀₁` on `{{0}}` is at most its squared norm `2`. -/
theorem sum_singleton_fourierCoeff_sq_chi_add_chi_le :
    ∑ S ∈ {({0} : Finset (Fin 2))},
      fourierCoeff (fun x => chi ℝ ({0} : Finset (Fin 2)) x + chi ℝ {0, 1} x) S ^ 2 ≤ 2 :=
  (sum_fourierCoeff_sq_le_expect_sq _ _).trans_eq expect_sq_chi_add_chi

/-- Approximating `χ₀ + χ₀₁` by the degree-one `χ₀`, which has no weight above degree one, bounds
the weight of `χ₀ + χ₀₁` above degree one by `‖χ₀₁‖₂ ^ 2 = 1`. -/
theorem sum_fourierCoeff_sq_chi_add_chi_le :
    ∑ S with 1 < #S,
      fourierCoeff (fun x => chi ℝ ({0} : Finset (Fin 2)) x + chi ℝ {0, 1} x) S ^ 2 ≤ 1 := by
  refine (sum_fourierCoeff_sq_le_expect_sub_sq (g := chi ℝ {0}) fun S hS => ?_).trans_eq ?_
  · rw [fourierCoeff_chi, ite_eq_right]
    rintro rfl
    simp at hS
  · simp only [add_sub_cancel_left, sq, chi_mul_self, Fintype.expect_const]

/-- Exercise 3.17 for `χ₀₁` and `χ₀₁ + χ₀ / 2`: the first is `0`-concentrated on `{{0, 1}}`, they
are at squared distance `1 / 4`, so the second is `1 / 2`-concentrated on `{{0, 1}}`. -/
theorem sum_compl_fourierCoeff_sq_chi_add_half_chi_le :
    ∑ S ∈ {({0, 1} : Finset (Fin 2))}ᶜ,
      fourierCoeff (fun x => chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2) S ^ 2 ≤
        1 / 2 := by
  have h := sum_fourierCoeff_sq_le_two_mul_add {({0, 1} : Finset (Fin 2))}ᶜ (chi ℝ {0, 1})
    (fun x => chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2)
  have hf : ∑ S ∈ {({0, 1} : Finset (Fin 2))}ᶜ, fourierCoeff (chi ℝ {0, 1}) S ^ 2 = 0 :=
    sum_eq_zero fun S hS => by
      rw [fourierCoeff_chi, ite_eq_right fun h => by simp [← h] at hS]
      norm_num
  have hfg : 𝔼 x, (chi ℝ ({0, 1} : Finset (Fin 2)) x -
      (chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2)) ^ 2 = 1 / 4 := by
    have (x : Fin 2 → Bool) : (chi ℝ ({0, 1} : Finset (Fin 2)) x -
        (chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2)) ^ 2 = 1 / 4 := by
      rw [show ∀ a b : ℝ, (a - (a + b / 2)) ^ 2 = b * b / 4 by intros; ring, chi_mul_self]
    simp only [this, Fintype.expect_const]
  rw [hf, hfg] at h
  linarith

/-- The weight of small coefficients for `χ₀₁ + χ₀ / 2`: its coefficient on `{0}` is `1 / 2`, so
its weight on `{{0}}` is at most `1 / 2` times its spectral `1`-norm. -/
theorem sum_singleton_fourierCoeff_sq_chi_add_half_chi_le :
    ∑ S ∈ {({0} : Finset (Fin 2))},
      fourierCoeff (fun x => chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2) S ^ 2 ≤
        1 / 2 * ∑ S, |fourierCoeff
          (fun x => chi ℝ ({0, 1} : Finset (Fin 2)) x + chi ℝ {0} x / 2) S| := by
  refine sum_fourierCoeff_sq_le_mul_sum_abs (by norm_num) fun S hS => ?_
  rw [mem_singleton] at hS
  subst hS
  simp only [div_eq_inv_mul, fourierCoeff_add, fourierCoeff_const_mul, fourierCoeff_chi]
  rw [ite_eq_right (by decide)]
  norm_num

/-- A Boolean function that is `δ`-close to one of degree at most `t` has Fourier weight at most
`4 δ` above degree `t`. -/
theorem sum_fourierCoeff_sq_le_four_mul_of_mem_lowDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool) → Bool) (t : ℕ) (hg : (fun x => signVal (g x)) ∈ lowDegree ℝ ι t) :
    ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      4 * (hammingDist f g / 2 ^ Fintype.card ι) := by
  rw [← expect_sq_signVal_sub_signVal]
  exact sum_fourierCoeff_sq_le_expect_sub_sq fun _ hS =>
    fourierCoeff_eq_zero_of_mem_lowDegree hg (mem_filter.1 hS).2

/-- Exercise 3.17 as stated in the book: `ε₁`-concentration of `f` on `F` and
`‖f - g‖₂ ^ 2 ≤ ε₂` give `2 (ε₁ + ε₂)`-concentration of `g` on `F`. -/
theorem sum_compl_fourierCoeff_sq_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (Finset ι)) (f g : (ι → Bool) → ℝ) {ε₁ ε₂ : ℝ}
    (hf : ∑ S ∈ Fᶜ, fourierCoeff f S ^ 2 ≤ ε₁) (hfg : 𝔼 x, (f x - g x) ^ 2 ≤ ε₂) :
    ∑ S ∈ Fᶜ, fourierCoeff g S ^ 2 ≤ 2 * (ε₁ + ε₂) := by
  have := sum_fourierCoeff_sq_le_two_mul_add Fᶜ f g
  linarith

/-- The concentration of Exercise 3.16 feeds sign rounding: rounding the truncated expansion of a
Boolean function to signs errs on at most an `ε` fraction of inputs. -/
theorem exists_card_le_hammingDist_signRound_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (Finset ι),
      (#F : ℝ) ≤ (∑ S, |fourierCoeff (fun x => signVal (f x)) S|) ^ 2 / ε ∧
      (hammingDist (signRound fun x => ∑ S ∈ F,
        fourierCoeff (fun x => signVal (f x)) S * chi ℝ S x) f : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨F, hF, hw⟩ := exists_card_le_sum_fourierCoeff_sq_le (fun x => signVal (f x)) hε
  refine ⟨F, hF, (hammingDist_signRound_sum_mul_chi_div_le f F _).trans ?_⟩
  simpa using hw

/-- A character is concentrated on its own set: with `‖χ̂_S‖₁ = 1`, at most `1 / ε` sets carry
all but `ε` of the weight. -/
theorem exists_card_le_one_div_sum_fourierCoeff_sq_chi_le (S : Finset (Fin 3)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : Finset (Finset (Fin 3)), (#F : ℝ) ≤ 1 / ε ∧
      ∑ T ∈ Fᶜ, fourierCoeff (chi ℝ S) T ^ 2 ≤ ε := by
  obtain ⟨F, hF, hconc⟩ := exists_card_le_sum_fourierCoeff_sq_le (chi ℝ S) hε
  refine ⟨F, ?_, hconc⟩
  rwa [sum_abs_fourierCoeff_chi, one_pow] at hF

end CslibFrontierTests.BooleanAnalysisSpectralConcentration
