/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegreePart

/-! # Tests for the low-degree part and its `L^q` norms

The low-degree part of a character keeps it exactly when its set is small, the low-degree part of
`g = χ_{0} + χ_{0, 1}` up to degree `1` is `χ_{0}`, of degree at most `1`, with squared `L²` norm
`1 ≤ ‖g‖₂ ^ 2 = 2`, and the sum of the degree-`0` and degree-`1` parts of `g`; the low-degree
part up to the number of coordinates is the function itself. `L^p` norms increase with `p`; the
`L²` form of Exercise 9.8(a), Proposition 10.37 and Lemma 10.38 apply at `q = 4`, and the `L²` form
of Exercise 9.8(b) and Proposition 10.37 at `q = 3 / 2`, in particular to `g`. -/

public section

namespace CslibFrontierTests.BooleanAnalysisLowDegreePart

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The low-degree part of `χ_{0, 1}` up to degree `1` has no coefficient on `{0, 1}`. -/
example : fourierCoeff (lowDegreePart 1 (chi ℝ ({0, 1} : Finset (Fin 3)))) {0, 1} = 0 := by
  simp

/-- The low-degree part of `χ_{0, 1}` up to degree `2` keeps its coefficient. -/
example : fourierCoeff (lowDegreePart 2 (chi ℝ ({0, 1} : Finset (Fin 3)))) {0, 1} = 1 := by
  simp [fourierCoeff_chi]

/-- The two-bit function `χ_{0} + χ_{0, 1}`: in the `±1` reading `signVal` (`false ↦ 1`,
`true ↦ -1`), it is `2 signVal (x 0)` when `x 1 = false` and `0` when `x 1 = true`. -/
noncomputable def g : (Fin 2 → Bool) → ℝ := fun x => chi ℝ {0} x + chi ℝ {0, 1} x

/-- Up to degree `1`, the low-degree part of `χ_{0} + χ_{0, 1}` is `χ_{0}`. -/
theorem lowDegreePart_one_g : lowDegreePart 1 g = chi ℝ {0} := by
  refine fourierCoeff_injective (funext fun S => ?_)
  have h : fourierCoeff g S = fourierCoeff (chi ℝ {0}) S + fourierCoeff (chi ℝ {0, 1}) S :=
    fourierCoeff_add _ _ S
  rw [fourierCoeff_lowDegreePart, h, fourierCoeff_chi, fourierCoeff_chi]
  by_cases h0 : S = {0}
  · subst h0
    simp [show ({0, 1} : Finset (Fin 2)) ≠ {0} by decide]
  · by_cases h01 : S = {0, 1}
    · subst h01
      simp [show ({0} : Finset (Fin 2)) ≠ {0, 1} by decide]
    · simp [Ne.symm h0, Ne.symm h01]

/-- A character has `L^q` norm `1`. -/
theorem lpNorm_chi (q : ℝ) (S : Finset (Fin 2)) : lpNorm q (chi ℝ S) = 1 := by
  simp [lpNorm, abs_chi, Real.one_rpow]

/-- `g^{≤1}` has degree at most `1`. -/
example : lowDegreePart 1 g ∈ lowDegree ℝ (Fin 2) 1 := lowDegreePart_mem_lowDegree 1 g

/-- The degree-`0` and degree-`1` parts of `g` sum to `χ_{0}`. -/
example (x : Fin 2 → Bool) : ∑ j ∈ range 2, levelPart j g x = chi ℝ {0} x := by
  rw [sum_range_levelPart 1 g x, lowDegreePart_one_g]

/-- The Fourier weight of `g` up to degree `1` is `1`. -/
theorem sum_fourierCoeff_g_sq : ∑ S with #S ≤ 1, fourierCoeff g S ^ 2 = 1 := by
  rw [← lpNorm_two_lowDegreePart_sq, lowDegreePart_one_g, lpNorm_chi, one_pow]

/-- `‖g‖₂ = √2`. -/
theorem lpNorm_two_g : lpNorm 2 g = √2 := by
  have h : 𝔼 x, g x ^ 2 = 2 := by
    rw [expect_sq_eq_sum_fourierCoeff_sq]
    have hc (S : Finset (Fin 2)) :
        fourierCoeff g S = fourierCoeff (chi ℝ {0}) S + fourierCoeff (chi ℝ {0, 1}) S :=
      fourierCoeff_add _ _ S
    simp only [hc, fourierCoeff_chi, add_sq, sum_add_distrib, ite_pow, one_pow,
      zero_pow two_ne_zero, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
    simp only [show ({0} : Finset (Fin 2)) ≠ {0, 1} by decide, ↓reduceIte]
    norm_num
  rw [lpNorm_two, h]

/-- Taking the low-degree part of `g` up to degree `1` does not increase the `L²` norm:
`1 ≤ √2`. -/
example : (1 : ℝ) ≤ √2 := by
  have h := lpNorm_two_lowDegreePart_le 1 g
  rwa [lowDegreePart_one_g, lpNorm_chi, lpNorm_two_g] at h

/-- The `L²` form of Exercise 9.8(a) at `q = 4` and `k = 1` for `g`: `1 ≤ √3 ‖g‖₂`. -/
example : 1 ≤ √3 * lpNorm 2 g := by
  have h := lpNorm_lowDegreePart_le_lpNorm_two (q := 4) (by norm_num) 1 g
  rw [lowDegreePart_one_g, lpNorm_chi] at h
  norm_num at h
  exact h

/-- Up to degree `3` on three coordinates, the low-degree part is the function itself. -/
example (f : (Fin 3 → Bool) → ℝ) : lowDegreePart 3 f = f :=
  lowDegreePart_of_card_le (by simp) f

/-- The mean absolute value is at most the root mean square. -/
example (f : (Fin 3 → Bool) → ℝ) : 𝔼 x, |f x| ≤ √(𝔼 x, f x ^ 2) := by
  rw [← lpNorm_one, ← lpNorm_two]
  exact lpNorm_le_lpNorm_of_exponent_le one_pos (by norm_num) f

/-- Proposition 10.37 at `q = 4`: `‖f^{≤k}‖₄ ≤ √3 ^ k ‖f‖₄`. -/
example (f : (Fin 3 → Bool) → ℝ) (k : ℕ) :
    lpNorm 4 (lowDegreePart k f) ≤ √3 ^ k * lpNorm 4 f := by
  have h := lpNorm_lowDegreePart_le (q := 4) (by norm_num) k f
  norm_num at h
  exact h

/-- Proposition 10.37 at `q = 4` and `k = 1` for `χ_{0} + χ_{0, 1}`: its `L⁴` norm is at least
`1 / √3`. -/
example : 1 ≤ √3 * lpNorm 4 g := by
  have h := lpNorm_lowDegreePart_le (q := 4) (by norm_num) 1 g
  rw [lowDegreePart_one_g, lpNorm_chi] at h
  norm_num at h
  exact h

/-- Lemma 10.38 at `ρ = 1 / 2`: `‖f^{≤k}‖₄ ≤ (2 √3) ^ k ‖T_{1/2} f‖₄`. -/
example (f : (Fin 3 → Bool) → ℝ) (k : ℕ) :
    lpNorm 4 (lowDegreePart k f) ≤ (2 * √3) ^ k * lpNorm 4 (noiseOp (1 / 2) f) := by
  have h := lpNorm_lowDegreePart_le_noiseOp (q := 4) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) k f
  rwa [show √(4 - 1 : ℝ) / (1 / 2) = 2 * √3 by norm_num; ring] at h

/-- The `L²` form of Lemma 10.38 for `χ_{0} + χ_{0, 1}`, `k = 1` and `ρ = 1 / 2`:
`‖T_{1/2} g‖₂ ≥ 1 / 2`. -/
example : 1 ≤ 2 * lpNorm 2 (noiseOp (1 / 2) g) := by
  have h := lpNorm_two_lowDegreePart_le_noiseOp (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) 1 g
  rw [lowDegreePart_one_g, lpNorm_chi] at h
  norm_num at h
  exact h

/-- `1 / √(3 / 2 - 1) = √2`. -/
theorem one_div_sqrt_three_halves_sub_one : (1 : ℝ) / √(3 / 2 - 1) = √2 := by
  rw [show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num, Real.sqrt_div' 1 (by norm_num), Real.sqrt_one,
    one_div_one_div]

/-- Proposition 10.37 at `q = 3 / 2`: `‖f^{≤k}‖_{3/2} ≤ √2 ^ k ‖f‖_{3/2}`. -/
example (f : (Fin 3 → Bool) → ℝ) (k : ℕ) :
    lpNorm (3 / 2) (lowDegreePart k f) ≤ √2 ^ k * lpNorm (3 / 2) f := by
  have h := lpNorm_lowDegreePart_le_of_le_two (q := 3 / 2) (by norm_num) (by norm_num) k f
  rwa [one_div_sqrt_three_halves_sub_one] at h

/-- The `L²` form of Exercise 9.8(b) at `q = 3 / 2` and `k = 1` for `g`: its `L^{3/2}` norm is at
least `1 / √2`. -/
example : 1 ≤ √2 * lpNorm (3 / 2) g := by
  have h := lpNorm_two_lowDegreePart_le_lpNorm (q := 3 / 2) (by norm_num) (by norm_num) 1 g
  rw [lowDegreePart_one_g, lpNorm_chi, one_div_sqrt_three_halves_sub_one, pow_one] at h
  exact h

end CslibFrontierTests.BooleanAnalysisLowDegreePart
