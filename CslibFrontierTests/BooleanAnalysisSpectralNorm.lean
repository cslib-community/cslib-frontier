/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
public import CslibFrontier.Probability.Fooling

/-! # Tests for the spectral norm of a product

A character `χ_S` has spectral norm `1` and square `1`, so the bound `‖(χ_S²)^‖₁ ≤ ‖χ̂_S‖₁²` is an
equality, and an `ε`-biased distribution `ε`-fools `χ_S²`. The product of the two coordinate
characters on two bits is a character, of spectral norm `1 = 1 · 1`. The function `χ_{0} + χ_{1}`
on two bits has spectral norm `2`, so every distribution, being `1`-biased, `4`-fools its square.
Multiplying it by a character keeps its spectral norm, writing it as a combination of characters
bounds its spectral norm by `2`, and so do restricting it and taking a coefficient of a restriction
as a function of the fixed bits. -/

public section

namespace CslibFrontierTests.BooleanAnalysisSpectralNorm

open Cslib Cslib.BitString Cslib.Probability Finset
open scoped BigOperators


/-- The square of a character is the constant `1`. -/
theorem chi_sq (S : Finset (Fin 3)) : (fun x => chi ℝ S x ^ 2) = fun _ => 1 :=
  funext fun x => (sq _).trans (chi_mul_self S x)

/-- The product formula at the empty set: `(χ_S χ_S)^(∅) = ∑_T χ̂_S(T) χ̂_S(T ∆ ∅) = 1`. -/
theorem fourierCoeff_chi_mul_chi_empty (S : Finset (Fin 3)) :
    fourierCoeff (fun x => chi ℝ S x * chi ℝ S x) ∅ = 1 := by
  have h (T : Finset (Fin 3)) : symmDiff T ∅ = T := symmDiff_bot T
  simp only [fourierCoeff_mul, fourierCoeff_chi, h, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, ite_true]

/-- The product of the two coordinate characters on two bits has spectral norm at most
`‖χ̂_{0}‖₁ ‖χ̂_{1}‖₁ = 1`. -/
theorem sum_abs_fourierCoeff_chi_zero_mul_chi_one_le :
    ∑ T, |fourierCoeff (fun x => chi ℝ ({0} : Finset (Fin 2)) x * chi ℝ {1} x) T| ≤ 1 :=
  (sum_abs_fourierCoeff_mul_le _ _).trans_eq (by
    rw [sum_abs_fourierCoeff_chi, sum_abs_fourierCoeff_chi, one_mul])

/-- The spectral norm of `χ_S²` is at most `‖χ̂_S‖₁² = 1`. -/
theorem sum_abs_fourierCoeff_chi_sq_le (S : Finset (Fin 3)) :
    ∑ T, |fourierCoeff (fun x => chi ℝ S x ^ 2) T| ≤ 1 :=
  (sum_abs_fourierCoeff_sq_le_sq _).trans_eq (by rw [sum_abs_fourierCoeff_chi, one_pow])

/-- The bound is attained: `χ_S² = 1` has spectral norm exactly `1`. -/
theorem sum_abs_fourierCoeff_chi_sq (S : Finset (Fin 3)) :
    ∑ T, |fourierCoeff (fun x => chi ℝ S x ^ 2) T| = 1 := by
  simp only [chi_sq, fourierCoeff_const, apply_ite abs, abs_one, abs_zero, sum_ite_eq',
    mem_univ, ite_true]

/-- An `ε`-biased distribution `ε`-fools the square of a character. -/
theorem fools_chi_sq {ε : ℝ} (hε : 0 ≤ ε) {X : PMF (Fin 3 → Bool)} (hX : IsSmallBias ε X)
    (S : Finset (Fin 3)) : Fools X ε fun x => chi ℝ S x ^ 2 := by
  have h := hX.fools_sq hε (chi ℝ S)
  rwa [sum_abs_fourierCoeff_chi, one_pow, one_mul] at h

/-- The sum of the two coordinate characters on two bits. -/
noncomputable def f (x : Fin 2 → Bool) : ℝ :=
  chi ℝ {0} x + chi ℝ {1} x

/-- `f` has spectral norm `2`. -/
theorem sum_abs_fourierCoeff_f : ∑ T, |fourierCoeff f T| = 2 := by
  have h (T : Finset (Fin 2)) : |fourierCoeff f T| =
      (if {0} = T then 1 else 0) + if {1} = T then 1 else 0 := by
    unfold f
    rw [fourierCoeff_add, fourierCoeff_chi, fourierCoeff_chi]
    exact abs_of_nonneg (by split_ifs <;> norm_num)
  simp only [h, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
  norm_num

/-- Every distribution is `1`-biased, so it `‖f̂‖₁² = 4`-fools `f²`; for instance a point
mass. -/
theorem fools_pure_f_sq : Fools (PMF.pure 0) 4 fun x => f x ^ 2 := by
  have h := (isSmallBias_one (PMF.pure (0 : Fin 2 → Bool))).fools_sq zero_le_one f
  rwa [sum_abs_fourierCoeff_f, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] at h

/-- Multiplying `f` by the character `χ_{0}` keeps its spectral norm `2`. -/
theorem sum_abs_fourierCoeff_chi_mul_f :
    ∑ T, |fourierCoeff (fun x => chi ℝ {0} x * f x) T| = 2 := by
  rw [sum_abs_fourierCoeff_chi_mul, sum_abs_fourierCoeff_f]

/-- The coefficient of `χ_{0} + χ_{1}` on `{0}` is `1`, read off the combination of characters. -/
theorem fourierCoeff_sum_chi_singleton_zero :
    fourierCoeff (fun x => ∑ u : Fin 2, (1 : ℝ) * chi ℝ {u} x) {0} = 1 := by
  rw [fourierCoeff_sum_mul]
  simp [fourierCoeff_chi]

/-- Written as a combination of the two coordinate characters with coefficients `1`, `f` has
spectral norm at most `|1| ‖χ̂_{0}‖₁ + |1| ‖χ̂_{1}‖₁ = 2`. -/
theorem sum_abs_fourierCoeff_sum_chi_le :
    ∑ V, |fourierCoeff (fun x => ∑ u : Fin 2, (1 : ℝ) * chi ℝ {u} x) V| ≤ 2 :=
  (sum_abs_fourierCoeff_sum_mul_le (fun _ => (1 : ℝ)) fun u => chi ℝ {u}).trans_eq
    (by simp only [abs_one, one_mul, sum_abs_fourierCoeff_chi]; norm_num)

/-- The restrictions of `f` have spectral norm at most `‖f̂‖₁ = 2` (Exercise 3.7(a)). -/
theorem sum_abs_fourierCoeff_f_piecewise_le (J : Finset (Fin 2)) (z : Fin 2 → Bool) :
    ∑ S, |fourierCoeff (fun x => f (J.piecewise x z)) S| ≤ 2 :=
  (sum_abs_fourierCoeff_piecewise_le f J z).trans_eq sum_abs_fourierCoeff_f

/-- The coefficient on `{0}` of the restriction of `f` fixing coordinate `1` to `z`, as a function
of `z`, has spectral norm at most `‖f̂‖₁ = 2` (a consequence of Proposition 3.21). -/
theorem sum_abs_fourierCoeff_fourierCoeff_f_piecewise_le :
    ∑ V, |fourierCoeff
      (fun z => fourierCoeff (fun x => f (({0} : Finset (Fin 2)).piecewise x z)) {0}) V| ≤ 2 :=
  (sum_abs_fourierCoeff_fourierCoeff_piecewise_le f {0} {0}).trans_eq sum_abs_fourierCoeff_f

end CslibFrontierTests.BooleanAnalysisSpectralNorm

end
