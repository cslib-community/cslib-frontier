/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.Regularity
public import CslibFrontier.Probability.Fooling

/-! # Tests for regular functions

Constants are `0`-regular and nonconstant characters are not. A character `χ_S` with `S`
nonempty is `1`-regular but not `1 / 2`-regular, so its fourth spectral moment above the mean is
at most its variance and at least `(1 / 2) ^ 4`. Every function is `‖f‖₁`-regular; for the
indicator of a point of three bits this is `1/8`. The uniform distribution, being `0`-biased, fools
every function exactly. -/

public section

namespace CslibFrontierTests.BooleanAnalysisRegularity

open Cslib Cslib.BitString Cslib.Probability Finset
open scoped BigOperators

/-- A constant function is `0`-regular. -/
theorem isFourierRegular_const (c : ℝ) : IsFourierRegular 0 (fun _ : Fin 3 → Bool => c) :=
  isFourierRegular_zero_iff.2 ⟨c, rfl⟩

/-- A character of a nonempty set is not constant, since it is not `0`-regular. -/
theorem chi_ne_const : ¬ ∃ c, chi ℝ ({0} : Finset (Fin 3)) = fun _ => c := fun h =>
  not_isFourierRegular_chi (singleton_nonempty 0) zero_lt_one (isFourierRegular_zero_iff.2 h)

/-- A character is `1`-regular. -/
theorem isFourierRegular_one_chi (S : Finset (Fin 3)) : IsFourierRegular 1 (chi ℝ S) :=
  fun T _ => by
    rw [fourierCoeff_chi]
    split_ifs <;> norm_num

/-- So its fourth spectral moment above the mean is at most its variance. -/
theorem sum_fourierCoeff_chi_pow_four_sub_le :
    ∑ S, fourierCoeff (chi ℝ ({0} : Finset (Fin 3))) S ^ 4 -
        (𝔼 x, chi ℝ ({0} : Finset (Fin 3)) x) ^ 4 ≤
      𝔼 x, (chi ℝ ({0} : Finset (Fin 3)) x - 𝔼 y, chi ℝ ({0} : Finset (Fin 3)) y) ^ 2 := by
  simpa using sum_fourierCoeff_pow_four_sub_le_of_isFourierRegular (isFourierRegular_one_chi {0})

/-- It is not `1 / 2`-regular, so its fourth spectral moment above the mean is at least
`(1 / 2) ^ 4`. -/
theorem pow_four_le_sum_fourierCoeff_chi_pow_four_sub :
    (1 / 2 : ℝ) ^ 4 ≤ ∑ S, fourierCoeff (chi ℝ ({0} : Finset (Fin 3))) S ^ 4 -
      (𝔼 x, chi ℝ ({0} : Finset (Fin 3)) x) ^ 4 :=
  pow_four_le_sum_fourierCoeff_pow_four_sub_of_not_isFourierRegular (by norm_num)
    (not_isFourierRegular_chi (singleton_nonempty 0) (by norm_num))

/-- The indicator of the point `0` of three bits is `‖f‖₁ = 1/8`-regular. -/
theorem isFourierRegular_ite_eq_zero :
    IsFourierRegular (1 / 8) fun x : Fin 3 → Bool => if x = 0 then (1 : ℝ) else 0 := by
  have h := isFourierRegular_expect_abs fun x : Fin 3 → Bool => if x = 0 then (1 : ℝ) else 0
  have he : 𝔼 x : Fin 3 → Bool, |if x = 0 then (1 : ℝ) else 0| = 1 / 8 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [apply_ite abs, abs_one, abs_zero, sum_ite_eq', mem_univ, ite_true,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num
  rwa [he] at h

/-- The uniform distribution, being `0`-biased, fools every function exactly. -/
theorem fools_uniformOfFintype_zero (f : (Fin 3 → Bool) → ℝ) :
    Fools (PMF.uniformOfFintype (Fin 3 → Bool)) 0 f := by
  simpa using isSmallBias_uniformOfFintype.fools le_rfl f

end CslibFrontierTests.BooleanAnalysisRegularity

end
