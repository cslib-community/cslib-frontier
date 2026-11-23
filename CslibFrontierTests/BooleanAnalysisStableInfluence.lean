/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.CoordinateOperators
public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence

/-! # Coordinate operators and stable influences on small cubes

The character `χ_{0,1}` of two of three coordinates is killed by the expectation over coordinate
`0` and kept by the coordinate Laplacian, and the Laplacian scales it by two, so
`⟨χ, L χ⟩ = I[χ] = 2`. Its `ρ`-stable influence at coordinate `0` is `ρ`, interpolating between
zero at `ρ = 0` and its influence one at `ρ = 1`. Its noise stability `ρ ^ 2` has derivative
`2ρ`, which is its total `ρ`-stable influence (Fact 2.53): zero, its level-one weight, at `ρ = 0`
and two, its total influence, at `ρ = 1` (Proposition 2.51). Proposition 2.54 applies to a
dictator at `δ = ε = 1 / 2`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisStableInfluence

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The character of the first two of three coordinates. -/
noncomputable abbrev χ₀₁ : (Fin 3 → Bool) → ℝ := chi ℝ ({0, 1} : Finset (Fin 3))

-- `E₀` kills `χ_{0,1}` and `L₀` keeps it.
example : fourierCoeff (coordExpect 0 χ₀₁) {0, 1} = 0 ∧
    fourierCoeff (coordLaplacian 0 χ₀₁) {0, 1} = 1 := by
  rw [fourierCoeff_coordExpect, fourierCoeff_coordLaplacian, fourierCoeff_chi]
  simp

-- `⟨χ, L χ⟩` is the total influence `2` of the character.
example : 𝔼 x, χ₀₁ x * laplacian χ₀₁ x = 2 := by
  rw [expect_mul_laplacian, totalInfluence_chi]
  rfl

-- The `ρ`-stable influence of coordinate `0` on `χ_{0,1}` is `ρ`.
example (ρ : ℝ) : stableInfluence ρ 0 χ₀₁ = ρ := by
  rw [stableInfluence_eq_sum]
  simp only [fourierCoeff_chi, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp

-- Proposition 2.54 for a dictator at `δ = ε = 1 / 2`.
example : (1 / 2 : ℝ) * (1 / 2) *
    #{i | (1 / 2 : ℝ) ≤ stableInfluence (1 - 1 / 2) i (fun x : Fin 3 → Bool => signVal (x 0))} ≤
      1 :=
  mul_card_filter_le_stableInfluence_signVal_le_one (by norm_num) (by norm_num) _ _

-- The noise stability of `χ_{0,1}` is `ρ ^ 2`.
example (ρ : ℝ) : noiseStability ρ χ₀₁ = ρ ^ 2 := by
  rw [noiseStability_eq_sum, sum_eq_single ({0, 1} : Finset (Fin 3))]
  · simp [fourierCoeff_chi, show #({0, 1} : Finset (Fin 3)) = 2 from rfl]
  · intro S _ hS
    simp [fourierCoeff_chi, Ne.symm hS]
  · simp

/-- The total `ρ`-stable influence of `χ_{0,1}` is `2ρ`. -/
theorem totalStableInfluence_χ₀₁ (ρ : ℝ) : totalStableInfluence ρ χ₀₁ = 2 * ρ := by
  have hc : #({0, 1} : Finset (Fin 3)) = 2 := rfl
  rw [totalStableInfluence_eq_sum, sum_eq_single ({0, 1} : Finset (Fin 3))]
  · simp [fourierCoeff_chi, hc]
  · intro S _ hS
    simp [fourierCoeff_chi, Ne.symm hS]
  · simp

/-- `χ_{0,1}` has no Fourier weight at degree one. -/
theorem levelWeight_one_χ₀₁ : levelWeight 1 χ₀₁ = 0 := by
  rw [levelWeight]
  refine sum_eq_zero fun S hS => ?_
  have hS' : ({0, 1} : Finset (Fin 3)) ≠ S := by
    rintro rfl
    simp at hS
  simp [fourierCoeff_chi, hS']

-- Fact 2.53 for `χ_{0,1}`: `d/dρ Stab_ρ[χ_{0,1}] = 2ρ`, in `deriv` form.
example (ρ : ℝ) : deriv (fun r => noiseStability r χ₀₁) ρ = 2 * ρ := by
  rw [(hasDerivAt_noiseStability χ₀₁ ρ).deriv, totalStableInfluence_χ₀₁]

-- Proposition 2.51 for `χ_{0,1}`: the derivative is `W¹ = 0` at `0` and `I = 2` at `1`.
example : HasDerivAt (fun r => noiseStability r χ₀₁) 0 0 :=
  levelWeight_one_χ₀₁ ▸ hasDerivAt_noiseStability_zero χ₀₁

example : HasDerivAt (fun r => noiseStability r χ₀₁) 2 1 := by
  have h := hasDerivAt_noiseStability_one χ₀₁
  rw [totalInfluence_chi] at h
  exact_mod_cast h

end CslibFrontierTests.BooleanAnalysisStableInfluence
