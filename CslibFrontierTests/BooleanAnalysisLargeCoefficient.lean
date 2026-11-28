/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.LargeCoefficient
import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta
import CslibFrontier.Foundations.BooleanAnalysis.Variance

/-! # Tests for a large low-degree Fourier coefficient

A constant has total influence `0`, so the spectral step of Friedgut's junta theorem must take the
empty set of coordinates: for every `ε > 0`, the Fourier weight on the nonempty sets is at most
`ε`. The dictator `x ↦ x 0` on one bit has variance `1` and total influence at most `1`, so
Corollary 9.32 applies to it with `K = 1` and gives a nonempty set of at most `8` coordinates with
a squared coefficient at least `1 / (4 (256/9 · 81 ^ 8 + 1) ^ 8)`. -/

public section

namespace CslibFrontierTests.BooleanAnalysisLargeCoefficient

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The constant `false` on two bits, read as signs, has total influence `0`. -/
theorem totalInfluence_const_false :
    totalInfluence (fun _ : Fin 2 → Bool => signVal false) ≤ 0 := by
  rw [totalInfluence_signVal]
  simp

/-- The spectral step for a constant: its set of coordinates has at most `0` elements, so the
Fourier weight on the sets that are not subsets of `∅`, the nonempty sets, is at most every
`ε > 0`. -/
theorem sum_not_subset_empty_fourierCoeff_sq_const_le {ε : ℝ} (hε : 0 < ε) :
    ∑ S with ¬S ⊆ ∅, fourierCoeff (fun _ : Fin 2 → Bool => signVal false) S ^ 2 ≤ ε := by
  obtain ⟨J, hJ, hw⟩ := exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le
    (fun _ : Fin 2 → Bool => false) hε totalInfluence_const_false
  have hJ0 : J = ∅ := card_eq_zero.1 (by
    have : (#J : ℝ) ≤ 0 := hJ.trans_eq (by simp)
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _))
  rwa [hJ0] at hw

/-- The dictator `x ↦ x 0` on one bit, read as signs, has variance `1`. -/
theorem variance_dictator :
    𝔼 x : Fin 1 → Bool, (signVal (x 0) - 𝔼 y : Fin 1 → Bool, signVal (y 0)) ^ 2 = 1 := by
  rw [expect_sub_expect_sq_signVal]
  simp only [← chi_singleton, expect_chi, (singleton_nonempty _).ne_empty, ↓reduceIte]
  norm_num

/-- The dictator `x ↦ x 0` on one bit has total influence at most `1`. -/
theorem totalInfluence_dictator_le_one :
    totalInfluence (fun x : Fin 1 → Bool => signVal (x 0)) ≤ 1 := by
  have h := totalInfluence_le_mul_expect_sq (fun x : Fin 1 → Bool => signVal (x 0))
  simp only [sq, signVal_mul_self, Fintype.card_fin, Nat.cast_one, one_mul] at h
  rwa [expect_const univ_nonempty] at h

/-- Corollary 9.32 for the dictator on one bit with `K = 1`: some nonempty set of at most `8`
coordinates has squared coefficient at least `1 / (4 (256/9 · 81 ^ 8 + 1) ^ 8)`. -/
theorem exists_le_fourierCoeff_sq_dictator :
    ∃ S : Finset (Fin 1), S ≠ ∅ ∧ (#S : ℝ) ≤ 8 ∧
      1 / (4 * (256 / 9 * (81 : ℝ) ^ 8 + 1) ^ 8) ≤
        fourierCoeff (fun x : Fin 1 → Bool => signVal (x 0)) S ^ 2 := by
  obtain ⟨S, hS, hcard, hcoeff⟩ := exists_le_fourierCoeff_sq_of_le_expect_sub_expect_sq
    (fun x : Fin 1 → Bool => x 0) (by rw [variance_dictator]; norm_num)
    totalInfluence_dictator_le_one
  refine ⟨S, hS, by simpa using hcard, ?_⟩
  simpa using hcoeff

end CslibFrontierTests.BooleanAnalysisLargeCoefficient
