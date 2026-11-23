/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.DeterministicEstimation
public import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
public import CslibFrontier.Probability.Fooling
import CslibFrontier.Probability.PMF.Expect

/-! # Tests for deterministic estimation from small-bias sample spaces

The whole cube, listed once, is a `0`-biased sample space, so its estimates are exact. A sample
space with a single seed is a point mass: its estimates are values at that point. On a thousand
bits, a sample space obtained from the powering construction estimates the coefficient of a
character to within `1/10` from at most `4 (1000 / (1/10) + 1)²` queries, and it estimates a bucket
that contains the character to at least `9/10`. The estimates read only the listed points. -/

public section

namespace CslibFrontierTests.BooleanAnalysisDeterministicEstimation

open Cslib Cslib.BitString Cslib.Probability Finset
open scoped BigOperators

/-- The whole cube, listed once, is `0`-biased. -/
theorem isSmallBias_id :
    IsSmallBias 0 ((PMF.uniformOfFintype (Fin 3 → Bool)).map id) := by
  rw [PMF.map_id]
  exact isSmallBias_uniformOfFintype

/-- The point `0` is listed by the whole cube. -/
theorem zero_mem_sampleSpacePoints_id :
    (0 : Fin 3 → Bool) ∈ sampleSpacePoints (id : (Fin 3 → Bool) → _) :=
  mem_sampleSpacePoints id 0

/-- A single seed mapped to `0` is the point mass at `0`: expectations are values at `0`. -/
theorem sum_uniformOfFintype_map_const (F : (Fin 3 → Bool) → ℝ) :
    ∑ x, (((PMF.uniformOfFintype Unit).map fun _ => (0 : Fin 3 → Bool)) x).toReal * F x = F 0 := by
  rw [Probability.PMF.sum_uniformOfFintype_map_mul]
  simp

/-- With a single seed mapped to `0`, the coefficient estimate is `f 0`. -/
theorem sampleSpaceCoeff_const (f : (Fin 3 → Bool) → ℝ) (U : Finset (Fin 3)) :
    sampleSpaceCoeff (fun _ : Unit => (0 : Fin 3 → Bool)) f U = f 0 := by
  rw [sampleSpaceCoeff_def]
  simp

/-- With a single seed mapped to `0` in both sample spaces, the bucket-weight estimate is
`f 0 ^ 2`. -/
theorem sampleSpaceBucketWeight_const (f : (Fin 3 → Bool) → ℝ) (J S : Finset (Fin 3)) :
    sampleSpaceBucketWeight (fun _ : Unit => (0 : Fin 3 → Bool)) (fun _ : Unit => 0) f J S =
      f 0 ^ 2 := by
  rw [sampleSpaceBucketWeight_def]
  simp [sampleSpaceCoeff_const, Finset.piecewise_same]

/-- A coefficient estimate of a character is at most one in absolute value. -/
theorem abs_sampleSpaceCoeff_chi_le_one {σ : Type*} [Fintype σ] (g : σ → Fin 3 → Bool)
    (T U : Finset (Fin 3)) : |sampleSpaceCoeff g (chi ℝ T) U| ≤ 1 :=
  abs_sampleSpaceCoeff_le_one g (fun x => (abs_chi T x).le) U

/-- With the whole cube as sample space the coefficient estimate is exact. -/
theorem sampleSpaceCoeff_id (f : (Fin 3 → Bool) → ℝ) (U : Finset (Fin 3)) :
    sampleSpaceCoeff id f U = fourierCoeff f U := by
  have h := abs_sampleSpaceCoeff_sub_fourierCoeff_le le_rfl isSmallBias_id f U
  rw [mul_zero] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-- The bucket-weight estimate is exact too, for functions bounded by one. -/
theorem sampleSpaceBucketWeight_id (f : (Fin 3 → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (J S : Finset (Fin 3)) : sampleSpaceBucketWeight id id f J S = bucketWeight f J S := by
  have h := abs_sampleSpaceBucketWeight_sub_bucketWeight_le le_rfl le_rfl isSmallBias_id
    isSmallBias_id hf J S
  simp only [mul_zero, add_zero] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-- It reads `|τ| |σ| = 64` points. -/
theorem length_sampleSpaceBucketPoints_id (J : Finset (Fin 3)) :
    (sampleSpaceBucketPoints (id : (Fin 3 → Bool) → _) id J).length = 64 := by
  rw [length_sampleSpaceBucketPoints]
  simp

/-- The coefficient estimate reads only the listed points: functions agreeing there have the
same estimate. -/
theorem sampleSpaceCoeff_ite {σ : Type*} [Fintype σ] (g : σ → Fin 3 → Bool)
    (U : Finset (Fin 3)) :
    sampleSpaceCoeff g (fun x => if x ∈ sampleSpacePoints g then chi ℝ U x else 0) U =
      sampleSpaceCoeff g (chi ℝ U) U :=
  sampleSpaceCoeff_congr g (fun _ hx => ite_eq_left hx) U

/-- So does the bucket-weight estimate. -/
theorem sampleSpaceBucketWeight_ite {σ τ : Type*} [Fintype σ] [Fintype τ]
    (g : σ → Fin 3 → Bool) (h : τ → Fin 3 → Bool) (J S : Finset (Fin 3)) :
    sampleSpaceBucketWeight g h
        (fun x => if x ∈ sampleSpaceBucketPoints g h J then chi ℝ S x else 0) J S =
      sampleSpaceBucketWeight g h (chi ℝ S) J S :=
  sampleSpaceBucketWeight_congr g h (fun _ hx => ite_eq_left hx) S

/-- On a thousand bits, a small-bias sample space estimates a character's coefficient to
`1/10`. -/
theorem exists_abs_sampleSpaceCoeff_chi_sub_one_le (T : Finset (Fin 1000)) :
    ∃ (m : ℕ) (g : BitString (2 * m) → BitString 1000),
      ((sampleSpacePoints g).length : ℝ) ≤ 4 * (1000 * 1 / (1 / 10) + 1) ^ 2 ∧
        |sampleSpaceCoeff g (chi ℝ T) T - 1| ≤ 1 / 10 := by
  obtain ⟨m, g, hcard, hg⟩ := exists_abs_sampleSpaceCoeff_sub_fourierCoeff_le 1000 (s := 1)
    (ε := 1 / 10) zero_le_one (by norm_num)
  refine ⟨m, g, by rwa [length_sampleSpacePoints], ?_⟩
  have h := hg (chi ℝ T) (sum_abs_fourierCoeff_chi T).le T
  rwa [fourierCoeff_chi, ite_eq_left rfl] at h

/-- The bucket-weight estimator finds the bucket of a character: its estimate is at least
`9/10`. -/
theorem exists_nine_div_ten_le_sampleSpaceBucketWeight_chi (T J : Finset (Fin 1000)) :
    ∃ (m : ℕ) (g : BitString (2 * m) → BitString 1000),
      9 / 10 ≤ sampleSpaceBucketWeight g g (chi ℝ T) J (T ∩ J) := by
  obtain ⟨m, g, -, hg⟩ := exists_abs_sampleSpaceBucketWeight_sub_bucketWeight_le 1000 (s := 1)
    (ε := 1 / 10) zero_le_one (by norm_num)
  refine ⟨m, g, ?_⟩
  have h := hg (chi ℝ T) (fun x => (abs_chi T x).le) (sum_abs_fourierCoeff_chi T).le J (T ∩ J)
  have hw := sq_fourierCoeff_le_bucketWeight (chi ℝ T) J T
  rw [fourierCoeff_chi, ite_eq_left rfl, one_pow] at hw
  linarith [(abs_le.1 h).1]

end CslibFrontierTests.BooleanAnalysisDeterministicEstimation

end
