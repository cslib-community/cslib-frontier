/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.BooleanAnalysis.CentralLimit
public import CslibFrontier.Foundations.BooleanAnalysis.HammingBallWeight
public import Mathlib.Analysis.Real.Pi.Bounds
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Probability.Gaussian.CDF

/-! # The degree-one weight of Hamming balls

On two bits at `t = 0` the Hamming ball is the single point `(1, 1)`. The exact identity
`W¹[f] = E[f(x) ∑ᵢ xᵢ / √n]²` gives `W¹ = 1 / 8`, as do the two degree-one coefficients `1 / 4`
computed directly. The limit `W¹[fₙ] → φ(t)²` is `1 / (2π)` at `t = 0` and `e⁻¹ / (2π)` at
`t = 1`. The central limit theorem on the cube applies to `z - |z|`, which is unbounded below and
of at most linear growth, and `E[|∑ᵢ xᵢ / √n|] → √(2 / π)` keeps it eventually below `1`. At
`t = 0` the mean tends to `1 / 2`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisHammingBallWeight

open Cslib.BitString Filter Finset Topology ProbabilityTheory Real MeasureTheory
open scoped BigOperators

-- The exact identity at `n = 2`, `t = 0`: the ball is the point `(1, 1)`, so `W¹ = 2 · (1/4)²`.
example : (levelWeight 1 fun x : Fin 2 → Bool =>
    if (0 : ℝ) < (√2)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) = 1 / 8 := by
  have h := levelWeight_one_hammingBall 2 0
  push_cast at h
  rw [h]
  have h2 : (0 : ℝ) < (√2)⁻¹ := by positivity
  have h2' : ¬ (√2)⁻¹ * 2 < (0 : ℝ) := not_lt.2 (by positivity)
  simp only [Fin.sum_univ_two, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num [h2.not_gt, h2', div_pow]

-- The same weight computed directly from the two degree-one coefficients, each `1 / 4`.
example : (levelWeight 1 fun x : Fin 2 → Bool =>
    if (0 : ℝ) < (√2)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) = 1 / 8 := by
  have h2 : (0 : ℝ) < (√2)⁻¹ := by positivity
  have h2' : ¬ (√2)⁻¹ * 2 < (0 : ℝ) := not_lt.2 (by positivity)
  simp only [levelWeight_one, Cslib.BitString.fourierCoeff, chi_singleton, Fin.sum_univ_two,
    Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num [h2.not_gt, h2']

-- At `t = 0` the degree-one weight tends to `φ(0)² = 1 / (2π)`.
example : Tendsto (fun n : ℕ => levelWeight 1 fun x : Fin n → Bool =>
    if (0 : ℝ) < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) atTop (𝓝 (1 / (2 * π))) := by
  convert tendsto_levelWeight_one_hammingBall 0 using 2
  rw [gaussianPDFReal_def]
  simp [mul_pow, Real.sq_sqrt pi_pos.le, mul_comm]

-- At `t = 1` the degree-one weight tends to `φ(1)² = e⁻¹ / (2π)`.
example : Tendsto (fun n : ℕ => levelWeight 1 fun x : Fin n → Bool =>
    if (1 : ℝ) < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) atTop
    (𝓝 (exp (-1) / (2 * π))) := by
  convert tendsto_levelWeight_one_hammingBall 1 using 2
  rw [gaussianPDFReal_def]
  simp only [sub_zero, one_pow, NNReal.coe_one, mul_one, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * π), ← Real.exp_natCast_mul]
  rw [div_eq_inv_mul]
  norm_num

-- At `t = 0` the ball is half the cube in the limit: the mean tends to `1 - Φ(0) = 1 / 2`.
example : Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool,
    if (0 : ℝ) < (√n)⁻¹ * ∑ i, signVal (x i) then (1 : ℝ) else 0) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_expect_hammingBall 0
  rwa [cdf_gaussianReal_zero_zero one_ne_zero, show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num] at h

-- The central limit theorem on the cube for `z ↦ z - |z| = 2 min z 0`, which is unbounded below
-- and of at most linear growth.
example : Tendsto (fun n : ℕ => 𝔼 x : Fin n → Bool,
    ((√n)⁻¹ * ∑ i, signVal (x i) - |(√n)⁻¹ * ∑ i, signVal (x i)|)) atTop
    (𝓝 (∫ z, (z - |z|) ∂gaussianReal 0 1)) :=
  tendsto_expect_inv_sqrt_mul_sum_signVal_of_sq_le (h := fun z => z - |z|) (by fun_prop)
    (a := 4) (b := 0) fun z => by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]; nlinarith [sq_nonneg z]
      · rw [abs_of_nonpos hz]; nlinarith [sq_nonneg z]

-- Since the mean absolute value of the normalized sign sum tends to `√(2 / π) < 1`, equation
-- (5.4), it is eventually below `1`.
example : ∀ᶠ n : ℕ in atTop, 𝔼 x : Fin n → Bool, |(√n)⁻¹ * ∑ i, signVal (x i)| < 1 := by
  have h : √(2 / π) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one pi_pos]
    linarith [pi_gt_three]
  exact tendsto_expect_abs_inv_sqrt_mul_sum_signVal.eventually (gt_mem_nhds h)

end CslibFrontierTests.BooleanAnalysisHammingBallWeight
