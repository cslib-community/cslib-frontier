/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.BiasedFourier
import Mathlib.Algebra.BigOperators.Fin

/-! # Tests for `p`-biased Fourier analysis

At rate `1/4` a bit has variance `3/4` and basis values `√(1/3)` and `-√3`, with mean `0` and second
moment `1`, and exchanging the rate with `3/4` complements the bit. The biased characters are
orthonormal, the point indicator and a function expand in them, the coefficient on `∅` is the mean
and on `{0}` is `σ` times a mean derivative, and a dictator has coefficients `μ` and `σ`.
Conditioning on one bit computes a mean, and pairing across a bit computes the centered second
moment of a dictator. Parseval for a dictator gives `σ² = 1 - μ²`, and
Plancherel for two dictators gives their correlation `μ²`. The covariance and variance identities
give a bit's variance `p - p²` and a dictator's variance `1 - μ²`, which is its biased Fourier
weight `σ²` off `∅`, and two dictators on different bits have covariance `0`. At rate `1/2` the
biased characters and coefficients are the usual ones.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisBiasedFourier

open Cslib Cslib.BitString Finset

/-- A bit of rate `1/4` read as a sign has variance `3/4`. -/
example : biasedStd (1 / 4) ^ 2 = 3 / 4 := by
  rw [biasedStd_sq (by norm_num) (by norm_num)]
  norm_num

/-- The standard deviation at rate `1/3` is positive. -/
example : 0 < biasedStd (1 / 3) :=
  biasedStd_pos (by norm_num) (by norm_num)

/-- At rate `1/4` the basis function at `true` is `-√3`. -/
example : biasedBasis (1 / 4) true = -√3 := by
  rw [biasedBasis_true (by norm_num) (by norm_num)]
  norm_num

/-- At rate `1/4` the basis function at `false` is `√(1/3)`. -/
example : biasedBasis (1 / 4) false = √(1 / 3) := by
  rw [biasedBasis_false (by norm_num) (by norm_num)]
  norm_num

/-- At rate `3/4` the basis function at `false` is `√3`, the negative of its value at `true` at
rate `1/4`. -/
example : biasedBasis (3 / 4) false = √3 := by
  have h := biasedBasis_one_sub (1 / 4) true
  rw [Bool.not_true, biasedBasis_true (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h

/-- At `p = 1/2` the biased basis is the usual sign: `φ(false) = 1`. -/
example : biasedBasis (1 / 2) false = 1 := by
  rw [biasedBasis_false (by norm_num) (by norm_num)]
  norm_num

/-- At rate `1/4`, `φ(true) = -3 φ(false)`, since `φ` has mean zero. -/
example : biasedBasis (1 / 4) true = -3 * biasedBasis (1 / 4) false := by
  have h := biasedBasis_mean (1 / 4)
  linarith

/-- At rate `1/4`, `3 φ(false)² + φ(true)²` is `4`, four times the second moment. -/
example : 3 * biasedBasis (1 / 4) false ^ 2 + biasedBasis (1 / 4) true ^ 2 = 4 := by
  have h := biasedBasis_sq_mean (p := 1 / 4) (by norm_num) (by norm_num)
  norm_num at h
  linarith

/-- Disagreeing bits at rate `1/4`: on a one-bit cube the point indicator at `true`, evaluated at
`false`, is `π(true) (1 + φ(false) φ(true)) = 0`. -/
example : (1 / 4 : ℝ) * (1 + biasedBasis (1 / 4) false * biasedBasis (1 / 4) true) = 0 := by
  have h := bernoulliWeight_mul_sum_biasedChi_mul_biasedChi (p := 1 / 4) (by norm_num)
    (by norm_num) (fun _ : Fin 1 => false) (fun _ => true)
  have hU : (univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hne : (fun _ : Fin 1 => false) ≠ fun _ => true := fun he => by simpa using congrFun he 0
  rw [hU, sum_pair (by decide)] at h
  simpa [bernoulliWeight, biasedChi, hne] using h

/-- The biased character of both coordinates at the all-`true` string, at rate `1/4`, is
`(-√3)² = 3`. -/
example : biasedChi (1 / 4) ({0, 1} : Finset (Fin 2)) (fun _ => true) = 3 := by
  rw [biasedChi_eq_prod_univ, Fin.prod_univ_two]
  simp only [mem_insert, mem_singleton, true_or, or_true, ite_true]
  rw [biasedBasis_true (by norm_num) (by norm_num)]
  norm_num

/-- Distinct biased characters are orthogonal at rate `1/3`. -/
example : bernoulliAverage (1 / 3)
    (fun x : Fin 3 → Bool => biasedChi (1 / 3) {0} x * biasedChi (1 / 3) {0, 1} x) = 0 := by
  rw [bernoulliAverage_biasedChi_mul_biasedChi (by norm_num) (by norm_num), ite_eq_right]
  decide

/-- A biased character has norm one. -/
example (S : Finset (Fin 3)) :
    bernoulliAverage (1 / 3) (fun x => biasedChi (1 / 3) S x * biasedChi (1 / 3) S x) = 1 := by
  rw [bernoulliAverage_biasedChi_mul_biasedChi (by norm_num) (by norm_num), ite_eq_left rfl]

/-- The indicator of a point vanishes at another point. -/
example : bernoulliWeight (1 / 3) (fun _ : Fin 2 => false) *
    ∑ S : Finset (Fin 2), biasedChi (1 / 3) S (fun i => decide (i = 0)) *
      biasedChi (1 / 3) S (fun _ => false) = 0 := by
  rw [bernoulliWeight_mul_sum_biasedChi_mul_biasedChi (by norm_num) (by norm_num), ite_eq_right]
  intro h
  simpa using congrFun h 0

/-- The biased Fourier expansion at rate `1/4` recovers the indicator of bit `0` at a string where
that bit is set. -/
example : ∑ S, biasedFourierCoeff (1 / 4) (fun x : Fin 2 → Bool => bitVal ℝ (x 0)) S *
    biasedChi (1 / 4) S (fun i => decide (i = 0)) = 1 := by
  rw [sum_biasedFourierCoeff_mul_biasedChi (by norm_num) (by norm_num)]
  simp

/-- Unfolding the coefficient on `∅`, where the character is `1`: the indicator of bit `0` has
mean `1/3` at rate `1/3`. -/
example : biasedFourierCoeff (1 / 3) (fun x : Fin 2 → Bool => if x 0 then 1 else 0) ∅ = 1 / 3 := by
  unfold biasedFourierCoeff
  simp only [biasedChi_empty, mul_one]
  exact bernoulliAverage_coordinate _ _

/-- Unfolding a singleton character gives the basis function of its coordinate. -/
example (p : ℝ) (x : Fin 2 → Bool) : biasedChi p {0} x = biasedBasis p (x 0) := by
  rw [biasedChi, prod_singleton]

/-- The coefficient on `∅` of the bit-`0` indicator read as `0` or `1` is its mean `p`. -/
example (p : ℝ) : biasedFourierCoeff p (fun x : Fin 2 → Bool => bitVal ℝ (x 0)) ∅ = p := by
  rw [biasedFourierCoeff_empty]
  simpa [bitVal] using bernoulliAverage_coordinate (ι := Fin 2) p 0

/-- The bit-`0` indicator read as `0` or `1` has derivative `-1/2` in bit `0`, so its coefficient on
`{0}` is `-σ/2`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    biasedFourierCoeff p (fun x : Fin 2 → Bool => bitVal ℝ (x 0)) {0} = -biasedStd p / 2 := by
  have h : derivative 0 (fun x : Fin 2 → Bool => bitVal ℝ (x 0)) = fun _ => -1 / 2 := by
    funext x
    norm_num [derivative, bitVal]
  rw [biasedFourierCoeff_singleton hp hp1, h, bernoulliAverage_const]
  ring

/-- Pairing across bit `0`: the dictator read as a sign has derivative `1` in its bit, so its
centered sign has expectation `4p(1 - p) = 1 - μ²`, for every `p`. -/
example (p : ℝ) : (bernoulliAverage p fun x : Fin 2 → Bool =>
    signVal (x 0) * (signVal (x 0) - (1 - 2 * p))) = 4 * p * (1 - p) := by
  have h : derivative 0 (fun x : Fin 2 → Bool => signVal (x 0)) = fun _ => 1 := by
    funext x
    norm_num [derivative]
  rw [bernoulliAverage_mul_signVal_sub, h, bernoulliAverage_const, mul_one]

/-- Conditioning on bit `0`: the product of two bits read as `0` or `1` has mean `p²`. -/
example (p : ℝ) :
    bernoulliAverage p (fun x : Fin 2 → Bool => bitVal ℝ (x 0) * bitVal ℝ (x 1)) = p * p := by
  rw [bernoulliAverage_eq_bernoulliAverage_update p 0]
  simp only [Function.update_self, bitVal, Bool.false_eq_true, ite_false, ite_true, zero_mul,
    one_mul, mul_zero, zero_add, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rw [bernoulliAverage_const_mul, bernoulliAverage_coordinate]

/-- The mean of a dictator at rate `p` is `μ = 1 - 2p`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    biasedFourierCoeff p (fun x : Fin 3 → Bool => signVal (x 1)) ∅ = 1 - 2 * p := by
  rw [biasedFourierCoeff_dictator hp hp1]
  simp

/-- A dictator's coefficient on its own coordinate is `σ`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    biasedFourierCoeff p (fun x : Fin 3 → Bool => signVal (x 1)) {1} = biasedStd p := by
  rw [biasedFourierCoeff_dictator hp hp1]
  simp

/-- A dictator has no weight on a set of two coordinates. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    biasedFourierCoeff p (fun x : Fin 3 → Bool => signVal (x 1)) {0, 1} = 0 := by
  rw [biasedFourierCoeff_dictator hp hp1, ite_eq_right (by decide), ite_eq_right (by decide),
    add_zero]

/-- Parseval's identity for a dictator gives `σ² = 1 - μ²`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : biasedStd p ^ 2 = 1 - (1 - 2 * p) ^ 2 := by
  have h := bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq hp hp1
    fun x : Fin 2 → Bool => signVal (x 0)
  simp only [sq, signVal_mul_self, bernoulliAverage_const, biasedFourierCoeff_dictator hp hp1,
    add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, sum_add_distrib, sum_ite_eq',
    mem_univ, ite_true] at h
  simp [(Finset.singleton_nonempty (0 : Fin 2)).ne_empty.symm] at h
  linarith

/-- Plancherel's identity for two dictators gives their correlation `μ²`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    bernoulliAverage p (fun x : Fin 2 → Bool => signVal (x 0) * signVal (x 1)) =
      (1 - 2 * p) ^ 2 := by
  rw [bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul hp hp1]
  simp only [biasedFourierCoeff_dictator hp hp1, add_mul, mul_add, ite_mul, mul_ite, zero_mul,
    mul_zero, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  simp [(Finset.singleton_nonempty (0 : Fin 2)).ne_empty.symm]
  ring

/-- The covariance identity: a bit read as `0` or `1` has variance `p - p²`, for every `p`. -/
example (p : ℝ) : bernoulliAverage p (fun x : Fin 2 → Bool =>
    (bitVal ℝ (x 0) - bernoulliAverage p fun y : Fin 2 → Bool => bitVal ℝ (y 0)) *
      (bitVal ℝ (x 0) - bernoulliAverage p fun y : Fin 2 → Bool => bitVal ℝ (y 0))) =
      p - p * p := by
  have h : bernoulliAverage p (fun y : Fin 2 → Bool => bitVal ℝ (y 0)) = p := by
    simpa [bitVal] using bernoulliAverage_coordinate (ι := Fin 2) p 0
  have hsq : (fun x : Fin 2 → Bool => bitVal ℝ (x 0) * bitVal ℝ (x 0)) =
      fun x => if x 0 then 1 else 0 := by
    funext x
    cases x 0 <;> simp [bitVal]
  rw [bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage, h, hsq,
    bernoulliAverage_coordinate]

/-- The variance identity: a dictator read as a sign has variance `1 - μ²`, for every `p`. -/
example (p : ℝ) : bernoulliAverage p (fun x : Fin 2 → Bool =>
    (signVal (x 0) - bernoulliAverage p fun y : Fin 2 → Bool => signVal (y 0)) ^ 2) =
      1 - bernoulliAverage p (fun y : Fin 2 → Bool => signVal (y 0)) ^ 2 := by
  rw [bernoulliAverage_sub_bernoulliAverage_sq]
  simp [sq, signVal_mul_self, bernoulliAverage_const]

/-- The variance of a dictator in the biased Fourier basis is its weight `σ²` on `{0}`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : bernoulliAverage p (fun x : Fin 2 → Bool =>
    (signVal (x 0) - bernoulliAverage p fun y : Fin 2 → Bool => signVal (y 0)) ^ 2) =
      biasedStd p ^ 2 := by
  rw [bernoulliAverage_sub_bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq hp hp1, sum_filter,
    Fintype.sum_eq_single {0} fun S hS => ?_]
  · simp [biasedFourierCoeff_dictator hp hp1]
  · by_cases h : S = ∅ <;> simp [h, hS, biasedFourierCoeff_dictator hp hp1]

/-- Two dictators on different bits have covariance `0` in the biased Fourier basis: their
coefficients off `∅` sit on `{0}` and `{1}`. -/
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : bernoulliAverage p (fun x : Fin 2 → Bool =>
    (signVal (x 0) - bernoulliAverage p fun y : Fin 2 → Bool => signVal (y 0)) *
      (signVal (x 1) - bernoulliAverage p fun y : Fin 2 → Bool => signVal (y 1))) = 0 := by
  rw [bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum hp hp1]
  refine sum_eq_zero fun S hS => ?_
  rw [biasedFourierCoeff_dictator hp hp1, biasedFourierCoeff_dictator hp hp1]
  simp only [(mem_filter.1 hS).2, ite_false, zero_add]
  by_cases h0 : S = {0}
  · subst h0
    simp
  · simp [h0]

/-- At `p = 1/2` the biased character of `{0, 2}` at `(true, false, true)` is `(-1)² = 1`. -/
example : biasedChi (1 / 2) ({0, 2} : Finset (Fin 3)) ![true, false, true] = 1 := by
  rw [biasedChi_one_half, chi_eq_prod_signVal]
  simp

/-- At `p = 1/2` a character's biased coefficient on itself is one. -/
example : biasedFourierCoeff (1 / 2) (chi ℝ ({0} : Finset (Fin 2))) {0} = 1 := by
  rw [biasedFourierCoeff_one_half, fourierCoeff_chi, ite_eq_left_iff]
  exact fun h => absurd rfl h

end CslibFrontierTests.BooleanAnalysisBiasedFourier
