/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Exponential.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Polynomial bounds on the real exponential

Two Taylor-type bounds on the real exponential for nonnegative arguments. They are the scalar
inequalities behind multiplicative Chernoff bounds and the Johnson–Lindenstrauss lemma.

* `exp (-x) ≤ 1 - x + x² / 2` (`Real.exp_neg_le_one_sub_add_sq_div_two`): multiply by
  `exp x ≥ 1 + x + x² / 2`.
* `1 + x ≤ exp (x - x² / 2 + x³ / 3)` (`Real.one_add_le_exp_sub_sq_div_two_add_cube_div_three`),
  equivalently `log (1 + x) ≤ x - x² / 2 + x³ / 3`. The exponent `v` is nonnegative. The degree-four
  Taylor polynomial `1 + v + v² / 2 + v³ / 6 + v⁴ / 24` is at most `exp v` and already dominates
  `1 + x`, by an explicit sum of nonnegative terms.

`CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic` has the weaker
`Real.exp_neg_le_one_sub_add_sq`, `exp (-y) ≤ 1 - y + y²`, valid for all `-1 ≤ y`.

A tail bound `c exp (-(a n))` with `c ≤ K` is at most `δ` once `n ≥ log (K / δ) / a`
(`Real.mul_exp_neg_le_of_log`); this turns Chernoff and Hoeffding bounds into sample sizes.

## Main results

* `Real.exp_neg_le_one_sub_add_sq_div_two`: `exp (-x) ≤ 1 - x + x² / 2` for `0 ≤ x`.
* `Real.one_add_le_exp_sub_sq_div_two_add_cube_div_three`: `1 + x ≤ exp (x - x² / 2 + x³ / 3)` for
  `0 ≤ x`.
* `Real.exp_neg_two_le_one_third`: `exp (-2) ≤ 1 / 3`.
* `Real.two_pow_le_exp`: `2 ^ n ≤ exp n`.
* `Real.exp_le_half_pow`: `exp x ≤ (1 / 2) ^ n` for `x ≤ -n`.
* `Real.one_sub_pow_le_exp`: `(1 - p) ^ R ≤ exp (-c)` for `p ≤ 1` and `c ≤ R p`.
* `Real.pow_le_one_third`: `p ^ k ≤ 1 / 3` for `0 ≤ p ≤ 1 - δ` and `2 ≤ δ k`.
* `Real.mul_exp_neg_le_of_log`: `c exp (-(a n)) ≤ δ` once `c ≤ K` and `log (K / δ) / a ≤ n`, the
  step that turns a tail bound into a sample size.
-/

public section

namespace Real

/-- `exp (-x) ≤ 1 - x + x² / 2` for `0 ≤ x`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq := quadratic_le_exp_of_nonneg hx
  rw [exp_neg, inv_le_iff_one_le_mul₀ (exp_pos x)]
  nlinarith [sq_nonneg x, exp_pos x,
    mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 1 - x + x ^ 2 / 2 by nlinarith)]

/-- `1 + x ≤ exp (x - x² / 2 + x³ / 3)` for `0 ≤ x`; equivalently
`log (1 + x) ≤ x - x² / 2 + x³ / 3`. -/
theorem one_add_le_exp_sub_sq_div_two_add_cube_div_three {x : ℝ} (hx : 0 ≤ x) :
    1 + x ≤ exp (x - x ^ 2 / 2 + x ^ 3 / 3) := by
  have hv0 : 0 ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by nlinarith [sq_nonneg (x - 3 / 4), sq_nonneg x]
  have h := sum_le_exp_of_nonneg hv0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  refine le_trans ?_ h
  -- `1296 (v + v² / 2 + v³ / 6 + v⁴ / 24 - x)` is a sum of nonnegative terms of degree at most 12.
  have h1 : 0 ≤ x ^ 7 * (x - 9 / 4) ^ 2 := by positivity
  have h2 : 0 ≤ x ^ 5 * (x - 1) ^ 2 := by positivity
  have h3 : 0 ≤ x ^ 5 := by positivity
  have h4 : 0 ≤ x ^ 4 := by positivity
  linarith

/-- `exp (-2) ≤ 1 / 3`. -/
theorem exp_neg_two_le_one_third : exp (-2) ≤ 1 / 3 := by
  rw [exp_neg, inv_le_comm₀ (exp_pos 2) (by norm_num)]
  linarith [add_one_le_exp 2]

/-- `2 ^ n ≤ exp n`, since `2 ≤ exp 1`. -/
theorem two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ exp n :=
  (pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp 1]) n).trans_eq
    (by rw [← exp_natCast_mul, mul_one])

/-- `exp x ≤ (1 / 2) ^ n` whenever `x ≤ -n`, since `2 ^ n ≤ exp n`. -/
theorem exp_le_half_pow (n : ℕ) {x : ℝ} (hx : x ≤ -(n : ℝ)) : exp x ≤ (1 / 2 : ℝ) ^ n :=
  calc exp x ≤ exp (-(n : ℝ)) := exp_le_exp.mpr hx
    _ = (exp (n : ℝ))⁻¹ := exp_neg (n : ℝ)
    _ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) (two_pow_le_exp n)
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]

/-- `(1 - p) ^ R ≤ exp (-c)` once `c ≤ R p`. -/
theorem one_sub_pow_le_exp {p c : ℝ} {R : ℕ} (hp1 : p ≤ 1) (hc : c ≤ R * p) :
    (1 - p) ^ R ≤ exp (-c) := by
  calc (1 - p) ^ R ≤ exp (-p) ^ R :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) R
    _ = exp (-(R * p)) := by rw [← exp_natCast_mul]; ring_nf
    _ ≤ exp (-c) := exp_le_exp.mpr (by linarith)

/-- Amplification bound: if `0 ≤ p ≤ 1 - δ` and `2 ≤ δ k`, then `p ^ k ≤ 1 / 3`. -/
theorem pow_le_one_third {p δ : ℝ} {k : ℕ} (hp : 0 ≤ p) (hpδ : p ≤ 1 - δ)
    (hk : 2 ≤ δ * k) : p ^ k ≤ 1 / 3 := by
  have hδ1 : δ ≤ 1 := by linarith
  have hpk : p ^ k ≤ (1 - δ) ^ k := pow_le_pow_left₀ hp hpδ k
  have hpow : (1 - δ) ^ k ≤ exp (-2) :=
    one_sub_pow_le_exp hδ1 (by linarith [mul_comm δ (k : ℝ)])
  exact hpk.trans (hpow.trans exp_neg_two_le_one_third)

/-- **Sample size from a logarithm**: if `c ≤ K`, `0 < K`, `0 < a`, `0 < δ` and
`log (K / δ) / a ≤ n`, then `c * exp (-(a * n)) ≤ δ`. -/
theorem mul_exp_neg_le_of_log {c K n a δ : ℝ}
    (hcK : c ≤ K) (hK : 0 < K) (ha : 0 < a) (hδ : 0 < δ)
    (hn : log (K / δ) / a ≤ n) :
    c * exp (-(a * n)) ≤ δ := by
  have hlog : log (K / δ) ≤ a * n := ((div_le_iff₀ ha).mp hn).trans_eq (mul_comm n a)
  have hexp : exp (-(a * n)) ≤ δ / K := by
    calc exp (-(a * n))
        ≤ exp (-log (K / δ)) := exp_le_exp.mpr (by linarith)
      _ = (K / δ)⁻¹ := by rw [exp_neg, exp_log (div_pos hK hδ)]
      _ = δ / K := inv_div K δ
  calc c * exp (-(a * n))
      ≤ K * exp (-(a * n)) := mul_le_mul_of_nonneg_right hcK (exp_pos _).le
    _ ≤ K * (δ / K) := mul_le_mul_of_nonneg_left hexp hK.le
    _ = δ := mul_div_cancel₀ δ hK.ne'

end Real
