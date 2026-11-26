/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingScale
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogTwoPow

/-!
# Monotonicity and linear-scaling bounds for `interpolationScale`

Elementary order and scaling inequalities for
`Cslib.Complexity.SubexponentialSAT.interpolationScale`. While `CountingScale.lean` establishes
`interpolationScale =o[atTop] id`, reductions into the bounded-width model counter (such as
circuit-to-CNF compilation with `numVars ≤ k * s + m`, or binary domain encodings with
`numVars ≤ b * n`) bound the target variable count linearly in a source parameter. Because
`interpolationScale` is monotone and doubles by at most a factor of `8`, any affine bound
`a ≤ C * b + D` lifts `2 ^ (A * interpolationScale a)` into `O(2 ^ (A' * interpolationScale b))`
for an explicit natural multiplier `A'`.

## Main results

* `Cslib.Complexity.SubexponentialSAT.interpolationScale_mono`: `Monotone interpolationScale`.
* `Cslib.Complexity.SubexponentialSAT.interpolationScale_two_mul_le`:
  `interpolationScale (2 * n) ≤ 8 * interpolationScale n`.
* `Cslib.Complexity.SubexponentialSAT.interpolationScale_le_of_linear`:
  affine upper bound on `interpolationScale a` when `a ≤ C * b + D`.
* `Cslib.Complexity.SubexponentialSAT.ceil_two_pow_interpolationScale_le_of_linear`:
  `⌈2 ^ (A * interpolationScale a)⌉₊ ≤ K * ⌈2 ^ (A' * interpolationScale b)⌉₊`
  under `a ≤ C * b + D`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH],
  Proposition 6.4, pp. 43–44.
-/

public section

namespace Cslib.Complexity.SubexponentialSAT

/-- `interpolationScale` is monotone on all natural numbers. -/
theorem interpolationScale_mono : Monotone interpolationScale := by
  refine monotone_nat_of_le_succ fun n => ?_
  set x : ℝ := (n : ℝ) + 16
  set y : ℝ := ((n + 1 : ℕ) : ℝ) + 16
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy : y = x + 1 := by push_cast [x, y]; ring
  have hlogx_gt1 : 1 < Real.log x := one_lt_log_add_sixteen n
  have hlogx : 0 < Real.log x := log_add_sixteen_pos n
  have hlogy : 0 < Real.log y := log_add_sixteen_pos (n + 1)
  have hll_le : Real.log (Real.log x) ^ 2 ≤ Real.log (Real.log y) ^ 2 :=
    pow_le_pow_left₀ (by linarith [one_lt_log_log_add_sixteen n])
      (Real.log_le_log hlogx (Real.log_le_log hx (by linarith))) 2
  have hratio : (n : ℝ) / Real.sqrt (Real.log x) ≤ ((n + 1 : ℕ) : ℝ) / Real.sqrt (Real.log y) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hlogx) (Real.sqrt_pos.mpr hlogy)]
    have hsq : ((n : ℝ) * Real.sqrt (Real.log y)) ^ 2 ≤
        (((n + 1 : ℕ) : ℝ) * Real.sqrt (Real.log x)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hlogy.le, Real.sq_sqrt hlogx.le]
      have hlog_diff : Real.log y ≤ Real.log x + 1 / x := by
        have hle := Real.log_le_sub_one_of_pos (div_pos hy hx)
        rw [Real.log_div hy.ne' hx.ne', hxy, add_div, div_self hx.ne'] at hle
        linarith [congrArg Real.log hxy]
      have hn2 : (n : ℝ) ^ 2 * (1 / x) ≤ (n : ℝ) := by
        rw [mul_one_div, div_le_iff₀ hx, sq]
        exact mul_le_mul_of_nonneg_left (by simp only [x]; linarith) (Nat.cast_nonneg n)
      calc (n : ℝ) ^ 2 * Real.log y
          ≤ (n : ℝ) ^ 2 * (Real.log x + 1 / x) := by gcongr
        _ = (n : ℝ) ^ 2 * Real.log x + (n : ℝ) ^ 2 * (1 / x) := by ring
        _ ≤ (n : ℝ) ^ 2 * Real.log x + (n : ℝ) * 1 := by linarith
        _ ≤ (n : ℝ) ^ 2 * Real.log x + (2 * (n : ℝ) + 1) * Real.log x := by
              gcongr
              linarith [Nat.cast_nonneg (α := ℝ) n]
        _ = ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log x := by push_cast; ring
    exact nonneg_le_nonneg_of_sq_le_sq (by positivity) (by simpa only [sq] using hsq)
  rw [interpolationScale, interpolationScale, ← div_mul_eq_mul_div, ← div_mul_eq_mul_div]
  exact mul_le_mul hratio hll_le (by positivity) (by positivity)

/-- Doubling the argument multiplies `interpolationScale` by at most `8`. -/
theorem interpolationScale_two_mul_le (n : ℕ) :
    interpolationScale (2 * n) ≤ 8 * interpolationScale n := by
  unfold interpolationScale
  set x : ℝ := (n : ℝ) + 16
  set y : ℝ := ((2 * n : ℕ) : ℝ) + 16
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy_le : x ≤ y := add_le_add_left (Nat.cast_le.mpr (Nat.le_mul_of_pos_left n two_pos)) 16
  have hy_sq : y ≤ x ^ 2 := by
    push_cast [x, y]
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  have hlogx : 0 < Real.log x := log_add_sixteen_pos n
  have hlogy : 0 < Real.log y := log_add_sixteen_pos (2 * n)
  have hlogy_le : Real.log y ≤ 2 * Real.log x :=
    calc Real.log y ≤ Real.log (x ^ 2) := Real.log_le_log hy hy_sq
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlly_le : Real.log (Real.log y) ≤ 2 * Real.log (Real.log x) := by
    have h1 := one_lt_log_log_add_sixteen n
    have hlog2 : Real.log 2 < 1 := Real.log_two_lt_one
    calc Real.log (Real.log y)
        ≤ Real.log (2 * Real.log x) := Real.log_le_log hlogy hlogy_le
      _ = Real.log 2 + Real.log (Real.log x) := Real.log_mul (by norm_num) hlogx.ne'
      _ ≤ 2 * Real.log (Real.log x) := by linarith
  have hll_sq : Real.log (Real.log y) ^ 2 ≤ 4 * Real.log (Real.log x) ^ 2 := by
    nlinarith only [hlly_le, one_lt_log_log_add_sixteen (2 * n)]
  have hsqrt_le : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y) :=
    Real.sqrt_le_sqrt (Real.log_le_log hx hxy_le)
  have hsqx : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlogx
  calc ((2 * n : ℕ) : ℝ) * Real.log (Real.log y) ^ 2 / Real.sqrt (Real.log y)
      ≤ ((2 * n : ℕ) : ℝ) * Real.log (Real.log y) ^ 2 / Real.sqrt (Real.log x) := by gcongr
    _ ≤ (2 * (n : ℝ)) * (4 * Real.log (Real.log x) ^ 2) / Real.sqrt (Real.log x) := by
        push_cast; gcongr
    _ = 8 * ((n : ℝ) * Real.log (Real.log x) ^ 2 / Real.sqrt (Real.log x)) := by ring

/-- Scaling the argument by `2 ^ k` multiplies `interpolationScale` by at most `8 ^ k`. -/
theorem interpolationScale_two_pow_mul_le (k n : ℕ) :
    interpolationScale (2 ^ k * n) ≤ (8 : ℝ) ^ k * interpolationScale n := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc interpolationScale (2 ^ (k + 1) * n)
        = interpolationScale (2 * (2 ^ k * n)) := by rw [pow_succ', mul_assoc]
      _ ≤ 8 * interpolationScale (2 ^ k * n) := interpolationScale_two_mul_le _
      _ ≤ 8 * ((8 : ℝ) ^ k * interpolationScale n) := by gcongr
      _ = (8 : ℝ) ^ (k + 1) * interpolationScale n := by rw [pow_succ', mul_assoc]

/-- Scaling the argument by `C` multiplies `interpolationScale` by at most `8 ^ C`. -/
theorem interpolationScale_mul_le (C n : ℕ) :
    interpolationScale (C * n) ≤ (8 ^ C : ℕ) * interpolationScale n := by
  have hle : C * n ≤ 2 ^ C * n := Nat.mul_le_mul_right n C.lt_two_pow_self.le
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (interpolationScale_mono hle).trans (interpolationScale_two_pow_mul_le C n)

/-- Any affine relation `a ≤ C * b + D` yields a linear bound on `interpolationScale a` in terms of
`interpolationScale b` plus a constant depending only on `D`. -/
theorem interpolationScale_le_of_linear {a b C D : ℕ} (h : a ≤ C * b + D) :
    interpolationScale a ≤
      (8 ^ (2 * C) : ℕ) * interpolationScale b + 8 * interpolationScale D := by
  rcases le_total (C * b) D with hCD | hDC
  · have h1 := (interpolationScale_mono (show a ≤ 2 * D by omega)).trans
      (interpolationScale_two_mul_le D)
    linarith [mul_nonneg (Nat.cast_nonneg (8 ^ (2 * C))) (interpolationScale_nonneg b)]
  · have h1 := (interpolationScale_mono (show a ≤ (2 * C) * b by rw [mul_assoc]; omega)).trans
      (interpolationScale_mul_le (2 * C) b)
    linarith [interpolationScale_nonneg D]

/-- Under an affine bound `a ≤ C * b + D`, the ceiling `⌈2 ^ (A * interpolationScale a)⌉₊` is at
most a constant natural multiple of `⌈2 ^ ((A * 8 ^ (2 * C)) * interpolationScale b)⌉₊`. -/
theorem ceil_two_pow_interpolationScale_le_of_linear (A C D : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ {a b : ℕ}, a ≤ C * b + D →
      ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale a)⌉₊ ≤
        K * ⌈(2 : ℝ) ^ (((A * 8 ^ (2 * C) : ℕ) : ℝ) * interpolationScale b)⌉₊ := by
  let K : ℕ := ⌈(2 : ℝ) ^ ((A : ℝ) * (8 * interpolationScale D))⌉₊
  refine ⟨K, Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _), fun {a b} hab => ?_⟩
  have hexp : (A : ℝ) * interpolationScale a ≤
      (A : ℝ) * (8 * interpolationScale D) +
        ((A * 8 ^ (2 * C) : ℕ) : ℝ) * interpolationScale b := by
    have hmul := mul_le_mul_of_nonneg_left (interpolationScale_le_of_linear hab) (Nat.cast_nonneg A)
    push_cast at hmul ⊢
    linarith
  refine Nat.ceil_le.mpr ?_
  rw [Nat.cast_mul]
  calc (2 : ℝ) ^ ((A : ℝ) * interpolationScale a)
      ≤ (2 : ℝ) ^ ((A : ℝ) * (8 * interpolationScale D) +
          ((A * 8 ^ (2 * C) : ℕ) : ℝ) * interpolationScale b) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ ((A : ℝ) * (8 * interpolationScale D)) *
          (2 : ℝ) ^ (((A * 8 ^ (2 * C) : ℕ) : ℝ) * interpolationScale b) :=
        Real.rpow_add (by norm_num) _ _
    _ ≤ (K : ℝ) * ⌈(2 : ℝ) ^ (((A * 8 ^ (2 * C) : ℕ) : ℝ) * interpolationScale b)⌉₊ :=
        mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity)

end Cslib.Complexity.SubexponentialSAT
