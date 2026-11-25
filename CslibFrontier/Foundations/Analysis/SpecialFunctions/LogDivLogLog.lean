/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary factorial and `log y / log (log y)` inversion bounds

Elementary estimates used when inverting factorial growth `2 ^ k * k!` into `Ω(log m / log log m)`
lower bounds (such as Czumaj–Vöcking related-machine and balls-into-bins price-of-anarchy bounds):

* `Nat.four_pow_le_two_mul_two_pow_mul_factorial`: `4 ^ k ≤ 2 * (2 ^ k * k!)` for `k ≥ 1`.
* `Real.one_lt_log_of_three_le`: `1 < log x` for `x ≥ 3`.
* `Real.add_mul_log_two_le`: `(x + d) * log 2 ≤ (1 + d / 2) * x * log x` for `x ≥ 2`, `d ≥ 0`.
* `Real.add_one_mul_log_add_one_le`: `(x + 1) * log (x + 1) ≤ 3 * x * log x` for `x ≥ 2`.
* `Real.inv_mul_log_div_log_log_le`: if `2 ≤ x`, `0 < c`, `exp x < y`, and
  `log y ≤ c * x * log x`, then `0 < log (log y)` and `(1 / c) * (log y / log (log y)) ≤ x`.
-/

public section

namespace Nat

/-- `4 ^ k ≤ 2 * (2 ^ k * k!)` for `k ≥ 1`, from `2 ^ (k - 1) ≤ k!`. -/
theorem four_pow_le_two_mul_two_pow_mul_factorial {k : ℕ} (hk : 1 ≤ k) :
    4 ^ k ≤ 2 * (2 ^ k * k.factorial) := by
  have hfac : 2 ^ (k - 1) ≤ k.factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := k - 1)
    have hadd : 1 + (k - 1) = k := by omega
    simpa only [Nat.factorial_one, one_mul, hadd] using h
  have hpow : 4 ^ k = 2 * 2 ^ k * 2 ^ (k - 1) := by
    have h2k : 2 * k = 1 + k + (k - 1) := by omega
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, h2k, pow_add, pow_add, pow_one]
  rw [hpow, mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfac)

end Nat

namespace Real

/-- `1 < log x` for `x ≥ 3`, since `exp 1 < 3`. -/
theorem one_lt_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 < log x := by
  rw [← log_exp 1]
  exact log_lt_log (exp_pos 1) ((exp_one_lt_d9.trans (by norm_num)).trans_le hx)

/-- `(x + d) * log 2 ≤ (1 + d / 2) * x * log x` for `x ≥ 2` and `d ≥ 0`, since `log 2 ≤ log x` and
`x + d ≤ (1 + d / 2) * x`. -/
theorem add_mul_log_two_le {x d : ℝ} (hx : 2 ≤ x) (hd : 0 ≤ d) :
    (x + d) * log 2 ≤ (1 + d / 2) * x * log x := by
  have hlog2 : log 2 ≤ log x := log_le_log (by norm_num) hx
  have hlogx_nn : 0 ≤ log x := (log_pos (by linarith)).le
  calc (x + d) * log 2 ≤ (x + d) * log x := mul_le_mul_of_nonneg_left hlog2 (by linarith)
    _ ≤ ((1 + d / 2) * x) * log x := mul_le_mul_of_nonneg_right (by nlinarith) hlogx_nn
    _ = (1 + d / 2) * x * log x := by ring

/-- `(x + 1) * log (x + 1) ≤ 3 * x * log x` for `x ≥ 2`, since `x + 1 ≤ x ^ 2` gives
`log (x + 1) ≤ 2 * log x` and `x + 1 ≤ (3 / 2) * x`. -/
theorem add_one_mul_log_add_one_le {x : ℝ} (hx : 2 ≤ x) :
    (x + 1) * log (x + 1) ≤ 3 * x * log x := by
  have hlogx_nn : 0 ≤ log x := (log_pos (by linarith)).le
  have hlog1 : log (x + 1) ≤ 2 * log x := by
    calc log (x + 1) ≤ log (x ^ 2) := log_le_log (by linarith) (by nlinarith)
      _ = 2 * log x := by rw [log_pow]; norm_num
  calc (x + 1) * log (x + 1) ≤ (x + 1) * (2 * log x) :=
        mul_le_mul_of_nonneg_left hlog1 (by linarith)
    _ ≤ ((3 / 2 : ℝ) * x) * (2 * log x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ = 3 * x * log x := by ring

/-- Logarithmic inversion for `x * log x` growth: if `2 ≤ x`, `0 < c`, `exp x < y`, and
`log y ≤ c * x * log x`, then `0 < log (log y)` and `(1 / c) * (log y / log (log y)) ≤ x`. -/
theorem inv_mul_log_div_log_log_le {x y c : ℝ} (hx : 2 ≤ x) (hc : 0 < c)
    (hexp : exp x < y) (hlogy : log y ≤ c * x * log x) :
    0 < log (log y) ∧ (1 / c) * (log y / log (log y)) ≤ x := by
  have hx_lt : x < log y := by
    rw [← log_exp x]
    exact log_lt_log (exp_pos x) hexp
  have hloglog_pos : 0 < log (log y) := log_pos (by linarith)
  have hlogx_lt : log x < log (log y) := log_lt_log (by linarith) hx_lt
  have hle : log y ≤ c * x * log (log y) :=
    hlogy.trans (mul_le_mul_of_nonneg_left hlogx_lt.le (by positivity))
  have hdiv : log y / log (log y) ≤ c * x := (div_le_iff₀ hloglog_pos).mpr hle
  refine ⟨hloglog_pos, ?_⟩
  calc (1 / c) * (log y / log (log y))
      ≤ (1 / c) * (c * x) := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = x := by field_simp

end Real
