/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Flat
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Charged subcubic native modular-counter time

The actual initialized execution, including halt, is bounded by a quadratic polynomial in
the runtime cyclic length p times seven to the computed ceiling-logarithmic matrix depth.
The real-power consequence has n exponent 2.81, strictly below three. Dependence on p remains
explicit; this does not claim subcubic time after arbitrary growth of p with n, nor complete
prime selection or the full ExactTriangle/3SUM endpoint.

All constants bound the proved native execution. They do not inherit the Light machine's
ring-operation constants from the pinned source.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

/-- Every actual initialized setup, memory/coefficient operation, recursion, scan and halt
fits this native seven-to-depth budget. -/
theorem cost_le_seven_pow (n p : ℕ) :
    cost n p + 10 ≤ (42 * p * p + 254 * p + 463) * 7 ^ Nat.clog 2 n := by
  let k := Nat.clog 2 n
  have hn2 : n * n ≤ 4 ^ k := calc
    n * n ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul (Nat.le_pow_clog (by decide) n)
      (Nat.le_pow_clog (by decide) n)
    _ = 4 ^ k := by rw [← mul_pow]; rfl
  have h4 : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) _
  have h2 : 2 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) _
  have ht := Strassen.traceBudget_potential_le p k
  have htrace : Strassen.traceBudget p k ≤ (42 * p * p + 240 * p + 178) * 7 ^ k := by omega
  change Strassen.traceBudget p k + (14 * p + 48) * 4 ^ k + 11 * (2 ^ k - 1) +
    91 * (n * n) + 4 * k + 81 + 9 * k + 31 + 10 ≤ _
  nlinarith only [htrace, Nat.mul_le_mul_left (14 * p + 48) h4,
    Nat.mul_le_mul_left 91 (hn2.trans h4),
    Nat.mul_le_mul_left 11 ((Nat.sub_le (2 ^ k) 1).trans h2),
    Nat.mul_le_mul_left 13 (Nat.lt_pow_self (n := k) (by decide : 1 < 7)).le,
    Nat.mul_le_mul_left 122 (Nat.one_le_pow k 7 (by decide))]

/-- A simple quadratic p envelope for the complete actual initialized instruction charge. -/
theorem cost_le_square (n p : ℕ) :
    cost n p + 10 ≤ 463 * (p + 1) ^ 2 * 7 ^ Nat.clog 2 n :=
  (cost_le_seven_pow n p).trans (Nat.mul_le_mul_right _ (by nlinarith))

private theorem seven_le_two_rpow : (7 : ℝ) ≤ (2 : ℝ) ^ (281 / 100 : ℝ) := by
  have hpow : ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ 100 = (2 : ℝ) ^ 281 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  apply (Real.rpow_le_rpow_iff (by norm_num) (by positivity)
    (by norm_num : 0 < ((100 : ℕ) : ℝ))).mp
  rw [Real.rpow_natCast, Real.rpow_natCast, hpow]
  exact_mod_cast (by decide +kernel : (7 : ℕ) ^ 100 ≤ 2 ^ 281)

private theorem seven_pow_clog_le (n : ℕ) :
    (7 : ℝ) ^ Nat.clog 2 n ≤ 8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) := by
  let k := Nat.clog 2 n
  have padR : (2 : ℝ) ^ k ≤ 2 * (n + 1 : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (Nat.clog_mono_right 2 (Nat.le_succ n))).trans
        (Nat.pow_clog_le_mul (by decide) (Nat.succ_ne_zero n))
  calc (7 : ℝ) ^ k ≤ ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ k :=
        pow_le_pow_left₀ (by norm_num) seven_le_two_rpow k
    _ = ((2 : ℝ) ^ k) ^ (281 / 100 : ℝ) := by
        rw [← Real.rpow_mul_natCast (by norm_num), mul_comm, Real.rpow_natCast_mul (by norm_num)]
    _ ≤ (2 * (n + 1 : ℝ)) ^ (281 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) padR (by norm_num)
    _ = (2 : ℝ) ^ (281 / 100 : ℝ) * (n + 1 : ℝ) ^ (281 / 100 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      convert Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ))
        (by norm_num : (281 / 100 : ℝ) ≤ 3) using 1
      norm_num

/-- The actual initialized native counter has subcubic n exponent 2.81 and quadratic p
factor, with every ring coefficient operation charged. The bound includes the final halt. -/
theorem cost_le_subcubic (n p : ℕ) :
    ((cost n p + 10 : ℕ) : ℝ) ≤
      3704 * (p + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) := by
  calc
    ((cost n p + 10 : ℕ) : ℝ) ≤ 463 * (p + 1 : ℝ) ^ 2 * (7 : ℝ) ^ Nat.clog 2 n := by
      exact_mod_cast cost_le_square n p
    _ ≤ 463 * (p + 1 : ℝ) ^ 2 * (8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left (seven_pow_clog_le n) (by positivity)
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
