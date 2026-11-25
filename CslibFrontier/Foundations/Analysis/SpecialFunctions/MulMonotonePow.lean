/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Multiplicative monotone functions on the positive integers are powers

A function `f ≥ 1` on the positive integers that is multiplicative, `f (m * n) = f m * f n`,
and monotone is a power function: `f n = n ^ e` with `e = log₂ f 2`
(`Cslib.eq_rpow_of_mul_monotone`). The proof compares `f (n ^ k)` with `f (2 ^ m)` for
`2 ^ m ≤ n ^ k < 2 ^ (m + 1)` and lets `k` grow. A spectral point is such a function on the
unit tensors (`Cslib.PartyTensor.antisymmRel_unit_mul`, `Cslib.PartyTensor.unit_le_unit`).

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Ov.Core.Unit` (`eq_rpow_of_mul_mono`)
-/

public section

namespace Cslib

/-- A function `f ≥ 1` on the positive integers that is multiplicative and monotone is a power
function: `f n = n ^ e` with `e = log₂ f 2`. -/
theorem eq_rpow_of_mul_monotone (f : ℕ → ℝ) (h1 : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n, 1 ≤ m → m ≤ n → f m ≤ f n) (n : ℕ) (hn : 1 ≤ n) :
    f n = (n : ℝ) ^ Real.logb 2 (f 2) := by
  have hone : f 1 = 1 := by
    have := hmul 1 1 le_rfl le_rfl
    have := h1 1 le_rfl
    nlinarith
  have hpow (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : f (m ^ k) = f m ^ k := by
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hm) hm, ih, pow_succ]
  have hfpos : ∀ m, 1 ≤ m → 0 < f m := fun m hm => lt_of_lt_of_le one_pos (h1 m hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.log (f 2) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (h1 2 (by norm_num))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_pow {u v : ℝ} {p q : ℕ} (hu : 0 < u) (hle : u ^ p ≤ v ^ q) :
      (p : ℝ) * Real.log u ≤ q * Real.log v := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hu p) hle
  set x := Real.log (f n) * Real.log 2 - a * Real.log n with hx
  have key (k : ℕ) : |(k : ℝ) * x| ≤ a * Real.log 2 := by
    set m := Nat.log 2 (n ^ k)
    have hm1 : 2 ^ m ≤ n ^ k := Nat.pow_log_le_self 2 (pow_ne_zero _ (by omega))
    have hm2 : n ^ k ≤ 2 ^ (m + 1) := (Nat.lt_pow_succ_log_self (by norm_num) _).le
    have f1 : f 2 ^ m ≤ f n ^ k := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ Nat.one_le_two_pow hm1
    have f2 : f n ^ k ≤ f 2 ^ (m + 1) := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_pow _ _ hn) hm2
    have g1 := hlog_pow (hfpos 2 (by norm_num)) f1
    have g2 := hlog_pow (hfpos n hn) f2
    have g3 := hlog_pow zero_lt_two (show (2 : ℝ) ^ m ≤ (n : ℝ) ^ k by exact_mod_cast hm1)
    have g4 := hlog_pow hnpos (show (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) by exact_mod_cast hm2)
    push_cast at g2 g4
    rw [abs_le, hx]
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_right g1 hl2.le, mul_le_mul_of_nonneg_left g4 ha0],
      by nlinarith [mul_le_mul_of_nonneg_right g2 hl2.le, mul_le_mul_of_nonneg_left g3 ha0]⟩
  have hx0 : x = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := exists_nat_gt (a * Real.log 2 / |x|)
    have := key k
    rw [abs_mul, Nat.abs_cast] at this
    linarith [(div_lt_iff₀ (abs_pos.2 hne)).1 hk]
  have hfin : Real.log (f n) = Real.logb 2 (f 2) * Real.log n := by
    rw [Real.logb, div_mul_eq_mul_div, eq_div_iff hl2.ne']; linarith
  rw [Real.rpow_def_of_pos hnpos, mul_comm, ← hfin, Real.exp_log (hfpos n hn)]

end Cslib
