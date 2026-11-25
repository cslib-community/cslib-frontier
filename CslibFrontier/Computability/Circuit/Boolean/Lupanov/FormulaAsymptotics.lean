/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-!
# Real asymptotic form of the formula parameter bound

The integer parameter bound in `FormulaBounds` yields the usual real logarithm and arbitrary
positive relative error. This module proves only the arithmetic conversion; the native
local-coding construction supplies the formula realizing `formulaBound`.

## Main results

* `Cslib.Circuits.Boolean.LupanovFormula.eventually_exists_formulaBound_real_le`: parameters
  of total dimension `n` whose bound is at most `(1 + ε) * 2 ^ n / Real.logb 2 n`.
-/

public section

namespace Cslib.Circuits.Boolean.LupanovFormula

open Filter

/-- Parameter selection with any positive relative error, using the real binary logarithm.
This converts the natural-number budget; it does not assume or assert formula realizability. -/
theorem eventually_exists_formulaBound_real_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ a c r s : ℕ, 0 < s ∧ a + (c + 2 ^ r) = n ∧
      (formulaBound a c (2 ^ r) s : ℝ) ≤ (1 + ε) * 2 ^ n / Real.logb 2 n := by
  obtain ⟨P, hP⟩ := exists_nat_gt (max 1 (3 / ε))
  have hP1 : (1 : ℝ) < P := lt_of_le_of_lt (le_max_left ..) hP
  have hPpos : (0 : ℝ) < P := lt_trans zero_lt_one hP1
  have hthree : (3 : ℝ) ≤ ε * P := by
    have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right ..) hP)
    linarith
  have hgain : ((P : ℝ) + 1) ^ 2 ≤ (1 + ε) * (P : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hthree hPpos.le
    nlinarith only [h, hP1]
  filter_upwards [eventually_exists_formulaBound_le P, eventually_ge_atTop (2 ^ P)]
    with n hparams hn
  obtain ⟨a, c, r, s, hs, hdim, hbound⟩ := hparams
  refine ⟨a, c, r, s, hs, hdim, ?_⟩
  have hpP : P ≤ Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two hn
  have hpPR : (P : ℝ) ≤ Nat.log2 n := by exact_mod_cast hpP
  have hlogpos : 0 < Real.logb 2 n :=
    hPpos.trans_le (hpPR.trans (Real.log2_le_logb n))
  have hfloor : ⌊Real.logb 2 n⌋₊ = Nat.log2 n := by
    simpa only [Nat.cast_ofNat, Nat.log2_eq_log_two] using Real.natFloor_logb_natCast 2 n
  have hlog : Real.logb 2 n < (Nat.log2 n : ℝ) + 1 := by
    simpa only [hfloor] using Nat.lt_floor_add_one (Real.logb 2 n)
  have hloggain : (P : ℝ) * Real.logb 2 n ≤ ((P : ℝ) + 1) * Nat.log2 n := by
    have h := mul_le_mul_of_nonneg_left hlog.le hPpos.le
    nlinarith only [h, hpPR]
  have hboundR : (P : ℝ) * Nat.log2 n * formulaBound a c (2 ^ r) s ≤
      ((P : ℝ) + 1) * 2 ^ n := by exact_mod_cast hbound
  have hfirst := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hloggain
      (Nat.cast_nonneg (formulaBound a c (2 ^ r) s) : (0 : ℝ) ≤ _)) hPpos.le
  have hsecond := mul_le_mul_of_nonneg_left hboundR
    (by positivity : (0 : ℝ) ≤ P + 1)
  have hthird := mul_le_mul_of_nonneg_right hgain (by positivity : (0 : ℝ) ≤ 2 ^ n)
  apply (le_div_iff₀ hlogpos).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hPpos 2)).mp
  nlinarith only [hfirst, hsecond, hthird]

end Cslib.Circuits.Boolean.LupanovFormula
