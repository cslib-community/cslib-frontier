/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Positivity

/-! # Real power bounds for `Nat.nthRoot`

Sandwiches `(n : ℝ) ^ ((r : ℝ)⁻¹)` between `(Nat.nthRoot r n : ℝ)` and `(Nat.nthRoot r n : ℝ) + 1`
for `r ≠ 0` (`Nat.cast_nthRoot_le_rpow`, `Real.rpow_lt_natCast_nthRoot_add_one`).
-/

public section

/-- For `r ≠ 0`, the integer `r`-th root `(Nat.nthRoot r n : ℝ)` is at most `(n : ℝ) ^ ((r : ℝ)⁻¹)`.
-/
theorem Nat.cast_nthRoot_le_rpow (r n : ℕ) (hr : r ≠ 0) :
    (Nat.nthRoot r n : ℝ) ≤ (n : ℝ) ^ ((r : ℝ)⁻¹) := by
  have h : (Nat.nthRoot r n : ℝ) ^ r ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := r) (a := n) (Or.inl hr)
  have h' := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (by positivity) hr] at h'

/-- For `r ≠ 0`, `(n : ℝ) ^ ((r : ℝ)⁻¹)` is strictly less than `(Nat.nthRoot r n : ℝ) + 1`. -/
theorem Real.rpow_lt_natCast_nthRoot_add_one (r n : ℕ) (hr : r ≠ 0) :
    (n : ℝ) ^ ((r : ℝ)⁻¹) < (Nat.nthRoot r n : ℝ) + 1 := by
  have h : (n : ℝ) < ((Nat.nthRoot r n + 1 : ℕ) : ℝ) ^ r := by
    exact_mod_cast Nat.lt_pow_nthRoot_add_one hr n
  have h' := Real.rpow_lt_rpow (by positivity) h (by positivity : (0 : ℝ) < (r : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (by positivity) hr, Nat.cast_add, Nat.cast_one] at h'
