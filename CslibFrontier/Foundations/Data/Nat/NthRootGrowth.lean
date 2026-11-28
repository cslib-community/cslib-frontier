/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomials below `2 ^ Nat.nthRoot r n`

A polynomial in `n` is eventually at most `2 ^ Nat.nthRoot r n` for every `r > 0`, so a circuit or
a machine of size `2 ^ (n ^ (1 / r))` absorbs any polynomial overhead. The square of the root of
order `2 r` is eventually at most the root of order `r`, which absorbs a subexponential factor
`2 ^ (K * Nat.nthRoot (2 * r) n)` as well. The module is separate so that the few clients that
need it do not widen the import fan-out of a hub such as
`CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure`.

## Main results

* `Nat.mul_pow_succ_le_two_pow`: `C * (n + 1) ^ K ≤ 2 ^ (C.size + K * (log₂ (n + 1) + 1))`.
* `Nat.eventually_mul_pow_mul_two_pow_le_two_pow_nthRoot`: for `0 < r`, a polynomial times
  `2 ^ (K₂ * Nat.nthRoot (2 * r) n)` is eventually at most `2 ^ Nat.nthRoot r n`.
* `Nat.eventually_mul_pow_le_two_pow_nthRoot`: for `0 < r`, every polynomial is eventually at
  most `2 ^ Nat.nthRoot r n`.
-/

public section

open Filter

/-- **A polynomial below a power of two**:
`C * (n + 1) ^ K ≤ 2 ^ (C.size + K * (log₂ (n + 1) + 1))`, since `C < 2 ^ C.size` and
`n + 1 ≤ 2 ^ (log₂ (n + 1) + 1)`. -/
theorem Nat.mul_pow_succ_le_two_pow (C K n : ℕ) :
    C * (n + 1) ^ K ≤ 2 ^ (C.size + K * (Nat.log 2 (n + 1) + 1)) := by
  have hC : C ≤ 2 ^ C.size := (Nat.lt_size_self C).le
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 1)).le
  calc C * (n + 1) ^ K
      ≤ 2 ^ C.size * (2 ^ (Nat.log 2 (n + 1) + 1)) ^ K :=
        Nat.mul_le_mul hC (Nat.pow_le_pow_left hn K)
    _ = 2 ^ (C.size + K * (Nat.log 2 (n + 1) + 1)) := by
        rw [← pow_mul, pow_add, mul_comm (Nat.log 2 (n + 1) + 1) K]

/-- **A growth lemma for roots of order `2 r` and `r`.** For `0 < r`, a polynomial times
`2 ^ (K₂ * Nat.nthRoot (2 * r) n)` is eventually at most `2 ^ Nat.nthRoot r n`: the square of
the root of order `2 r` is at most the root of order `r`, and beats any linear function of it. -/
theorem Nat.eventually_mul_pow_mul_two_pow_le_two_pow_nthRoot {r : ℕ} (hr : 0 < r)
    (C K₁ K₂ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * (n + 1) ^ K₁ * 2 ^ (K₂ * Nat.nthRoot (2 * r) n) ≤ 2 ^ Nat.nthRoot r n := by
  have h2r : 2 * r ≠ 0 := by omega
  filter_upwards [eventually_ge_atTop ((2 * r * K₁ + K₂ + (C.size + 2 * r * K₁) + 1) ^ (2 * r))]
    with n hn
  set a := Nat.nthRoot (2 * r) n
  have haT : 2 * r * K₁ + K₂ + (C.size + 2 * r * K₁) + 1 ≤ a := (Nat.le_nthRoot_iff h2r).2 hn
  have han : a ^ (2 * r) ≤ n := Nat.pow_nthRoot_le_iff.2 (Or.inl h2r)
  have hlt : n < (a + 1) ^ (2 * r) := Nat.lt_pow_nthRoot_add_one h2r n
  have hlog : Nat.log 2 (n + 1) < 2 * r * (a + 1) := by
    apply Nat.log_lt_of_lt_pow (by omega)
    calc n + 1 ≤ (a + 1) ^ (2 * r) := hlt
      _ < (2 ^ (a + 1)) ^ (2 * r) := Nat.pow_lt_pow_left Nat.lt_two_pow_self h2r
      _ = 2 ^ (2 * r * (a + 1)) := by rw [← pow_mul, mul_comm]
  have h1 : K₁ * (Nat.log 2 (n + 1) + 1) ≤ K₁ * (2 * r * (a + 1)) := Nat.mul_le_mul_left _ hlog
  have h3 : (2 * r * K₁ + K₂) * a + (C.size + 2 * r * K₁) ≤ a ^ 2 := by
    nlinarith [Nat.mul_le_mul_right a haT]
  have hexp : C.size + K₁ * (Nat.log 2 (n + 1) + 1) + K₂ * a ≤ a ^ 2 := by
    have : C.size + K₁ * (2 * r * (a + 1)) + K₂ * a =
        (2 * r * K₁ + K₂) * a + (C.size + 2 * r * K₁) := by ring
    linarith
  have hroot : a ^ 2 ≤ Nat.nthRoot r n := by
    refine (Nat.le_nthRoot_iff hr.ne').2 ?_
    calc (a ^ 2) ^ r = a ^ (2 * r) := by rw [← pow_mul]
      _ ≤ n := han
  calc C * (n + 1) ^ K₁ * 2 ^ (K₂ * a)
      ≤ 2 ^ (C.size + K₁ * (Nat.log 2 (n + 1) + 1)) * 2 ^ (K₂ * a) :=
        Nat.mul_le_mul_right _ (Nat.mul_pow_succ_le_two_pow C K₁ n)
    _ = 2 ^ (C.size + K₁ * (Nat.log 2 (n + 1) + 1) + K₂ * a) := (pow_add _ _ _).symm
    _ ≤ 2 ^ Nat.nthRoot r n := Nat.pow_le_pow_right (by norm_num) (hexp.trans hroot)

/-- Every polynomial is eventually at most `2 ^ Nat.nthRoot r n`, for `0 < r`. -/
theorem Nat.eventually_mul_pow_le_two_pow_nthRoot {r : ℕ} (hr : 0 < r) (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (n + 1) ^ k ≤ 2 ^ Nat.nthRoot r n :=
  (Nat.eventually_mul_pow_mul_two_pow_le_two_pow_nthRoot hr C k 0).mono fun n h => by
    simpa using h
