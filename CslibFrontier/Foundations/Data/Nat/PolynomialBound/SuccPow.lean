/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Nat.Basic

/-!
# A polynomial below an exponential

`(n + 1) ^ d ≤ 2 ^ (d * n)`, the bound that turns a polynomial factor of a running time into a
constant factor in the exponent of an exponential one. It sits in its own module so that the few
clients that need it do not widen the import fan-out of a hub such as
`CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure`.

## Main results

* `Nat.succ_pow_le_two_pow_mul`: `(n + 1) ^ d ≤ 2 ^ (d * n)`.
-/

public section

/-- `(n + 1) ^ d ≤ 2 ^ (d * n)`, since `n + 1 ≤ 2 ^ n`. -/
theorem Nat.succ_pow_le_two_pow_mul (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * n) :=
  calc (n + 1) ^ d ≤ (2 ^ n) ^ d := Nat.pow_le_pow_left Nat.lt_two_pow_self d
    _ = 2 ^ (d * n) := by rw [← Nat.pow_mul, Nat.mul_comm]
