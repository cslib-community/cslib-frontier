/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Numbers `t * m + z` with a digit `z < m`

Mixed-radix numbers with one low digit, as when constraints of a family are numbered by a pair of
parameters: quotient and remainder by `m` recover the parameters, and the number stays below
`T * m` when `t < T`.

## Main results

* `Nat.mul_add_div_mod_of_lt`: the quotient and remainder of `t * m + z` by `m` are `t` and `z`.
* `Nat.mul_add_lt_mul_of_lt`: `t * m + z < T * m` when `t < T` and `z < m`.
-/

public section

namespace Nat

/-- The quotient and remainder of `t * m + z` by `m` are `t` and `z` when `z < m`. -/
theorem mul_add_div_mod_of_lt (t : ℕ) {z m : ℕ} (hz : z < m) :
    (t * m + z) / m = t ∧ (t * m + z) % m = z :=
  ⟨mul_add_div_of_lt t hz, mul_add_mod_of_lt hz⟩

/-- A mixed-radix number `t * m + z` with digit `z < m` is below `T * m` when `t < T`. -/
theorem mul_add_lt_mul_of_lt {t T z m : ℕ} (ht : t < T) (hz : z < m) : t * m + z < T * m := by
  have : (t + 1) * m ≤ T * m := Nat.mul_le_mul_right m ht
  rw [Nat.succ_mul] at this
  omega

end Nat
