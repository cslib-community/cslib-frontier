/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Basic/ENNReal/Inv.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.ENNReal.Inv

/-!
# Fractions in `ℝ≥0∞`

A probability computed by counting is a fraction `a / b` of natural numbers in `ℝ≥0∞`. Comparing
two such fractions reduces to comparing the cross products in `ℕ`, and the probability that `m`
independent trials all succeed is a power `(a / b) ^ m`, which distributes over the quotient.

Mathlib's `div_pow` needs a `DivisionCommMonoid`, which `ℝ≥0∞` is not (`0 * ⊤ = 0` breaks
`(a * b)⁻¹ = a⁻¹ * b⁻¹`), so the quotient form of the power is stated here directly.

## Main results

* `ENNReal.natCast_div_le_natCast_div_iff`: for `b, d ≠ 0`, `a / b ≤ c / d ↔ a * d ≤ c * b`.
* `ENNReal.div_pow`: `(a / b) ^ n = a ^ n / b ^ n` for all `a b : ℝ≥0∞`.
* `ENNReal.one_sub_pow_succ_le`: for `δ ≤ 1`, the recursion
  `1 - (1 - δ) ^ (n + 1) ≤ (1 - δ) (1 - (1 - δ) ^ n) + δ` behind the probability `1 - (1 - δ) ^ n`
  that one of `n` independent trials with probability `δ` succeeds.
* `ENNReal.ofReal_div_natCast`: `ENNReal.ofReal (k / N) = k / N` for natural numbers with `N > 0`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- Two fractions of natural numbers with nonzero denominators compare in `ℝ≥0∞` as their cross
products compare in `ℕ`: `a / b ≤ c / d ↔ a * d ≤ c * b`. -/
theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast Iff.rfl

/-- A power of a quotient in `ℝ≥0∞` is the quotient of the powers, with no side conditions. -/
protected theorem div_pow (a b : ℝ≥0∞) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-- One more round at flip probability `δ`: the recursion behind `1 - (1 - δ) ^ n`. -/
theorem one_sub_pow_succ_le {δ : ℝ≥0∞} (hδ : δ ≤ 1) (n : ℕ) :
    1 - (1 - δ) ^ (n + 1) ≤ (1 - δ) * (1 - (1 - δ) ^ n) + δ := by
  have hq : 1 - δ + δ = 1 := tsub_add_cancel_of_le hδ
  have hqtop : 1 - δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [ENNReal.mul_sub (fun _ _ => hqtop), mul_one, ← pow_succ']
  calc 1 - (1 - δ) ^ (n + 1) = 1 - δ + δ - (1 - δ) ^ (n + 1) := by rw [hq]
    _ ≤ 1 - δ - (1 - δ) ^ (n + 1) + δ := add_tsub_le_tsub_add

/-- A quotient of natural numbers as an extended nonnegative real is the real quotient. -/
theorem ofReal_div_natCast (k N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal ((k : ℝ) / N) = (k : ℝ≥0∞) / N := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

end ENNReal
