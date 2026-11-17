/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rounding real coordinates to signs

`BitString.signRound` reads a negative real coordinate as `true`, whose sign is `-1`, and every
other coordinate as `false`, whose sign is `1`. A rounding error against a sign of magnitude `a`
costs at least `a²` in squared error. Summing over the coordinates bounds the Hamming distance
after rounding. These elementary estimates apply to real approximations of Boolean functions
and to spectral label recovery.

## Main results

* `Cslib.BitString.sq_mul_hammingDist_signRound_le_sum_sq_sub`: scaled signs and squared error.
* `Cslib.BitString.hammingDist_signRound_le_sum_sq_sub`: the unit-sign specialization.
-/

public section

namespace Cslib.BitString

open Finset

variable {α : Type*}

/-- A real function rounded to its sign: `true`, the sign `-1`, where it is negative, and
`false`, the sign `1`, elsewhere. In particular, zero rounds to `false`. -/
@[expose] noncomputable def signRound (g : α → ℝ) (x : α) : Bool :=
  decide (g x < 0)

/-- The sign rounding of `g` at `x` is `true` exactly when `g x < 0`. -/
@[simp] theorem signRound_apply (g : α → ℝ) (x : α) :
    signRound g x = decide (g x < 0) :=
  rfl

private theorem sq_le_sq_sub_mul_signVal_of_decide_ne {b : Bool} {a r : ℝ} (ha : 0 ≤ a)
    (h : decide (r < 0) ≠ b) : a ^ 2 ≤ (r - a * signVal b) ^ 2 := by
  cases b
  · have hr : r < 0 := by simpa using h
    simp only [signVal_false, mul_one]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hr.le ha]
  · have hr : 0 ≤ r := by simpa using h
    simp only [signVal_true, mul_neg_one, sub_neg_eq_add]
    nlinarith [mul_nonneg hr ha]

variable [Fintype α]

/-- Each misclassified coordinate costs at least `a²` in squared error from a sign of magnitude
`a`. The estimate also holds at `a = 0`. -/
theorem sq_mul_hammingDist_signRound_le_sum_sq_sub (f : α → Bool) (g : α → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * (hammingDist (signRound g) f : ℝ) ≤ ∑ x, (g x - a * signVal (f x)) ^ 2 := by
  rw [hammingDist, card_filter, Nat.cast_sum, Finset.mul_sum]
  refine sum_le_sum fun x _ => ?_
  split_ifs with h
  · simpa only [Nat.cast_one, mul_one] using
      sq_le_sq_sub_mul_signVal_of_decide_ne ha h
  · simpa using sq_nonneg (g x - a * signVal (f x))

/-- Rounding a real approximation to its sign makes at most its total squared error in
misclassified coordinates, reading the target bits as signs. -/
theorem hammingDist_signRound_le_sum_sq_sub (f : α → Bool) (g : α → ℝ) :
    (hammingDist (signRound g) f : ℝ) ≤ ∑ x, (signVal (f x) - g x) ^ 2 := by
  simpa only [one_pow, one_mul, sub_sq_comm] using
    sq_mul_hammingDist_signRound_le_sum_sq_sub f g (a := 1) (by norm_num)

end Cslib.BitString
