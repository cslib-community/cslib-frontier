/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Order/Ring/Abs.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Squares of positive and negative parts

In a linearly ordered commutative ring, write `max a 0` and `max (-a) 0` for the positive and
negative parts of `a`, as in Mathlib's `max_zero_sub_max_neg_zero_eq_self`. The square of `a` is
the sum of the squares of its parts (`sq_max_zero_add_sq_max_neg_zero`), and taking parts does not
increase squared distances (`sq_max_zero_sub_add_sq_max_neg_zero_sub_le`). Both appear in the proof
of Cheeger's inequality, where a test vector is split into its positive and negative parts.
-/

public section

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The square of `a` is the sum of the squares of its positive and negative parts. -/
theorem sq_max_zero_add_sq_max_neg_zero (a : α) : max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by
  rcases le_total a 0 with ha | ha <;>
    simp only [max_eq_left, max_eq_right, ha, neg_nonneg, neg_nonpos] <;> ring

/-- The positive parts of `a` and `b`, and their negative parts, are together no farther apart
in squared distance than `a` and `b`. -/
theorem sq_max_zero_sub_add_sq_max_neg_zero_sub_le (a b : α) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [max_eq_left, max_eq_right, ha, hb, neg_nonneg, neg_nonpos] <;> nlinarith
