/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib general order lemma)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Basic.Real.Basic

/-!
# Finite nonnegative weights on the extended reals

Multiplying an extended real by a finite nonnegative real preserves order.
The zero-weight case remains valid when one of the compared values is infinite.

## Main results

* `WithTop.mul_le_mul_of_nonneg_coe_left`: multiply an inequality by a finite
  nonnegative real on the left.
-/

public section

namespace WithTop

/-- A finite nonnegative left multiplier preserves order on `WithTop ℝ`. -/
theorem mul_le_mul_of_nonneg_coe_left {a : ℝ} (ha : 0 ≤ a)
    {b c : WithTop ℝ} (h : b ≤ c) : (a : WithTop ℝ) * b ≤ (a : WithTop ℝ) * c := by
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha]
  · exact (WithTop.mul_right_strictMono (WithTop.coe_pos.mpr ha)
      WithTop.coe_ne_top).monotone h

end WithTop
