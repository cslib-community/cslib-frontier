/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Normed/Module/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The distance between a vector and its negative

In a real normed space a vector `x` and `-x` are at distance `2 ‖x‖` (`dist_self_neg`).

## Main results

* `dist_self_neg`: `dist x (-x) = 2 * ‖x‖`.
-/

public section

/-- A vector and its negative are at distance twice its norm. -/
theorem dist_self_neg {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    dist x (-x) = 2 * ‖x‖ := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul, Real.norm_two]
