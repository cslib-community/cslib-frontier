/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Normed/Module/Normalize.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Normalize

/-! # Norm bound for normalized vectors -/

public section

namespace NormedSpace

/-- Normalization maps the space into the closed unit ball. -/
theorem norm_normalize_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : ‖NormedSpace.normalize v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [NormedSpace.norm_normalize hv]

end NormedSpace
