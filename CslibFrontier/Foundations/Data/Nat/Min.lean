/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Init.lean`)

public import CslibFrontier.Init

/-!
# Saturating natural-number addition

Capping an accumulator before adding a nonnegative increment does not change the final capped
sum. This permits bounded counters to compute sums without storing uncapped intermediate values.
-/

public section

namespace Nat

/-- Capping a summand at the final cap does not change a saturated natural-number sum. -/
theorem min_min_add (n a b : ℕ) : min n (min n a + b) = min n (a + b) := by
  omega

end Nat
