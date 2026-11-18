/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.QueryComplexity.Randomized.Nisan

/-! The linear randomized query lower bound for majority
([Goldreich, Exercise 10.8][Goldreich2007DraftR5]) applied to a single randomized decision tree,
and at a concrete input length. -/

set_option linter.privateModule false

namespace CslibFrontierTests.QueryComplexity.MajorityLowerBound

open Cslib Cslib.QueryComplexity

/-- Every randomized decision tree computing majority with error `1/3` has depth at least
`(⌊n/2⌋ + 1) / 3`. -/
example {n : ℕ} (hn : 1 ≤ n) {μ : RandomizedDecisionTree (Fin n) Bool}
    (hμ : μ.Computes (1 / 3 : ℝ) (majority n)) :
    n / 2 + 1 ≤ 3 * μ.depth :=
  (div_two_add_one_le_three_mul_randomizedComplexity_majority hn).trans
    (Nat.mul_le_mul_left 3 (randomizedComplexity_le_depth hμ))

/-- Majority of `100` bits needs at least `17` queries with error `1/3`. -/
example : 17 ≤ randomizedComplexity (1 / 3) (majority 100) := by
  have := div_two_add_one_le_three_mul_randomizedComplexity_majority (n := 100) (by norm_num)
  omega

end CslibFrontierTests.QueryComplexity.MajorityLowerBound
