/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.QueryComplexity.Randomized.Nisan
import CslibFrontier.Computability.QueryComplexity.Threshold

/-! The linear randomized probe lower bound for majority
([Goldreich, Exercise 10.8][Goldreich2007DraftR5]): on executed probes, under the strict tie
convention, and at a concrete input length. -/

set_option linter.privateModule false

namespace CslibFrontierTests.QueryComplexity.MajorityLowerBound

open Cslib Cslib.QueryComplexity

/-- At length `100`, some input and coin outcome execute at least `17` probes. -/
example {μ : RandomizedDecisionTree (Fin 100) Bool} (hμ : μ.Computes (1 / 3 : ℝ) (majority 100)) :
    ∃ x, ∃ t ∈ μ.weights.support, 17 ≤ t.cost x := by
  obtain ⟨x, t, ht, h⟩ := hμ.exists_div_two_add_one_le_three_mul_cost_majority (by norm_num)
  exact ⟨x, t, ht, by omega⟩

/-- The strict tie convention (`⌊n/2⌋ + 1` ones, as in the main text) gives the same bound. -/
example {n : ℕ} (hn : 1 ≤ n) {μ : RandomizedDecisionTree (Fin n) Bool}
    (hμ : μ.Computes (1 / 3 : ℝ) (threshold n (n / 2 + 1))) :
    ∃ x, ∃ t ∈ μ.weights.support, n / 2 + 1 ≤ 3 * t.cost x := by
  obtain ⟨x, t, ht, h⟩ := hμ.exists_one_sub_two_mul_mul_blockSensitivity_le_cost
  have hbs : blockSensitivity (threshold n (n / 2 + 1)) = n / 2 + 1 := by
    rw [blockSensitivity_threshold (by omega) (by omega)]
    omega
  rw [hbs] at h
  refine ⟨x, t, ht, ?_⟩
  have : ((n / 2 + 1 : ℕ) : ℝ) ≤ 3 * (t.cost x : ℝ) := by
    push_cast at h ⊢
    linarith
  exact_mod_cast this

/-- The complexity form: majority of `100` bits needs at least `17` queries with error `1/3`. -/
example : 17 ≤ randomizedComplexity (1 / 3) (majority 100) := by
  have := div_two_add_one_le_three_mul_randomizedComplexity_majority (n := 100) (by norm_num)
  omega

end CslibFrontierTests.QueryComplexity.MajorityLowerBound
