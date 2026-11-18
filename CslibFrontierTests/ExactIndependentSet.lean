/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.IndependentSet.Exact

/-! `EXACT INDSET ∈ DP` ([Arora and Barak, Exercise 5 §8(a)][AroraBarak07]) and its membership
condition on instances: every graph is in `EXACT INDSET` at its independence number and at no
larger target. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ExactIndependentSet

open Cslib Cslib.Complexity

example : ExactIndependentSet ∈ DP encIndependentSetInstance := ExactIndependentSet_mem_DP

/-- Every graph is a member at its independence number. -/
example (G : Graph) : (⟨G, G.indepNum⟩ : IndependentSetInstance) ∈ ExactIndependentSet :=
  mem_ExactIndependentSet.2 rfl

/-- A target above the independence number is not a member, because no independent set of that
size exists. -/
example (G : Graph) : (⟨G, G.indepNum + 1⟩ : IndependentSetInstance) ∉ ExactIndependentSet :=
  fun h => absurd (mem_ExactIndependentSet_iff.1 h).1
    (by rw [← Graph.le_indepNum_iff]; omega)

end CslibFrontierTests.ExactIndependentSet
