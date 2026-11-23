/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.IndependentSet

/-! Checked clients for [Goldreich2007DraftR5], Exercise 10.4: the existential form "for some
constants `0 < s < L < 1`, `gapVC_{s,L}` is NP-hard", and a yes-instance of the gap problem: the
graph with one vertex and no edge has cover number `0 ≤ s * 1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GapVertexCoverFraction

open Cslib.Complexity

-- Exercise 10.4 as printed.
example : ∃ s L : ℝ, 0 < s ∧ s < L ∧ L < 1 ∧
    PromiseProblem.NPHard encGraph (GapVertexCoverFraction s L) :=
  ⟨_, _, by norm_num, by norm_num, by norm_num, GapVertexCoverFraction_npHard⟩

-- A yes-instance: a cover of no vertices suffices without edges.
example : (⟨[0], []⟩ : Graph) ∈ (GapVertexCoverFraction (2 / 3) (3 / 4)).yes := by
  have h := Graph.vertexCoverNum_le_of_mem_VertexCover (G := ⟨[0], []⟩) (k := 0)
    (mem_VertexCover_iff.2 ⟨∅, by simp, by simp [Graph.toSimpleGraph_adj], by simp⟩)
  change ((Graph.vertexCoverNum ⟨[0], []⟩ : ℕ) : ℝ) ≤ _
  rw [Nat.le_zero.1 h]
  norm_num

end CslibFrontierTests.GapVertexCoverFraction
