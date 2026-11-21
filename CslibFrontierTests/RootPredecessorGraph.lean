/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorGraph

open Cslib Turing Turing.MultiTapeTM Turing.MultiTapeTM.RootPredecessorGraph

-- With two control intervals and one Boolean copy there are four half-edges. At label width
-- zero all three earlier half-edges contribute to the last edge's actual class rank.
example {State : Type} (machine : MultiTapePTM 0 Bool State) (input : List Bool) (b : ℕ)
    (code : MultiTapePTM.BlockLetter 0 State b → Fin 1 → Bool)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount 0 2 1) 0) :
    PacketPacking.Seeded.rank (vertexCount 0 2 1) 0
        (MultiTapePTM.explicitVertexEquiv 0 2 1).toEmbedding
        (rowOf machine input b 0 code) (colOf 0 2 1) seed 3 = 3 := by
  rw [rank_eq_sum_query]
  have h (j : Fin 4) :
      RootPredecessorQuery.query 0 (graphInput 0 2 1 0 0 seed 3 j) = decide (j.val < 3) := by
    rw [query_eq_predecessor machine input b 0 code]
    simp only [PacketPacking.Seeded.predecessor, decide_eq_decide]
    exact ⟨And.left, fun hj => ⟨hj, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  simp_rw [h]
  decide
