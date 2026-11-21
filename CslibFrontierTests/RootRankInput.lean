/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootRankInput

open Turing Turing.MultiTapePTM Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query

-- The first half-edge has no predecessors. From ordinary blank work tapes, the same machine
-- accepts the false claim and rejects the true claim about its low rank bit.
example {State : Type} (M : MultiTapePTM 0 Bool State) (input : List Bool) (b σ a : ℕ)
    (code : BlockLetter 0 State b → Fin 1 → Bool)
    (seed : BalancedSchedules.SeededLabels.Seed (RootPredecessorGraph.vertexCount 0 1 1) (6 * a)) :
    ∃ (tapes : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM tapes Bool Q) (time : ℕ),
      let e : Fin (RootPredecessorGraph.edgeCount 0 1 1) := 0
      let arg := RootPredecessorGraph.graphInput 0 1 1 σ a seed e e
      let start (claim : Bool) := atm.toPTM.toNTM.initCfg
        (CarryLookaheadCountingPair.encInput
          (RootPredecessorContext.word arg, ⟨2, ⟨1, 0, claim⟩⟩))
      atm.HaltsWithin time (start false) ∧ atm.HaltsWithin time (start true) ∧
        atm.AcceptsWithin time (start false) ∧ ¬atm.AcceptsWithin time (start true) := by
  obtain ⟨u, Q, hQ, atm, C, E, h⟩ := RootRankInput.exists_classRank_evaluator 0
  let e : Fin (RootPredecessorGraph.edgeCount 0 1 1) := 0
  have hz : PacketPacking.Seeded.rank _ a (explicitVertexEquiv 0 1 1).toEmbedding
      (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf 0 1 1)
      seed e = 0 := by
    rw [PacketPacking.Seeded.rank_eq_sum_predecessors]
    simp [PacketPacking.Seeded.predecessor, e]
  have hf := h M input b σ code seed e 1 0 false
  have ht := h M input b σ code seed e 1 0 true
  refine ⟨u, Q, hQ, atm, _, hf.1, ht.1, hf.2.mpr ?_, fun hacc => ?_⟩
  · rw [hz]
    rfl
  · have := ht.2.mp hacc
    rw [hz] at this
    contradiction
