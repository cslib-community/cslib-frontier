/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingRank

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib
open Cslib.Circuits.Boolean.CarryLookahead.Query

-- The first genuine half-edge has rank zero for every seed. The same finite machine halts
-- and distinguishes the two proposed low bits from the prepared root context.
example :
    ∃ (s u r v : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size s u r v) Bool S) (C D : ℕ),
      ∀ {State : Type} (_machine : MultiTapePTM 0 Bool State) (input : List Bool) (b a : ℕ)
        (_code : MultiTapePTM.BlockLetter 0 State b → Fin 1 → Bool)
        (seed : BalancedSchedules.SeededLabels.Seed
          (RootPredecessorGraph.vertexCount 0 1 1) (6 * a))
        (claim : Bool),
        let arg := RootPredecessorGraph.graphInput 0 1 1 0 a seed 0 0
        let params : CountingInput.Input := ⟨2, ⟨1, 0, claim⟩⟩
        let cfg := (CarryLookaheadCountingPrepare.initial s u r v input
          (RootPredecessorContext.word arg) params).withState (some atm.toPTM.initial)
        let time := C * (arg.raw.length + (RootPredecessorQuery.shortSize arg + 2 + 1 + 1) ^ D + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔ false = claim) := by
  obtain ⟨s, u, r, v, S, hS, atm, C, D, h⟩ := RootPackingRank.exists_rank_evaluator 0
  refine ⟨s, u, r, v, S, hS, atm, C, D, ?_⟩
  intro State machine input b a code seed claim
  obtain ⟨hh, ha⟩ := h machine input b 0 code a seed 0 1 0 claim
  refine ⟨hh, ha.trans ?_⟩
  rw [PacketPacking.Seeded.rank_eq_sum_predecessors]
  simp [PacketPacking.Seeded.predecessor]
