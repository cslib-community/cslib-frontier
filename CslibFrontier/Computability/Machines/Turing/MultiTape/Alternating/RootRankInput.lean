/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingPair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPortRank

/-!
# Root graph rank bits from an external request

The class-rank machine and the port-rank machine start on an ordinary encoded input with all
work tapes blank. The source machine's input is independent of the physical counting request.
Both rank computations retain the linear raw schedule charge after parsing their inputs.
-/

public section

namespace Turing.MultiTapeATM.RootRankInput

open MultiTapeTM MultiTapePTM Cslib Cslib.Circuits.Frontier
open Cslib.Circuits.Boolean.CarryLookahead.Query
open RootPredecessorGraph (edgeCount vertexCount)
open CarryLookaheadCountingPair (encInput exists_evaluator_on_pair)

/-- On the encoded root graph, seed, edge and counting parameters, an ordinary alternating
machine checks any bit of the seeded class rank of the genuine numbered edge. -/
theorem exists_classRank_evaluator (k : ℕ) :
    ∃ (tapes : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM tapes Bool Q) (C E : ℕ),
      ∀ {q copies a : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
        (e : Fin (edgeCount k q copies)) (w : ℕ) (bit : Fin w) (claim : Bool),
        let n := edgeCount k q copies
        let arg := RootPredecessorGraph.graphInput k q copies σ a seed e e
        let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := atm.toPTM.toNTM.initCfg (encInput (RootPredecessorContext.word arg, params))
        let time := C * (arg.raw.length +
          (RootPredecessorQuery.shortSize arg + n.size + w.size + 1) ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (PacketPacking.Seeded.rank (vertexCount k q copies) a
            (explicitVertexEquiv k q copies).toEmbedding
            (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
            seed e).testBit bit.val = claim) := by
  obtain ⟨d, hd⟩ := RootPredecessorContext.exists_computableInO k
  obtain ⟨u, Q, hQ, atm, C, E, h⟩ := exists_evaluator_on_pair RootPredecessorContext.word
    (fun a => a.raw.length) RootPredecessorQuery.shortSize _ hd d (fun a => by
      have hw := RootPredecessorContext.length_word_le a
      rw [RootPredecessorQuery.length_encInput] at hw
      unfold RootPredecessorQuery.shortSize
      omega) (fun a j => by
      rw [RootPredecessorContext.inputOf_word]
      exact Nat.add_le_add_left (Nat.pow_le_pow_left
        (RootPredecessorContext.shortSize_withCandidate_le a j) d) _)
  refine ⟨u, Q, hQ, atm, C, E, ?_⟩
  intro q copies a State M input b σ code seed e w bit claim
  simpa only [RootPredecessorContext.predicate_word, RootPackingRank.sum_eq_rank M input b σ code
    a seed e] using h (RootPredecessorGraph.graphInput k q copies σ a seed e e)
      (edgeCount k q copies) w bit claim

/-- A blank-tape machine checks a bit of the row or column port prefix rank in the actual
root child. Taking the complete prefix also gives the port total. -/
theorem exists_portRank_evaluator (k : ℕ) :
    ∃ (tapes : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM tapes Bool Q) (C E : ℕ),
      ∀ {q copies a : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
        (i : Fin a) (column : Bool) (g : ℕ) {bound : ℕ} (_hb : bound ≤ edgeCount k q copies)
        (w : ℕ) (bit : Fin w) (claim : Bool),
        let n := edgeCount k q copies
        let arg := RootPortRank.graphInput k q copies σ a seed i column g bound
        let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := atm.toPTM.toNTM.initCfg (encInput (RootPortContext.word arg, params))
        let time := C * (arg.2.raw.length +
          (RootPortQuery.shortSize arg + n.size + w.size + 1) ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (NativeChild.portRank (RootPortGraph.groups seed i) g
            (RootPortGraph.ends (q := q) M input b σ code) (RootPortGraph.side column)
            bound).testBit bit.val = claim) := by
  obtain ⟨d, hd⟩ := RootPortContext.exists_computableInO k
  obtain ⟨u, Q, hQ, atm, C, E, h⟩ := exists_evaluator_on_pair RootPortContext.word
    (fun a => a.2.raw.length) RootPortQuery.shortSize _ hd d RootPortContext.length_word_le
    (fun a j => by
      rw [RootPortContext.inputOf_word]
      exact Nat.add_le_add_left (Nat.pow_le_pow_left
        (RootPortContext.shortSize_withCandidate_le a j) d) _)
  refine ⟨u, Q, hQ, atm, C, E, ?_⟩
  intro q copies a State M input b σ code seed i column g bound hb w bit claim
  simpa only [RootPortRank.sum_eq_portRank M input b σ code seed i column g hb] using
    h (RootPortRank.graphInput k q copies σ a seed i column g bound)
      (edgeCount k q copies) w bit claim

end Turing.MultiTapeATM.RootRankInput
