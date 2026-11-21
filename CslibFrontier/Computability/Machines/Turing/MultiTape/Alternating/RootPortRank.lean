/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortGraph

/-!
# Alternating bit queries for row and column port ranks of a root child

One finite alternating machine counts candidate parent ports using a fixed seed, coordinate,
side and group. The prefix can be any number from zero through the complete edge count, so the
same machine supplies the row-port total needed to offset column ranks. Its clock charges
linearly for the raw schedule and polynomially for the short metadata and counting parameters.
-/

public section

namespace Turing.MultiTapeATM.RootPortRank

open MultiTapeTM MultiTapePTM Cslib Cslib.Circuits.Frontier
open RootPredecessorGraph (edgeCount vertexCount inputOfIndices)
open Cslib.Circuits.Boolean.CarryLookahead.Query

/-- The fixed port and prefix, before the counter supplies its candidate index. -/
@[expose] def graphInput (k q copies σ a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (i : Fin a) (column : Bool) (g bound : ℕ) : RootPortQuery.Input :=
  (⟨column, i.val, g⟩, inputOfIndices k q copies σ a seed bound 0)

/-- For a represented root graph, the emitted sum on its stored context equals the native
child's row or column prefix rank. -/
theorem sum_eq_portRank {k q copies a : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (i : Fin a) (column : Bool) (g : ℕ) {bound : ℕ} (hb : bound ≤ edgeCount k q copies) :
    (∑ j ∈ Finset.range (edgeCount k q copies), (RootPortContext.predicate k
      (RootPortContext.word (graphInput k q copies σ a seed i column g bound), j)).toNat) =
        NativeChild.portRank (RootPortGraph.groups seed i) g
          (RootPortGraph.ends (q := q) machine input b σ code)
          (RootPortGraph.side column) bound := by
  rw [RootPortGraph.portRank_eq_sum_query machine input b σ code seed i column g hb,
    ← Fin.sum_univ_eq_sum_range]
  simp only [RootPortContext.predicate_word]
  rfl

/-- A single native alternating machine decides every claimed bit of a root child's port prefix
rank. The clock covers every path on the supplied context, including padded candidate indices. -/
theorem exists_portRank_evaluator (k : ℕ) :
    ∃ (scratch u r t : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch u r t) Bool S) (C E : ℕ),
      ∀ {q copies a : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
        (i : Fin a) (column : Bool) (g : ℕ) {bound : ℕ} (_hb : bound ≤ edgeCount k q copies)
        (w : ℕ) (bit : Fin w) (claim : Bool),
        let n := edgeCount k q copies
        let arg := graphInput k q copies σ a seed i column g bound
        let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch u r t input
          (RootPortContext.word arg) params).withState (some atm.toPTM.initial)
        let time := C * (arg.2.raw.length +
          (RootPortQuery.shortSize arg + n.size + w.size + 1) ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (NativeChild.portRank (RootPortGraph.groups seed i) g
            (RootPortGraph.ends (q := q) machine input b σ code) (RootPortGraph.side column)
            bound).testBit bit.val = claim) := by
  obtain ⟨d, hd⟩ := RootPortContext.exists_computableInO k
  obtain ⟨s, u, r, t, S, hS, atm, C, E, h⟩ :=
    CarryLookaheadCountingFromParametersCost.exists_evaluator_on_context
      RootPortContext.word (fun a => a.2.raw.length) RootPortQuery.shortSize _ hd d
      RootPortContext.length_word_le (fun a j => by
        rw [RootPortContext.inputOf_word]
        exact Nat.add_le_add_left (Nat.pow_le_pow_left
          (RootPortContext.shortSize_withCandidate_le a j) d) _)
  refine ⟨s, u, r, t, S, hS, atm, C, E, ?_⟩
  intro q copies a State machine input b σ code seed i column g bound hb w bit claim
  simpa only [sum_eq_portRank machine input b σ code seed i column g hb] using
    h input (graphInput k q copies σ a seed i column g bound) (edgeCount k q copies) w bit claim

end Turing.MultiTapeATM.RootPortRank
