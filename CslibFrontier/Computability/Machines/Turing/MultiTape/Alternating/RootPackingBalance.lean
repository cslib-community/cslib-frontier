/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingRank
public import CslibFrontier.Computability.PolyTime.SeededRankCapacity
public import CslibFrontier.Foundations.Combinatorics.SeededPackingRank.Balance

/-!
# Local balance checks for a seeded root packing

A universal edge challenge and one bounded rank guess per edge suffice. The native capacity
predicate rejects oversized ranks. Every bit of a surviving guess can be challenged on the
same rank machine, initialized with the represented schedule and the same seed. The edge and
guess quantifiers are logical in this interface. The bounded machine checks each bit claim.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance

open MultiTapeTM MultiTapePTM Cslib Cslib.Circuits.Boolean.CarryLookahead.Query
open RootPredecessorGraph (graphInput edgeCount vertexCount)

/-- The claimed bit is verified on the native rank machine within its actual branch budget. -/
def checksBit {scratch u r v : ℕ} {S : Type}
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch u r v) Bool S)
    (C E : ℕ) (input : List Bool) (arg : RootPredecessorQuery.Input) (n w j : ℕ) (claim : Bool) :
    Prop :=
  CarryLookaheadCountingFromParametersCost.checksBit
    (scratch := scratch) (u := u) (r := r) (t := v) atm C E input
    (RootPredecessorContext.word arg) arg.raw.length (RootPredecessorQuery.shortSize arg)
    n w j claim

/-- Balance of any proposed seed is equivalent to bounded local guesses, a native capacity
check and clocked verification of every bit. One machine works uniformly for all root graphs
with the fixed source tape count. The empty edge universe requires no edge challenge. -/
theorem exists_local_verifier (k : ℕ) :
    ∃ (scratch u r v : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch u r v) Bool S) (C E : ℕ),
      ∀ {q copies : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool) (a : ℕ)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a)),
        let n := edgeCount k q copies
        let w := Nat.clog 2 n
        PacketPacking.Seeded.Balanced (vertexCount k q copies) a
          (explicitVertexEquiv k q copies).toEmbedding
          (RootPredecessorGraph.rowOf machine input b σ code)
          (RootPredecessorGraph.colOf k q copies) seed ↔
          ∀ e : Fin n, ∃ g : Fin (2 ^ w), SeededRankCapacity.fits ⟨n, a, g.val⟩ = true ∧
            ∀ j : Fin w, checksBit (scratch := scratch) (u := u) (r := r) (v := v) atm C E input
              (graphInput k q copies σ a seed e e) n w j.val (g.val.testBit j.val) := by
  obtain ⟨s, u, r, v, S, hS, atm, C, E, h⟩ := RootPackingRank.exists_rank_evaluator k
  refine ⟨s, u, r, v, S, hS, atm, C, E, ?_⟩
  intro q copies State machine input b σ code a seed
  let n := edgeCount k q copies
  let w := Nat.clog 2 n
  let check := fun (e : Fin n) (j : Fin w) claim =>
    checksBit (scratch := s) (u := u) (r := r) (v := v) atm C E input
      (graphInput k q copies σ a seed e e) n w j.val claim
  have hw : Fintype.card (Fin n) ≤ 2 ^ w := by
    simpa only [Fintype.card_fin] using Nat.le_pow_clog (by decide : 1 < 2) n
  have hv := PacketPacking.Seeded.balanced_iff_rank_bit_checks (vertexCount k q copies) a
    (explicitVertexEquiv k q copies).toEmbedding (RootPredecessorGraph.rowOf machine input b σ code)
    (RootPredecessorGraph.colOf k q copies) seed hw check (by
      intro e j claim
      obtain ⟨hh, ha⟩ := h machine input b σ code a seed e w j claim
      exact ⟨fun hc => ha.mp hc.2, fun ht => ⟨hh, ha.mpr ht⟩⟩)
  simpa only [Fintype.card_fin, SeededRankCapacity.fits_eq_true_iff] using hv

end Turing.MultiTapeATM.RootPackingBalance
