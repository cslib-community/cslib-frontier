/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPortRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortParent

/-!
# Clocked bit checks for a root child's parent half-edge

For each source tape count one alternating machine checks the selected bits of every needed
row or column count. The child address has the proposed parent exactly when a single bounded
row total passes its full-prefix bit checks and the appropriate row or column branch passes.
The column offset uses that same row total. Guessing the total and challenging its bits are
logical quantifiers in this contract.
-/

public section

namespace Turing.MultiTapeATM.RootPortParentBits

open MultiTapeTM MultiTapePTM Cslib Cslib.Circuits.Frontier
open RootPredecessorGraph (edgeCount vertexCount)
open RootPortParent (leaf prefixCount)
open Cslib.Circuits.Boolean.CarryLookahead.Query

/-- For each bit, run the same clocked machine with the candidate's corresponding bit value. -/
def verifies {scratch u r t : ℕ} {S : Type}
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch u r t) Bool S)
    (C E : ℕ) (input : List Bool) (arg : RootPortQuery.Input) (n w guess : ℕ) : Prop :=
  ∀ bit : Fin w, CarryLookaheadCountingFromParametersCost.checksBit
    (scratch := scratch) (u := u) (r := r) (t := t) atm C E input (RootPortContext.word arg)
    arg.2.raw.length (RootPortQuery.shortSize arg) n w bit.val (guess.testBit bit.val)

/-- The represented child's valid parent witnesses are exactly those passing bounded membership
and count tests. A width of `clog 2 (n + 1)` accommodates a full-prefix count equal to `n`. -/
theorem exists_local_verifier (k : ℕ) :
    ∃ (scratch u r t : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch u r t) Bool S) (C E : ℕ),
      ∀ {q copies a : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
        (i : Fin a) (g j e : ℕ),
        let n := edgeCount k q copies
        let w := Nat.clog 2 (n + 1)
        let es := RootPortGraph.ends (q := q) machine input b σ code
        let gs := RootPortGraph.groups seed i
        let check (column : Bool) (bound guess : ℕ) := verifies
          (scratch := scratch) (u := u) (r := r) (t := t) atm C E input
          (RootPortRank.graphInput k q copies σ a seed i column g bound) n w guess
        (j < (NativeChild.portEdges gs g es Prod.fst).length +
          (NativeChild.portEdges gs g es Prod.snd).length ∧ NativeChild.parentEdge gs g es j = e) ↔
          ∃ rows : Fin (2 ^ w), check false n rows.val ∧ e < n ∧
            ((leaf σ seed i g false n e = true ∧ j < 2 ^ w ∧ check false e j) ∨
              (leaf σ seed i g true n e = true ∧ rows.val ≤ j ∧ j - rows.val < 2 ^ w ∧
                check true e (j - rows.val))) := by
  obtain ⟨s, u, r, t, S, hS, atm, C, E, h⟩ := RootPortRank.exists_portRank_evaluator k
  refine ⟨s, u, r, t, S, hS, atm, C, E, ?_⟩
  intro q copies a State machine input b σ code seed i g j e
  let n := edgeCount k q copies
  let w := Nat.clog 2 (n + 1)
  have hw : n < 2 ^ w := Nat.le_pow_clog (by decide : 1 < 2) (n + 1)
  let check (column : Bool) (bound guess : ℕ) := verifies
    (scratch := s) (u := u) (r := r) (t := t) atm C E input
    (RootPortRank.graphInput k q copies σ a seed i column g bound) n w guess
  have hc (column : Bool) {bound : ℕ} (hb : bound ≤ n) (guess : ℕ) :
      check column bound guess ↔ ∀ bit : Fin w, guess.testBit bit.val =
        (prefixCount σ seed i g column bound).testBit bit.val := by
    apply forall_congr'
    intro bit
    obtain ⟨hh, ha⟩ := h machine input b σ code seed i column g hb w bit (guess.testBit bit.val)
    have hcount := RootPortGraph.portRank_eq_sum_query machine input b σ code seed i column g hb
    change NativeChild.portRank _ _ _ _ _ = prefixCount σ seed i g column bound at hcount
    rw [← hcount]
    exact ⟨fun hcheck => (ha.mp hcheck.2).symm, fun heq => ⟨hh, ha.mpr heq.symm⟩⟩
  constructor
  · intro hp
    let rows := prefixCount σ seed i g false n
    have hr : rows < 2 ^ w := (RootPortParent.prefixCount_le σ seed i g false n).trans_lt hw
    have hrows (bit : Fin w) : rows.testBit bit.val =
        (prefixCount σ seed i g false n).testBit bit.val := rfl
    obtain ⟨he, hbranch⟩ :=
      (RootPortParent.parentEdge_witness_iff_bits machine input b σ code seed i g hw hr hrows).mp hp
    refine ⟨⟨rows, hr⟩, (hc false le_rfl rows).mpr hrows, he, ?_⟩
    change (_ ∧ _ ∧ check false e j) ∨ (_ ∧ rows ≤ j ∧ _ ∧ check true e (j - rows))
    rw [hc false he.le j, hc true he.le (j - rows)]
    exact hbranch
  · rintro ⟨rows, hrows, he, hbranch⟩
    apply (RootPortParent.parentEdge_witness_iff_bits machine input b σ code seed i g hw rows.isLt
      ((hc false le_rfl rows.val).mp hrows)).mpr
    refine ⟨he, ?_⟩
    change (_ ∧ _ ∧ check false e j) ∨ (_ ∧ rows.val ≤ j ∧ _ ∧ check true e (j - rows.val))
      at hbranch
    rwa [hc false he.le j, hc true he.le (j - rows.val)] at hbranch

end Turing.MultiTapeATM.RootPortParentBits
