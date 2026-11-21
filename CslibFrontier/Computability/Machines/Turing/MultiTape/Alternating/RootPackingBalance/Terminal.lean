/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingPair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest

/-!
# The physical continuation for a completed balance challenge

The choice word and the retained public data are one serialized request on the work tape. A
native loader rewinds that tape and prepares the two count-machine inputs. For a constant
answer it requests bit zero of an empty count. The same alternating machine executes both
constant decisions and genuine rank queries.
-/

public section
namespace Turing.MultiTapeATM.RootPackingBalance

open MultiTapeTM Cslib Circuits.Boolean.CarryLookahead.Query
open RootBalanceRequest (Input encInput challenge prepare selected shortSize rootQuery)

/-- The result of executing the count request prepared from a completed challenge. -/
@[expose] def terminalValue (k : ℕ) (x : Input) : Prop :=
  let p := (prepare x).2
  (∑ j ∈ Finset.range p.count, (RootPredecessorQuery.query k
    (RootPredecessorContext.withCandidate (selected x) j)).toNat).testBit p.query.bit =
      p.query.claim

/-- A sharp native preparation may decode additional fields before entering the rank terminal. -/
theorem exists_terminal_of_prepare {α : Type} (k : ℕ) {enc : α ↪ List Bool} (model : α → Input)
    {T : α → ℕ}
    (hd : ComputableInO (fun z => prepare (model z)) enc RootBalanceRequest.encOutput T T) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q)
      (c A D : ℕ), ∀ (input : List Bool) (z : α),
      let x := model z
      let p := (prepare x).2
      let start := WordGameLeaf.config src (some atm.toPTM.initial) (enc z) (enc z).length
        (TerminalLayout.blank U input)
      let countTime := A * ((selected x).raw.length + (RootPredecessorQuery.shortSize (selected x) +
        p.count.size + p.query.width.size + 1) ^ D + 1)
      let time := (enc z).length + c * (T z + 1) +
        8 + countTime
      atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ terminalValue k x) := by
  obtain ⟨s, u, r, v, S, hS, rank, A, D, h⟩ := RootPackingRank.exists_evaluator k
  let hf := (ComputableInDegree.fst encBits CountingInput.encInput).inO_one.comp_linear hd
  let hg := (ComputableInDegree.snd encBits CountingInput.encInput).inO_one.comp_linear hd
  obtain ⟨U, src, Q, hQ, atm, c, ht⟩ := TerminalLayout.exists_load hf hg
    (CarryLookaheadCountingPair.contextTape s u r v) (CarryLookaheadCountingPair.paramTape s u r v)
    (CarryLookaheadCountingPair.contextTape_ne_paramTape s u r v) rank
  refine ⟨U, src, Q, hQ, atm, c, A, D, ?_⟩
  intro input z
  let x := model z
  let p := (prepare x).2
  have hv : p.query.bit < p.query.width := SeededRankRequest.valid_bit (challenge x)
  obtain ⟨hh, ha⟩ := h input (selected x) p.count p.query.width ⟨p.query.bit, hv⟩ p.query.claim
  rw [CarryLookaheadCountingPair.initial_eq_ready] at hh ha
  obtain ⟨hh', ha'⟩ := ht input z _ hh
  exact ⟨hh', ha'.trans ha⟩

/-- The whole terminal starts on the final choice tape and actually runs the native rank ATM.
Its clock accounts for the rewind, both protected words and the ensuing count branch. -/
theorem exists_terminal (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q)
      (c d A D : ℕ), ∀ (input : List Bool) (x : Input),
      let p := (prepare x).2
      let start := WordGameLeaf.config src (some atm.toPTM.initial) (encInput x) (encInput x).length
        (TerminalLayout.blank U input)
      let countTime := A * ((selected x).raw.length + (RootPredecessorQuery.shortSize (selected x) +
        p.count.size + p.query.width.size + 1) ^ D + 1)
      let time := (encInput x).length + c * ((rootQuery x).raw.length + shortSize x ^ d + 1) +
        8 + countTime
      atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ terminalValue k x) := by
  obtain ⟨d, hd⟩ := RootBalanceRequest.exists_computableInO
  obtain ⟨U, src, Q, hQ, atm, c, A, D, h⟩ := exists_terminal_of_prepare k id hd
  exact ⟨U, src, Q, hQ, atm, c, d, A, D, h⟩

end Turing.MultiTapeATM.RootPackingBalance
