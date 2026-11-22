/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveWordSum

/-!
One fixed raw-request machine is tested at heights zero and one with arbitrary source and
context words. Its one-step native leaf supplies an all-ones pair at width three. The pair has
integer value fourteen, so the two heights return six and four modulo eight. Every output bit
and both claims are covered, including the carry and modular wrap in the positive-height case.
-/

namespace CslibFrontierTests.CarrySaveWordSum

open Turing Turing.MultiTapeATM Turing.MultiTapeATM.CarrySaveWordSum
open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery Cslib.BitString
open Cslib.Circuits.Boolean.CarryLookahead.Query

private noncomputable def leaf (_carry claim : Bool) : MultiTapeATM 12 Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ _ =>
    ⟨0, fun _ => (none, 0), some claim, none⟩)) (fun _ => false)

private theorem next_leaf {T : Type} {input : List Bool} (cfg : Cfg 12 Bool T input)
    (carry claim move : Bool) :
    (leaf carry claim).next move (cfg.withState (some ())) =
      { cfg.withState none with output := cfg.output ++ [claim] } := by
  rw [leaf, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [Action.apply, Cfg.withState]

private theorem leaf_bound (input : List Bool) (scratch : CarrySaveStream.Scratch 6)
    (sizeBudget : ℕ) : CarrySaveStream.LeafBound leaf 1 sizeBudget input scratch := by
  intro height bits path unary frontier status carry claim _ _
  apply haltsWithin_succ.mpr
  intro move
  rw [show (leaf carry claim).toPTM.toNTM.q₀ = () from rfl, next_leaf]
  apply haltsWithin_of_halted
  rfl

private theorem leaf_correct (input : List Bool) (scratch : CarrySaveStream.Scratch 6)
    (sizeBudget : ℕ) :
    CarrySaveStream.LeafCorrect (w := 3) (fun _ _ => true) leaf 1 sizeBudget input scratch := by
  intro height bits path unary frontier status carry claim _ _ hbits
  rw [acceptsWithin_succ_of_existential _ rfl rfl]
  simp only [show (leaf carry claim).toPTM.toNTM.q₀ = () from rfl, next_leaf]
  cases carry <;> cases claim <;>
    simp [AcceptsWithin, Cfg.withState, CarrySaveQuery.value, component, tree, hbits,
      fstBits, sndBits, Fin.appendEquiv]

private theorem expected_value (height : Fin 2) (bit : Fin 3) :
    (carryLookaheadAdd 3).eval interpretation (tree (fun _ _ => true) height.val []) bit =
      (if height.val = 0 then 6 else 4).testBit bit.val := by
  rw [← testBit_equivFin ((carryLookaheadAdd 3).eval interpretation
    (tree (fun _ _ => true) height.val [])) bit, val_eval_carryLookaheadAdd_pair,
    pairVal_tree_mod]
  have hp : pairVal (fun _ : Fin (3 + 3) => true) = 14 := by decide
  fin_cases height <;> simp [leafSum, hp]

-- The existential machine is outside all runtime choices, including height and the long words.
example : ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM K Bool Q) (C D : ℕ),
    ∀ (input context : List Bool) (height : Fin 2) (bit : Fin 3) (claim : Bool),
      let request : Request := ⟨context, height.val, ⟨3, bit.val, claim⟩⟩
      let start := SharedWordFork.start source atm input (encRequest request) 0
      let time := C * (context.length + height.val +
        ((CountingInput.encInput ⟨height.val, request.query⟩).length + 1) ^ D + 1) + 1
      atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
        (if height.val = 0 then 6 else 4).testBit bit.val = claim) := by
  obtain ⟨K, source, Q, hQ, atm, C, D, h⟩ := exists_evaluator leaf
  refine ⟨K, source, Q, hQ, atm, C, D, ?_⟩
  intro input context height bit claim request start time
  have hs := h input context height.val 3 1 (fun _ _ => true)
    (leaf_bound input _ _) (leaf_correct input _ _) bit claim
  exact ⟨hs.1, hs.2.trans (by rw [expected_value])⟩

end CslibFrontierTests.CarrySaveWordSum
