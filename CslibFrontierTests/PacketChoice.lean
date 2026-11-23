/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.PacketChoice

public section

namespace Turing.MultiTapeATM.PacketChoice.Tests

open MultiTapeTM MultiTapeTM.PacketChoice QuantifiedWord
open Cslib.Circuits.Frontier.TensorNetwork

-- Two width-two fields 01 and 10 choose modes zero and one, once each.
private def twoRows : Context := ⟨3, 2, 0, 1, true, true, 6⟩
private def matching : Input := ⟨twoRows, [1, 1, 0]⟩
private def wrong : Input := ⟨twoRows, [2, 0, 0]⟩

example : plays (fun xs => check (matching, xs) = true) [] (flags matching.context) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

example : ¬ plays (fun xs => check (wrong, xs) = true) [] (flags wrong.context) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- A two-mode field has width two, so code three is padding and must be rejected.
example : ¬ plays (fun xs => check (⟨⟨2, 1, 0, 1, true, true, 3⟩, []⟩, xs) = true)
    [] (flags ⟨2, 1, 0, 1, true, true, 3⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- A nontarget mode is forbidden even if its proposed count agrees.
example : ¬ plays (fun xs => check (⟨⟨2, 1, 0, 1, false, true, 1⟩, [1, 0]⟩, xs) = true)
    [] (flags ⟨2, 1, 0, 1, false, true, 1⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- Exponents of modes outside the target set do not constrain the coefficient.
example : plays (fun xs => check (⟨⟨2, 1, 0, 1, false, true, 2⟩, [2 ^ 100, 1]⟩, xs) = true)
    [] (flags ⟨2, 1, 0, 1, false, true, 2⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- The empty row product still requires all target exponents to be zero.
example : ¬ plays (fun xs => check (⟨⟨1, 0, 0, 1, true, true, 0⟩, [1]⟩, xs) = true)
    [] (flags ⟨1, 0, 0, 1, true, true, 0⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- Missing dense exponent entries have the promised default-zero meaning.
example : plays (fun xs => check (⟨⟨3, 0, 0, 1, true, true, 0⟩, []⟩, xs) = true)
    [] (flags ⟨3, 0, 0, 1, true, true, 0⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- With zero modes, zero-width row fields select only the local term, with no universal bits.
theorem zero_modes_local_fields :
    plays (fun xs => check (⟨⟨0, 2, 0, 0, true, true, 0⟩, [2 ^ 100]⟩, xs) = true)
    [] (flags ⟨0, 2, 0, 0, true, true, 0⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

-- An oversized target exponent is rejected by the same native linear-comparison terminal.
example : ¬ plays (fun xs => check (⟨⟨1, 0, 0, 1, true, true, 0⟩, [2 ^ 100]⟩, xs) = true)
    [] (flags ⟨1, 0, 0, 1, true, true, 0⟩) := by
  rw [plays_check]
  unfold CoeffWordSum.Valid
  decide

/- One actual finite machine accepts the matching assignment and rejects the wrong multiplicities
for every host input, with the native clock from the public theorem. -/
example :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ host : List Bool,
        let accepts := fun a : Input =>
          atm.AcceptsWithin (C * ((encList encNat a.exponents).length + shortSize a ^ D + 1))
            (SharedWordFork.start src atm host (encInput a) 0)
        accepts matching ∧ ¬ accepts wrong := by
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := exists_evaluator
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host accepts
  refine ⟨(h host matching).2.mpr (by unfold CoeffWordSum.Valid; decide), ?_⟩
  intro ha
  have hv := (h host wrong).2.mp ha
  have hbad : ¬ CoeffWordSum.Valid wrong.context.modes wrong.context.rows
      wrong.context.modes.size (targets wrong.context) (fun k => wrong.exponents.getD k 0)
      wrong.context.assignment := by
    unfold CoeffWordSum.Valid
    decide
  exact hbad hv

end Turing.MultiTapeATM.PacketChoice.Tests
