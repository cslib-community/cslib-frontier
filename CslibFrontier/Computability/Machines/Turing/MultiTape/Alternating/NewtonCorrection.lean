/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.NewtonCorrection
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting

/-! # The native finishing adder for Newton's correction term -/

public section
namespace Turing.MultiTapeATM.NewtonCorrection

open MultiTapeTM Cslib GaloisRingArith Cslib.Circuits.Boolean
open Cslib.Circuits.Frontier.FastContraction
open Cslib.Circuits.Frontier.FastContraction.NewtonCorrection

/-- One machine verifies a bit of the factor `2-z`. Its local left operand is one
or three, while a right operand calls for one bit of `z` with reversed polarity.
The caller's clock is charged once. -/
theorem exists_evaluator {k : ℕ} {S : Type} [Finite S]
    (roots : Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool Q) (c e : ℕ),
      ∀ (input context : List Bool) (m p time : ℕ) (z : Ring p (modulus m))
        (i : Fin (modulus m).length),
        (∀ (j : Fin p) (right claim : Bool),
          let cfg := (CarrySaveCountingRoot.initial k input context 1 p j.val).withState
            (some (roots right claim).toPTM.initial)
          (roots right claim).HaltsWithin time cfg ∧
            ((roots right claim).AcceptsWithin time cfg ↔
              (if right then !((representative m p z).coeff i.val).val.testBit j.val
                else (offset i.val).testBit j.val) = claim)) →
        ∀ (j : Fin p) (claim : Bool),
          let cfg := (CarryLookaheadCounting.initial k r q input context 1 p j.val
            claim).withState (some atm.toPTM.initial)
          let clock := CarryLookaheadCounting.clockOfRoot c e p time
          atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
            ((representative m p (2 - z)).coeff i.val).val.testBit j.val = claim) := by
  obtain ⟨r, T, fin, terminal, a, b, ht⟩ := CountingTerminal.exists_terminal_for_pair roots
  obtain ⟨q, Q, fin', atm, c, e, h⟩ :=
    CarryLookaheadCounting.exists_finisher_for_pair terminal a b
  refine ⟨r, q, Q, fin', atm, c, e, ?_⟩
  intro input context m p time z i hroots j claim
  let v := pair i.val (representative m p z)
  have hv := ht input context 1 p time v (by
    intro idx right val
    simpa only [v, component_pair] using hroots idx right val)
  obtain ⟨hh, ha⟩ := h input context 1 p time v hv j claim
  exact ⟨hh, ha.trans (by simp only [v, bit_sum])⟩

end Turing.MultiTapeATM.NewtonCorrection
