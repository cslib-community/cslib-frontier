/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.PacketValidity

public section

namespace Turing.MultiTapeATM.PacketValidity.Tests

open MultiTapeTM MultiTapeTM.PacketValidity QuantifiedWord
open Cslib Cslib.Circuits.Frontier TensorNetwork

/-- A two-row choice with matching target multiplicities and either asserted value. -/
@[expose] def matching (claim : Bool) : Input :=
  ⟨⟨⟨3, 2, 0, 1, true, true, 6⟩, 8, 0, 0, claim⟩, [1, 1, 0]⟩

/-- The same row choices with an incorrect multiplicity vector. -/
@[expose] def wrong (claim : Bool) : Input :=
  { matching claim with exponents := [2, 0, 0] }

private theorem value_matching (claim : Bool) : value (matching claim) = true := by
  classical
  change (true && _) = true
  rw [Bool.true_and, decide_eq_true_eq]
  dsimp only [matching]
  unfold CoeffWordSum.Valid
  decide

private theorem value_wrong (claim : Bool) : value (wrong claim) = false := by
  classical
  change (true && _) = false
  rw [Bool.true_and, decide_eq_false_iff_not]
  dsimp only [wrong, matching]
  unfold CoeffWordSum.Valid
  decide

-- Negating a claim changes both the terminal comparison and the owner of every choice bit.
example : plays (fun xs => check (matching true, xs) = true) [] (flags (matching true).header) := by
  rw [plays_check, value_matching]
  rfl

example : ¬ plays (fun xs => check (matching false, xs) = true)
    [] (flags (matching false).header) := by
  rw [plays_check, value_matching]
  decide

example : plays (fun xs => check (wrong false, xs) = true) [] (flags (wrong false).header) := by
  rw [plays_check, value_wrong]
  rfl

example : ¬ plays (fun xs => check (wrong true, xs) = true) [] (flags (wrong true).header) := by
  rw [plays_check, value_wrong]
  decide

-- No challenge bits are needed when there are no modes, for either polarity.
example (claim : Bool) :
    let a : Input := ⟨⟨⟨0, 2, 0, 0, true, true, 0⟩, 1, 0, 0, claim⟩, [2 ^ 100]⟩
    plays (fun xs => check (a, xs) = true) [] (flags a.header) ↔ claim = true := by
  dsimp only
  rw [plays_check]
  have hv : value ⟨⟨⟨0, 2, 0, 0, true, true, 0⟩, 1, 0, 0, claim⟩, [2 ^ 100]⟩ = true := by
    classical
    change (true && _) = true
    rw [Bool.true_and, decide_eq_true_eq]
    dsimp only
    unfold CoeffWordSum.Valid
    decide
  rw [hv]
  exact eq_comm

-- Precision zero, a nonconstant coefficient, and a nonzero bit all select zero, even when valid.
example (precision coefficient bit : ℕ) (h : precision = 0 ∨ coefficient ≠ 0 ∨ bit ≠ 0) :
    let a := { matching false with header :=
      { (matching false).header with
        precision := precision, coefficient := coefficient, bit := bit } }
    plays (fun xs => check (a, xs) = true) [] (flags a.header) := by
  dsimp only
  rw [plays_check]
  rcases h with h | h | h <;> simp [value, active, h, matching]

-- Padding is rejected, so its false claim is accepted.
example :
    let a : Input := ⟨⟨⟨2, 1, 0, 1, true, true, 3⟩, 8, 0, 0, false⟩, []⟩
    plays (fun xs => check (a, xs) = true) [] (flags a.header) := by
  dsimp only
  rw [plays_check]
  change (true && _) = false
  rw [Bool.true_and, decide_eq_false_iff_not]
  unfold CoeffWordSum.Valid
  decide

-- The validity bit is the input at row-count index in the actual packet circuit.
private def packet : NativePacket.PacketCtx :=
  ⟨8, FastContraction.modulus 0, 1, 2, 0, 3, 0, 1, true, true, true, [], []⟩

example :
    ((FastContraction.representative 0 8
      (NativePacket.PacketWordSum.factor packet [(0, false), (1, true)] [1, 1, 0] 6 2)).coeff
        0).val.testBit 0 = true := by
  exact (value_ofPacket 0 packet rfl [(0, false), (1, true)] [1, 1, 0]
    6 0 0 true).symm.trans (value_matching true)

/-- One finite machine answers all four signed requests for every preserved host word. -/
theorem native_signed_queries :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ host : List Bool,
        let accepts := fun a : Input =>
          atm.AcceptsWithin (C * ((encList encNat a.exponents).length + shortSize a ^ D + 1))
            (SharedWordFork.start src atm host (encInput a) 0)
        accepts (matching true) ∧ ¬ accepts (matching false) ∧
          accepts (wrong false) ∧ ¬ accepts (wrong true) := by
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := exists_evaluator
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host accepts
  have haccept (a : Input) : accepts a ↔ value a = a.header.claim := by
    rw [value_eq_factor_bit 0 a (fun _ _ => 0)]
    exact (h host a 0 (fun _ _ => 0)).2
  simp only [haccept, value_matching, value_wrong]
  decide

end Turing.MultiTapeATM.PacketValidity.Tests
