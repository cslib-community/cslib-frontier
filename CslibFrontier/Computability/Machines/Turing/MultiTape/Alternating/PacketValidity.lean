/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PacketValidity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native

/-!
# Native signed bits of the packet validity input

One fixed finite alternating machine answers either claimed value of the coefficient circuit's
validity-factor bit. It accepts exactly the requested representative bit of the actual ring
factor. The statement covers every modulus scale, coefficient index, precision and bit index,
including precision zero and out-of-range indices. The unrelated row factors are arbitrary.

The dense exponent list contributes linearly to the clock. Only the short binary header and
the binary length of that list enter the polynomial. Quantifier polarity, flag preparation,
challenge generation, rewinding and the deterministic terminal are included in the bound.
Arithmetic row and source-factor inputs remain separate from this validity input.
-/

public section

namespace Turing.MultiTapeATM.PacketValidity

open MultiTapeTM MultiTapeTM.PacketValidity
open Cslib Cslib.Circuits.Frontier TensorNetwork

/-- One fixed finite ATM checks either claimed bit of the packet's actual validity factor,
with a linear dense-word charge and a polynomial in short metadata. -/
theorem exists_evaluator :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : Input) (m : ℕ)
        (term : Fin a.header.context.rows → Option (Fin a.header.context.modes) →
          GaloisRingArith.Ring a.header.precision (FastContraction.modulus m)),
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * ((encList encNat a.exponents).length + shortSize a ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          ((FastContraction.representative m a.header.precision
            (CoeffWordSum.factor a.header.context.modes a.header.context.rows
              a.header.context.modes.size (PacketChoice.targets a.header.context) term
              (fun k => a.exponents.getD k 0) a.header.context.assignment
              a.header.context.rows)).coeff a.header.coefficient).val.testBit a.header.bit =
            a.header.claim) := by
  obtain ⟨dCheck, hcheck⟩ := exists_check_inO
  obtain ⟨dF, hflags⟩ := exists_flags_inO
  have hflagLength : PolyBounded shortSize (fun a : Input => (flags a.header).length) :=
    flags_polyTime.polyBounded_length.comp (g := Input.header)
      (PolyBounded.self.mono fun a => by simp only [shortSize]; omega)
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := QuantifiedWord.exists_linear_evaluator
    (long := fun a : Input => (encList encNat a.exponents).length)
    (short := shortSize) (challenge := challengeSize)
    hflags hcheck 2 (fun a => by simp [shortSize])
    (fun a => by
      simp only [encInput_apply, encInputFields, length_encPair, shortSize]
      omega) hflagLength
    (fun a xs _ => by simp only [challengeSize]; omega)
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a m term
  refine ⟨(h host a).1, (h host a).2.trans ?_⟩
  rw [plays_check, value_eq_factor_bit m a term]

end Turing.MultiTapeATM.PacketValidity
