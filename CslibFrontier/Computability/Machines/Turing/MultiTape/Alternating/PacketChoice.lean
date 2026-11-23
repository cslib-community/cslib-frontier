/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PacketChoice
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native

/-!
# A finite alternating machine for packet row-choice validity

One fixed finite machine receives short packet metadata and the dense binary exponent list.
It checks all row range and target guards, universally chooses a binary mode, counts that mode's
row occurrences, and reads its prescribed exponent once. Acceptance is exactly the validity
factor in `CoeffWordSum`, with the assignment fixed before the universal challenge.

Preparation, choices, rewinding and the actual deterministic terminal are included. The encoded
exponent list is charged linearly; the polynomial depends on short metadata and the binary
encoded-list length. Missing exponent entries are zero. Empty mode and row sets retain their
required guards and multiplicity checks.
-/

public section

namespace Turing.MultiTapeATM.PacketChoice

open MultiTapeTM MultiTapeTM.PacketChoice

/-- One fixed finite machine verifies the packet coefficient's row-choice validity factor.
Its clock is linear in the dense binary exponent encoding and polynomial only in short data. -/
theorem exists_evaluator :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : Input),
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * ((encList encNat a.exponents).length + shortSize a ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          Cslib.Circuits.Frontier.TensorNetwork.CoeffWordSum.Valid
            a.context.modes a.context.rows a.context.modes.size (targets a.context)
            (fun k => a.exponents.getD k 0) a.context.assignment) := by
  obtain ⟨dCheck, hcheck⟩ := exists_check_inO
  obtain ⟨dF, hflags⟩ := exists_flags_inO
  have hflagLength : PolyBounded shortSize (fun a : Input => (flags a.context).length) :=
    flags_polyTime.polyBounded_length.comp (g := Input.context)
      (PolyBounded.self.mono fun a => by simp only [shortSize]; omega)
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := QuantifiedWord.exists_linear_evaluator
    (long := fun a : Input => (encList encNat a.exponents).length)
    (short := shortSize) (challenge := challengeSize)
    hflags hcheck 2 (fun a => by simp [shortSize])
    (fun a => by
      simp only [encInput_apply, encInputFields, length_encPair, shortSize]
      omega) hflagLength
    (fun a xs _ => by
      simp only [challengeSize, encData, length_encPair, encBits_apply, shortSize]
      omega)
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a
  exact ⟨(h host a).1, (h host a).2.trans (plays_check a)⟩

end Turing.MultiTapeATM.PacketChoice
