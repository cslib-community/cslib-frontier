/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PortAssignment
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native

/-!
# A finite alternating machine for local assignment consistency

One fixed finite machine receives the proposed ports, local bits, and raw global assignment on
one work tape. It prepares its universal index choices, checks the length guard, and reads just
one addressed global bit on each branch. Acceptance means that the proposed local word is
exactly the global assignment restricted to the proposed ordered ports.

The native clock includes preparation, universal choices, rewinding, and the deterministic
terminal. Its dependence on the raw global assignment is linear. All polynomial work is confined
to the short context and the binary global length.
-/

public section

namespace Turing.MultiTapeATM.PortAssignment

open MultiTapeTM MultiTapeTM.PortAssignment

/-- A single finite machine verifies every proposed local assignment, with the candidate fixed
before its universal index is chosen. It includes all native preparation and terminal work and
charges the raw global word only linearly, even for repeated or out-of-range ports. -/
theorem exists_evaluator :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : Input),
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * (a.word.length + shortSize a ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          a.context.bits = Cslib.Circuits.Frontier.DescribedNetwork.wordBits
            a.word a.context.ports) := by
  obtain ⟨dCheck, hcheck⟩ := exists_check_inO
  obtain ⟨dF, hflags⟩ := exists_flags_inO
  have hflagLength : PolyBounded shortSize (fun a : Input => (flags a.context).length) :=
    flags_polyTime.polyBounded_length.comp (g := Input.context)
      (PolyBounded.self.mono fun a => by simp only [shortSize]; omega)
  obtain ⟨U, src, Q, hQ, atm, C, D, h⟩ := QuantifiedWord.exists_linear_evaluator
    (long := fun a : Input => a.word.length) (short := shortSize) (challenge := challengeSize)
    hflags hcheck 2 (fun a => by simp [shortSize])
    (fun a => by
      simp only [encInput_apply, encInputFields, length_encPair, encBits_apply, shortSize]
      omega) hflagLength
    (fun a xs _ => by
      simp only [challengeSize, encData, length_encPair, encBits_apply, shortSize]
      omega)
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a
  exact ⟨(h host a).1, (h host a).2.trans (plays_check a)⟩

end Turing.MultiTapeATM.PortAssignment
