/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# The input length within logarithmic space

The length `n` of an encoded instance, written in binary, is computed within space
`log₂ n + 1` (`Turing.MultiTapeTM.inputLength_inSpace`): a logspace counter
(`Turing.MultiTapeTM.computableInLogSpace_bitsLength`) whose binary output has `log₂ n + 1` bits.
This is the usual first step of a logarithmic-space machine that writes a polynomial of the input
length, such as a step count, on its work tapes.

## Main results

* `Turing.MultiTapeTM.inputLength_inSpace`: the binary input length within space `log₂ n + 1`.
-/

public section

namespace Turing.MultiTapeTM

/-- **The input length within logarithmic space**: the length `n` of the encoded instance, in
binary, is computed within space `log₂ n + 1`, where the space charges the work tapes and the
output but not the read-only input. -/
theorem inputLength_inSpace {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun a => (enc a).length) enc encNat
      fun a => Nat.log2 (enc a).length + 1 :=
  ((ComputableInLogSpace.comp' computableInLogSpace_bitsLength
      (ComputableInLogSpace.of_eq (f := fun a => enc a) (encIn := enc) (encMid := encBits)
        fun _ => rfl)).inSpace_of_length_log
    ⟨1, fun a => by rw [one_mul]; exact length_encNat_le_log2 le_rfl⟩).mono_le
    fun _ => Nat.le_succ _

end Turing.MultiTapeTM
