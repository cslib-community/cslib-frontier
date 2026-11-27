/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Reading the input at a stored position

The basic accessor for bodies of `Turing.MultiTapeTM.ComputableInSpace.loopWith`: the bit of the
input at a position held in the registers. It is the logspace lookup
`Turing.MultiTapeTM.computableInLogSpace_bitsGetElem?` after the logspace map that swaps the index
and the input, in context form by `Turing.MultiTapeTM.ComputableInLogSpace.inSpace_context`, since
its value has constant length.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.inputBit`: the bit of the input at a stored binary
  position, in context form.
-/

public section

namespace Turing.MultiTapeTM

/-- `⌊log₂⌋` of the length of a word, within logarithmic space. -/
theorem ComputableInSpace.log2BitsLength :
    ComputableInSpace (fun w : List Bool => Nat.log2 w.length) encBits encNat
      fun w => Nat.log2 (encBits w).length :=
  (ComputableInLogSpace.unaryToBinary
      (ComputableInLogSpace.unaryLog2 ComputableInLogSpace.bitsLength)).inSpace_of_length_log
    ⟨1, fun w => by
      simpa only [one_mul, encBits_apply] using
        length_encNat_le_log2 (Nat.log2_le_self w.length)⟩

private theorem length_encOption_bool_le (o : Option Bool) : (encOption encBool o).length ≤ 2 := by
  cases o <;> simp

/-- **Reading the input at a stored position.** The bit of the encoded input `a` at the position
`i`, `none` past its end, as a function of the stored binary index and the input, within the
binary length of the index plus the logarithm of the length of the input. The index is the first
component, so this is a part of a body of `Turing.MultiTapeTM.ComputableInSpace.loopWith` that
reads the input where its registers point. -/
theorem ComputableInSpace.inputBit {α : Type} (encA : α ↪ List Bool) :
    ComputableInSpace (fun p : ℕ × α => (encA p.2)[p.1]?) (encPair encNat encA)
      (encOption encBool) fun p => (encNat p.1).length + Nat.log2 (encA p.2).length :=
  (computableInLogSpace_bitsGetElem?.comp' (ComputableInLogSpace.pair
    ((ComputableInLogSpace.of_eq (encMid := encBits) fun _ => rfl).comp'
      (ComputableInLogSpace.snd encNat encA))
    (ComputableInLogSpace.fst encNat encA))).inSpace_context
    ⟨2, fun _ => (length_encOption_bool_le _).trans (by omega)⟩

end Turing.MultiTapeTM
