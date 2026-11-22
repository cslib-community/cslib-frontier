/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingLeafRequest

/-!
The physical words may have arbitrary high zero padding. Only the short context controls
index clipping, while the complete assignment path is retained verbatim. Carry components,
zero precision and out-of-range clipped indices use the constant-zero dispatch header.
-/

namespace CslibFrontierTests.StoppingLeafRequest

open Turing.MultiTapeTM Turing.MultiTapeATM.StoppingLeafRequest
open Cslib.Circuits.Frontier.FastContraction.StoppingQuery Product ProductRouting

private def context : Context := ⟨⟨0, 3, 4⟩, 1⟩

private def query (padding : ℕ) (carry : Bool) : Input :=
  ⟨context, true :: List.replicate padding false, List.replicate padding false,
    [true, false, true, true], carry, true :: List.replicate padding false⟩

-- The typed context changes no serialized cell, including the unused physical width word.
example (padding : ℕ) (carry : Bool) : encInput (query padding carry) =
    Cslib.CountingLeaf.encRawInput
      ⟨encContext context, true :: List.replicate padding false, List.replicate padding false,
        [true, false, true, true], carry, true :: List.replicate padding false⟩ :=
  encInput_eq _

example (padding : ℕ) : cappedBit (query padding false) = 1 := by
  have h : Cslib.BitString.lsbValue (query padding false).bit = 1 := by
    simp [query, Cslib.BitString.lsbValue]
  exact (cappedBit_eq _ (by rw [h]; change 1 < 3; decide)).trans h

-- The original assignment is retained; its length does not enter any polynomial power.
example (padding : ℕ) : (prepare true (query padding false)).assignment =
    [true, false, true, true] := rfl

example : (prepare true (query 80 false)).position.data.bit = 1 := rfl

example : (instruction true (query 80 true)).take 3 = [false, false, false] := rfl

example : (instruction false { query 80 false with bit := [true, true] }).take 3 =
    [false, false, true] := rfl

example : (instruction false
    { query 80 false with context := ⟨⟨0, 0, 4⟩, 1⟩ }).take 3 =
    [false, false, true] := rfl

example (claim : Bool) : ∃ d, ComputableInO (instruction claim) encInput encBits
    (fun x => (encInput x).length + ((encContext x.context).length + 1) ^ d)
    (fun x => (encInput x).length + ((encContext x.context).length + 1) ^ d) :=
  exists_instruction_inO claim

end CslibFrontierTests.StoppingLeafRequest
