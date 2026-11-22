/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredCount
import CslibFrontierTests.SpaceQueryLoop

/-!
# Majority of the bits of a word by enumeration

The predicate at index `i` is the bit of the word at the stored position `i`, read by
`Turing.MultiTapeTM.ComputableInSpace.inputBit`; the range is the length of the word, computed by
the scan of `CslibFrontierTests.SpaceQueryLoop`. `Turing.MultiTapeTM.ComputableInSpace.majorityWith`
enumerates the positions with a stored counter. No loop state or invariant is written.
-/

open Turing Turing.MultiTapeTM

namespace SpaceStoredCountTest

/-- The bit at a position, `false` past the end. -/
def bit (p : ℕ × List Bool) : Bool := (p.2[p.1]?).getD false

/-- Majority of the bits, as an enumeration of the positions. -/
def majority (w : List Bool) : Bool :=
  decide (w.length < 2 * (List.range w.length).countP fun i => bit (i, w))

example : majority [true, false, true] = true := by decide
example : majority [true, false, false, true] = false := by decide

theorem bit_inSpace : ComputableInSpace bit (encPair encNat encBits) encBool
    fun p => (encNat p.1).length + Nat.log2 (encBits p.2).length :=
  (ComputableInSpace.budget_optionGetD false (ComputableInSpace.inputBit encBits)).of_enc_eq
    fun _ => rfl

theorem length_inSpace : ComputableInSpace (fun w : List Bool => w.length) encBits encNat
    fun w => Nat.log2 (encBits w).length :=
  (SpaceQueryLoopTest.encScan_pos_budget SpaceQueryLoopTest.scan_inSpace).mono_le fun w => by
    simp only [encBits_apply]; omega

/-- **Majority of the bits of a word** within logarithmic space, by counting over positions. -/
theorem majority_inSpace : ComputableInSpace majority encBits encBool
    fun w => Nat.log2 w.length :=
  (length_inSpace.majorityWith bit_inSpace).weaken
    ⟨2, fun w => by simp only [encBits_apply]; omega⟩

example : ComputableInLogSpace majority encBits encBool :=
  majority_inSpace.computableInLogSpace

end SpaceStoredCountTest
