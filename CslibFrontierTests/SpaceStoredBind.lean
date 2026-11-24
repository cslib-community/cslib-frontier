/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredBind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontierTests.SpaceQueryLoop

/-!
# Majority by storing a count

Whether more than half of the bits of a word are ones: the number of ones is computed once by the
counting routine of `CslibFrontierTests.SpaceQueryLoop` and stored, and the comparison with the
length of the word is a function of the stored count and the word, in context form.
`Turing.MultiTapeTM.ComputableInSpace.bindWith` adds the two budgets.
-/

open Turing Turing.MultiTapeTM

namespace SpaceStoredBindTest

/-- The comparison of a stored count with the length of the word. -/
def compare (p : ℕ × List Bool) : Bool := decide (p.2.length < 2 * p.1)

/-- The budget of the comparison: the stored count and the logarithm of the length of the
word. -/
abbrev budget (p : ℕ × List Bool) : ℕ := (encNat p.1).length + Nat.log2 (encBits p.2).length

theorem compare_inSpace : ComputableInSpace compare (encPair encNat encBits) encBool budget := by
  have hc : ComputableInSpace (fun p : ℕ × List Bool => p.1) (encPair encNat encBits) encNat
      budget :=
    (ComputableInLogSpace.fst encNat encBits).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)
  have hlen : ComputableInSpace (fun p : ℕ × List Bool => p.2.length) (encPair encNat encBits)
      encNat budget :=
    (computableInLogSpace_bitsLength.comp'
      (ComputableInLogSpace.snd encNat encBits)).inSpace_context
      ⟨1, fun p => by
        have := length_encNat_le_log2 (le_refl p.2.length)
        simp only [encBits_apply] at this ⊢
        omega⟩
  have htwo : ComputableInSpace (fun _ : ℕ × List Bool => 2) (encPair encNat encBits) encNat
      budget := ComputableInSpace.budget_const 2
  exact (ComputableInSpace.budget_natLt hlen (ComputableInSpace.budget_natMul htwo hc)).of_enc_eq
    fun _ => rfl

example : compare (2, [true, false, true]) = true := rfl
example : compare (1, [true, false, false]) = false := rfl

/-- **Majority** within logarithmic space, by storing the number of ones. -/
theorem majority_inSpace :
    ComputableInSpace (fun w : List Bool => decide (w.length < 2 * w.count true)) encBits encBool
      fun w => Nat.log2 w.length :=
  (ComputableInSpace.bindWith (Sg := fun w => Nat.log2 (encBits w).length)
    SpaceQueryLoopTest.count_inSpace compare_inSpace).weaken
    ⟨3, fun w => by simp only [encBits_apply]; omega⟩

example : ComputableInLogSpace (fun w : List Bool => decide (w.length < 2 * w.count true)) encBits
    encBool :=
  majority_inSpace.computableInLogSpace

end SpaceStoredBindTest
