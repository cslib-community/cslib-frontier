/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.WordMachines

/-!
# Bit words within a fixed workspace budget

Budget-preserving `fun_prop` rules for words of bits held in registers: a test of every bit, the
binary counter `Cslib.BitString.increment`, the word that repeats a bit to a width given in unary,
the value of a word, concatenation and a unary number in binary. Each costs space linear in its
arguments, which the caller's certificates already pay for, so a body of
`Turing.MultiTapeTM.ComputableInSpace.loopWith` or
`Turing.MultiTapeTM.ComputableInSpace.recWith` that steps a counter or compares stored words is
composed by `space` without a hand-written certificate. Stored words are compared by
`Turing.MultiTapeTM.ComputableInSpace.budget_decideEq`.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.budget_bitsAll`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_bitsIncrement`: a test of every bit, such as the
  overflow test, and the successor of a binary counter.
* `Turing.MultiTapeTM.ComputableInSpace.budget_bitsReplicate`: the word that repeats a bit, such
  as the words of zeros and of ones.
* `Turing.MultiTapeTM.ComputableInSpace.budget_ofBits`: the value of a word.
* `Turing.MultiTapeTM.ComputableInSpace.budget_bitsAppend`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_unaryToNat`: concatenation, and a unary number in
  binary.
-/

namespace Turing.MultiTapeTM

public section

namespace ComputableInSpace

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

/-- Whether every bit of a word satisfies `p`, within the budget. With `p := id` this is the
overflow test of a binary counter. -/
@[fun_prop]
theorem budget_bitsAll (p : Bool → Bool) {l : α → List Bool}
    (hl : ComputableInSpace l encIn encBits Bs) :
    ComputableInSpace (fun x => (l x).all p) encIn encBool Bs :=
  budget_comp_linear (((ComputableInLogSpace.bitsAll p).inSpace_of_length_log
    ⟨1, fun _ => by simp⟩).mono_le fun _ => Nat.log2_le_self _) hl

/-- The successor of a binary counter, least significant bit first, within the budget. -/
@[fun_prop]
theorem budget_bitsIncrement {l : α → List Bool} (hl : ComputableInSpace l encIn encBits Bs) :
    ComputableInSpace (fun x => Cslib.BitString.increment (l x)) encIn encBits Bs :=
  budget_comp_linear (of_inO ComputableInDegree.increment.inO_one) hl

/-- The word that repeats a fixed bit, of a width given in unary, within the budget. -/
@[fun_prop]
theorem budget_bitsReplicate (b : Bool) {n : α → ℕ}
    (hn : ComputableInSpace n encIn encUnary Bs) :
    ComputableInSpace (fun x => List.replicate (n x) b) encIn encBits Bs :=
  budget_comp_linear (of_inO (ComputableInDegree.of_transducer (encIn := encUnary)
    (encMid := encBits) (f := fun n : ℕ => List.replicate n b)
    (Internal.WordMachines.mapT fun _ => b) fun n => by
      rw [show (Internal.WordMachines.mapT fun _ => b).q₀ = () from rfl,
        Internal.WordMachines.mapT_run, encUnary_apply, List.map_replicate]
      rfl).inO_one) hn

/-- The value of a word, least significant bit first, within the budget. -/
@[fun_prop]
theorem budget_ofBits {l : α → List Bool} (hl : ComputableInSpace l encIn encBits Bs) :
    ComputableInSpace (fun x => ofBits (l x)) encIn encNat Bs :=
  budget_comp_linear (of_inO ComputableInO.bitsToNat) hl

/-- The concatenation of two words, within the budget. -/
@[fun_prop]
theorem budget_bitsAppend {l₁ l₂ : α → List Bool} (h₁ : ComputableInSpace l₁ encIn encBits Bs)
    (h₂ : ComputableInSpace l₂ encIn encBits Bs) :
    ComputableInSpace (fun x => l₁ x ++ l₂ x) encIn encBits Bs :=
  (h₁.append h₂ fun _ => rfl).weaken (.add (.refl _) (.refl _))

/-- A number given in unary, in binary, within the budget. -/
@[fun_prop]
theorem budget_unaryToNat {n : α → ℕ} (hn : ComputableInSpace n encIn encUnary Bs) :
    ComputableInSpace n encIn encNat Bs :=
  budget_comp_linear (g := fun m : ℕ => m)
    ((of_inO ComputableInO.unaryToNat).mono_le fun m => by
      rw [encUnary_apply, List.length_replicate]) hn

end ComputableInSpace

end

end Turing.MultiTapeTM
