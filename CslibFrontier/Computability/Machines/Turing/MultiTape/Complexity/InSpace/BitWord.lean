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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization

/-!
# Bit words within a fixed workspace budget

Budget-preserving `fun_prop` rules for words of bits held in registers: the test for the word
of ones, the binary counter `Cslib.BitString.increment`, the words of zeros and of ones
of a width given in unary, the value of a word, concatenation and a unary number in
binary. Each costs space linear in its arguments,
which the caller's certificates already pay for, so a body of
`Turing.MultiTapeTM.ComputableInSpace.loopWith` or
`Turing.MultiTapeTM.ComputableInSpace.recWith` that steps a counter or compares stored words is
composed by `space` without a hand-written certificate. Stored words are compared by
`Turing.MultiTapeTM.ComputableInSpace.budget_decideEq`.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.budget_bitsAll`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_bitsIncrement`: the overflow test and the
  successor of a binary counter.
* `Turing.MultiTapeTM.ComputableInSpace.budget_replicateFalse`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_replicateTrue`: the words of zeros and of ones.
* `Turing.MultiTapeTM.ComputableInSpace.budget_ofBits`: the value of a word.
* `Turing.MultiTapeTM.ComputableInSpace.budget_bitsAppend`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_unaryToNat`: concatenation, and a unary number in
  binary.
-/

namespace Turing.MultiTapeTM

/-- The transducer testing whether all bits are ones. -/
private def allT : Transducer Bool Bool where
  q₀ := true
  step a b := (a && b, [])
  final a := [a]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem allT_run (a : Bool) (u : List Bool) : allT.run a u = [a && u.all id] := by
  induction u generalizing a with
  | nil => simp [allT]
  | cons b u ih =>
    rw [Transducer.run_cons]
    change [] ++ allT.run (a && b) u = _
    rw [ih, List.nil_append, List.all_cons, id, Bool.and_assoc]

/-- The transducer writing a zero for every symbol. -/
private def zeroT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem zeroT_run (u : List Bool) : zeroT.run () u = List.replicate u.length false := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [Transducer.run_cons]
    change [false] ++ zeroT.run () u = _
    rw [ih, List.length_cons, List.replicate_succ, List.singleton_append]

public section

namespace ComputableInSpace

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

/-- Whether a word consists of ones, within the budget: the overflow test of a binary counter. -/
@[fun_prop]
theorem budget_bitsAll {l : α → List Bool} (hl : ComputableInSpace l encIn encBits Bs) :
    ComputableInSpace (fun x => (l x).all id) encIn encBool Bs :=
  budget_comp_linear (of_inO (ComputableInDegree.of_transducer (encIn := encBits)
    (encMid := encBool) (f := fun u : List Bool => u.all id) allT fun u => by
      rw [show allT.q₀ = true from rfl, allT_run]; rfl).inO_one) hl

/-- The successor of a binary counter, least significant bit first, within the budget. -/
@[fun_prop]
theorem budget_bitsIncrement {l : α → List Bool} (hl : ComputableInSpace l encIn encBits Bs) :
    ComputableInSpace (fun x => Cslib.BitString.increment (l x)) encIn encBits Bs :=
  budget_comp_linear (of_inO ComputableInDegree.increment.inO_one) hl

/-- The word of zeros of a width given in unary, within the budget. -/
@[fun_prop]
theorem budget_replicateFalse {n : α → ℕ} (hn : ComputableInSpace n encIn encUnary Bs) :
    ComputableInSpace (fun x => List.replicate (n x) false) encIn encBits Bs :=
  budget_comp_linear (of_inO (ComputableInDegree.of_transducer (encIn := encUnary)
    (encMid := encBits) (f := fun n : ℕ => List.replicate n false) zeroT fun n => by
      rw [show zeroT.q₀ = () from rfl, zeroT_run, encUnary_apply, List.length_replicate]
      rfl).inO_one) hn

/-- The word of ones of a width given in unary, within the budget: it is the unary numeral. -/
@[fun_prop]
theorem budget_replicateTrue {n : α → ℕ} (hn : ComputableInSpace n encIn encUnary Bs) :
    ComputableInSpace (fun x => List.replicate (n x) true) encIn encBits Bs :=
  hn.of_enc_eq fun _ => rfl

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
