/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Basic.Finite.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelFacts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes

/-! # The existing concatenation machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

public section

namespace Turing.MultiTapeMachine

variable {k₁ k₂ : ℕ} {Symbol State₁ State₂ : Type}

/-- Choice-free sequential concatenation of two explicit tables on a common input. -/
def append (first : MultiTapeMachine k₁ Symbol State₁ Empty Id)
    (second : MultiTapeMachine k₂ Symbol State₂ Empty Id) :
    MultiTapeMachine (max k₁ k₂) Symbol (State₁ ⊕ State₂) Empty Id :=
  (first.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (second.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- Exact tidy semantics and resources of explicit output concatenation. -/
theorem computesTidilyInTimeAndSpace_append
    {first : MultiTapeMachine k₁ Symbol State₁ Empty Id}
    {second : MultiTapeMachine k₂ Symbol State₂ Empty Id}
    {input output₁ output₂ : List Symbol} {time₁ space₁ time₂ space₂ : ℕ}
    (h₁ : first.toTM.ComputesTidilyInTimeAndSpace input output₁ time₁ space₁)
    (h₂ : second.toTM.ComputesTidilyInTimeAndSpace input output₂ time₂ space₂) :
    (first.append second).toTM.ComputesTidilyInTimeAndSpace input (output₁ ++ output₂)
      (time₁ + time₂) (space₁ + space₂ + 2 * max k₁ k₂) := by
  rw [append, toTM_seq, toTM_extendTapes, toTM_extendTapes]
  exact (MultiTapeTM.transformsTapes_seq (h₁.extendTapes _) (h₂.extendTapes _)
    fun _ _ _ _ hfirst hsecond => ⟨hfirst.1, hsecond.1⟩).imp (fun _ _ h => h)
    (by
      rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨htapes, rfl⟩, rfl⟩
      exact ⟨htapes, rfl⟩)
    le_rfl (by omega)

end Turing.MultiTapeMachine

end

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- Run `tm₁` and then `tm₂`, both with their work tapes padded to `max k₁ k₂`. -/
public noncomputable def appendTM (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (tm₂ : MultiTapeTM k₂ Symbol S₂) : MultiTapeTM (max k₁ k₂) Symbol (S₁ ⊕ S₂) :=
  (tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).seq
    (tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))

/-- If `tm₁` computes `y₁` from `x` tidily and `tm₂` computes `y₂` from `x` tidily, then
`appendTM tm₁ tm₂` computes `y₁ ++ y₂` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.append {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x y₁ y₂ : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x y₁ t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace x y₂ t₂ s₂) :
    (appendTM tm₁ tm₂).ComputesTidilyInTimeAndSpace x (y₁ ++ y₂) (t₁ + t₂)
      (s₁ + s₂ + 2 * max k₁ k₂) :=
  (transformsTapes_seq (h₁.extendTapes _) (h₂.extendTapes _)
    fun _ _ _ _ hP hQ => ⟨hP.1, hQ.1⟩).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩; exact ⟨hws, rfl⟩) le_rfl
    (by omega)

end Turing.MultiTapeTM
