/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime

/-!
# Plain polynomial-time closure and deciders

Decidability can be stated using any Boolean decider. Captured projections and conditionals
compose the direct plain providers, retaining their encodings and independent resource bounds.
A polynomial time bound on a machine also supplies a polynomial space bound via its real run.
-/

public section

namespace Turing.MultiTapeTM

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- The indicator of `A` is the Boolean function that is `true` exactly on `A`. -/
theorem indicator_eq_iff {A : Set α} {g : α → Bool} :
    indicator A = g ↔ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h a => ?_, fun h => funext fun a => ?_⟩
  · subst h
    by_cases ha : a ∈ A <;> simp [indicator, ha]
  · rcases hg : g a <;> simp [indicator, h a, hg]

-- upstream: candidate (after crei/tidy-universal lands)

/-! ### Decidability through a Boolean decider -/

/-- A problem is decidable within given bounds exactly when some Boolean function deciding
membership is computable within them, with answers encoded by `encBool`. -/
theorem decidableInTimeAndSpace_iff {A : Set α} {enc : α ↪ List Bool} {t s : α → ℕ} :
    DecidableInTimeAndSpace A enc t s ↔
      ∃ g : α → Bool, ComputableInTimeAndSpace g enc encBool t s ∧ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h => ⟨indicator A, h, indicator_eq_iff.mp rfl⟩, fun ⟨g, hg, hA⟩ => ?_⟩
  rw [DecidableInTimeAndSpace, indicator_eq_iff.mpr hA]
  exact hg

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

-- Register captured projections for ordinary plain automation.
attribute [fun_prop] fst' snd'

/-- Project a first component and convert its encoding. Certifying the pair-valued function first
determines the source encoding before automation searches for the conversion certificate. -/
@[fun_prop]
theorem fstWithEncoding {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encA output) :
    ComputableInPolyTime (fun p => (f p).1) encC output :=
  h.comp hf.fst'

/-- Project a second component and convert its encoding. The pair certificate fixes the source
encoding; the conversion certificate supplies the efficient change of representation. -/
@[fun_prop]
theorem sndWithEncoding {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encB output) :
    ComputableInPolyTime (fun p => (f p).2) encC output :=
  h.comp hf.snd'

/-- A case distinction between functions computable in polynomial time on all inputs. -/
@[fun_prop]
theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  ComputableInPolyTime.ite hc hf hg


/-- Return the encoded word of an already computed value. The source and result encodings of
that value remain fixed; this reads the representation already produced by its certificate. -/
@[fun_prop]
theorem encoding_comp {δ : Type*} {ε : Type*} {input : δ ↪ List Bool}
    {output : ε ↪ List Bool} {f : δ → ε} (hf : ComputableInPolyTime f input output) :
    ComputableInPolyTime (fun a => output (f a)) input encBits :=
  (ComputableInPolyTime.of_eq (fun _ => rfl) :
    ComputableInPolyTime output output encBits).comp hf

end Turing.MultiTapeTM.ComputableInPolyTime
