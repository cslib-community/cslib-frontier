/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.WordPredicates

/-!
# Direct degree certificates for option encoding machines

Construction and fixed-default elimination reuse the encoding capability's degree certificates.
The Boolean test retains its constant output degree. No higher tidy calculus is used.
-/

public section
namespace Turing.MultiTapeTM.ComputableInDegree
open Internal.WordPredicates

variable {β : Type*} {enc₁ : β ↪ List Bool}

/-- Construct an optional value in an encoding with the option capability. -/
theorem optionSome {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] :
    ComputableInDegree some enc₁ enc 1 1 := OptionEncoding.some

/-- Eliminate an optional value using a fixed default. -/
theorem getD {enc : Option β ↪ List Bool} [OptionEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1 := OptionEncoding.getD d

/-- Whether a standard encoded option holds a value; the Boolean output has degree zero. -/
theorem isSome (enc : β ↪ List Bool) {encO : Option β ↪ List Bool}
    [OptionEncoding enc encO] :
    ComputableInDegree (fun o : Option β => o.isSome) encO encBool 1 0 :=
  OptionEncoding.isSome enc

/-- Translate between option representations using their native capabilities. This is a real
classification and reconstruction machine, rather than a word-equality cast. -/
theorem optionTranslate (enc : β ↪ List Bool) {source target : Option β ↪ List Bool}
    [OptionEncoding enc source] [OptionEncoding enc target] :
    ComputableInDegree (id : Option β → Option β) source target 1 1 := by
  rcases isEmpty_or_nonempty β with h | h
  · convert (const (encIn := source) (encMid := target) none).mono (d' := 1) (e' := 1) using 1
    funext o
    cases o with
    | none => rfl
    | some a => exact isEmptyElim a
  · obtain ⟨d⟩ := h
    have hs : ComputableInDegree (fun o : Option β => some (o.getD d)) source target 1 1 :=
      (optionSome (enc₁ := enc)).comp (getD (enc₁ := enc) d) |>.mono
    convert ite (isSome enc) (hs.restrict _) ((const none).restrict _) using 1
    · funext o
      cases o <;> rfl
    all_goals decide

/-- Convert the silent/halt representation to tagged options in linear resources. -/
theorem optionFromHalt (enc : β ↪ List Bool) :
    ComputableInDegree (id : Option β → Option β) (encHaltOption enc) (encOption enc) 1 1 :=
  .of_isEmpty_ite none (fun o ho => by cases o <;> simp_all)
    (.of_eq fun ⟨o, ho⟩ => by
      cases o with
      | none => simp only [encHaltOption_none, List.isEmpty_nil, Bool.true_eq_false] at ho
      | some a => rfl)

/-- The option encoding determines the encoding used for the payload and fallback. -/
@[fun_prop]
theorem optionGetD {α : Type*} (enc : α ↪ List Bool) (fallback : α)
    {encO : Option α ↪ List Bool} [OptionEncoding enc encO] :
    ComputableInDegree (fun o => o.getD fallback) encO enc 1 1 :=
  getD (enc₁ := enc) fallback

end Turing.MultiTapeTM.ComputableInDegree
