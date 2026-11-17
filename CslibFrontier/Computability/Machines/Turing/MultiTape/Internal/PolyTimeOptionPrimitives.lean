/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# Direct plain polynomial-time option operations

The option encoding machines supply construction and fixed-default elimination. Composition
retains every encoded input, including captured arguments and a runtime fallback. Empty value
types need no inhabitant assumption.

The `Tagged` search rules fix only the intermediate option format, leaving the payload encoding
to the value certificate. Generic rules alone leave this intermediate encoding unconstrained in
`fun_prop` (notably for list search followed by elimination). They remain available for explicitly
supplied formats, including halt and silent protocols; no typeclass selects a default encoding.

## Main results

* `ComputableInPolyTime.optionSome`: construct an optional value.
* `ComputableInPolyTime.optionIsSome`: test a computed optional value.
* `ComputableInPolyTime.optionGetD`: read an option with a runtime fallback.
* `ComputableInPolyTime.optionGetDWithInput`, `.optionElimWithInput`: retain captured inputs.
* `ComputableInPolyTime.optionMapWithInput`: map a computed option with a captured callback.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Construct an optional value with the standard option encoding. -/
@[fun_prop]
theorem optionSome (enc : α ↪ List Bool) {encO : Option α ↪ List Bool}
    [OptionEncoding enc encO] :
    ComputableInPolyTime (some (α := α)) enc encO :=
  ComputableInDegree.optionSome.computableInPolyTime

/-- Test whether a computed option contains a value, without requiring a default value. -/
@[fun_prop]
theorem optionIsSome {encO : Option β ↪ List Bool} [OptionEncoding encB encO]
    {value : α → Option β}
    (hvalue : ComputableInPolyTime value encA encO) :
    ComputableInPolyTime (fun a => (value a).isSome) encA encBool :=
  (ComputableInDegree.isSome encB).computableInPolyTime.comp hvalue

/-- Branch on a computed option, charging its full value and any captured original input. -/
@[fun_prop]
theorem optionElimWithInput {γ : Type} {encC : γ ↪ List Bool}
    {encO : Option β ↪ List Bool} [OptionEncoding encB encO]
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableInPolyTime value encA encO)
    (hfallback : ComputableInPolyTime fallback encA encC)
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC := by
  rcases isEmpty_or_nonempty β with h | h
  · convert hfallback using 1
    funext a
    cases value a with
    | none => rfl
    | some b => exact isEmptyElim b
  · obtain ⟨b⟩ := h
    have hget : ComputableInPolyTime (fun a => (value a).getD b) encA encB :=
      (ComputableInDegree.getD b).computableInPolyTime.comp hvalue
    obtain ⟨Tv, Sv, hTv, hSv, hv⟩ := hvalue.exists_computableInO
    obtain ⟨Tn, Sn, hTn, hSn, hn⟩ := hfallback.exists_computableInO
    obtain ⟨Tb, Sb, hTb, hSb, hb⟩ := hbody.exists_computableInO
    have hp := (id'.prod hget).polyBounded_length
    have hTbranch : PolyBounded (fun a => (encA a).length)
        (fun a => (value a).elim (Tn a) (fun b => Tb (a, b))) :=
      (hTn.add (hTb.comp hp)).mono fun a => by
        cases value a <;> simp
    have hSbranch : PolyBounded (fun a => (encA a).length)
        (fun a => (value a).elim (Sn a) (fun b => Sb (a, b))) :=
      (hSn.add (hSb.comp hp)).mono fun a => by
        cases value a <;> simp
    exact (ComputableInO.optionElimWithInput hv hn hb).computableInPolyTime
      ((((PolyBounded.const 2).mul hTv).add .self).add hTbranch)
      ((((PolyBounded.const 2).mul hSv).add .self).add hSbranch)

/-- Read an option with a fallback supplied as part of the input. -/
@[fun_prop]
theorem optionGetD (enc : α ↪ List Bool) {encO : Option α ↪ List Bool}
    [OptionEncoding enc encO] :
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair encO enc) enc := by
  have h := optionElimWithInput (body := fun (_ : Option α × α) (a : α) => a)
    (fst encO enc) (snd encO enc)
    (snd (encPair encO enc) enc)
  convert h using 1
  funext p
  cases p.1 <;> rfl

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
@[fun_prop]
theorem optionGetDWithInput {encO : Option β ↪ List Bool} [OptionEncoding encB encO]
    {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value encA encO)
    (hfallback : ComputableInPolyTime fallback encA encB) :
    ComputableInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  (optionGetD encB).comp (hvalue.prod hfallback)

/-- Map a computed option, charging the callback jointly with its captured input. -/
@[fun_prop]
theorem optionMapWithInput {γ : Type} {encC : γ ↪ List Bool}
    {encOC : Option γ ↪ List Bool} [OptionEncoding encC encOC]
    {encO : Option β ↪ List Bool} [OptionEncoding encB encO]
    {value : α → Option β} {f : α → β → γ}
    (hvalue : ComputableInPolyTime value encA encO)
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair encA encB) encC) :
    ComputableInPolyTime (fun a => (value a).map (f a)) encA encOC := by
  have h := hvalue.optionElimWithInput (body := fun a b => some (f a b))
    (ComputableInPolyTime.const none) ((optionSome encC (encO := encOC)).comp hf)
  convert h using 1
  funext a
  cases value a <;> rfl

/-- Tagged-option inference rule: the payload encoding is supplied by the value certificate. -/
@[fun_prop]
theorem optionIsSomeTagged {value : α → Option β}
    (hvalue : ComputableInPolyTime value encA (encOption encB)) :
    ComputableInPolyTime (fun a => (value a).isSome) encA encBool :=
  optionIsSome (encB := encB) (encO := encOption encB) hvalue

/-- Tagged-option inference rule: the payload encoding is supplied by the value certificate. -/
@[fun_prop]
theorem optionElimWithInputTagged {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encC)
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC :=
  optionElimWithInput (encB := encB) (encO := encOption encB) hvalue hfallback hbody

/-- Tagged-option inference rule: the payload encoding is supplied by the value certificate. -/
@[fun_prop]
theorem optionGetDWithInputTagged {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encB) :
    ComputableInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  optionGetDWithInput (encB := encB) (encO := encOption encB) hvalue hfallback

/-- Tagged-option inference rule: the payload encoding is supplied by the value certificate. -/
@[fun_prop]
theorem optionMapWithInputTagged {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {f : α → β → γ}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair encA encB) encC) :
    ComputableInPolyTime (fun a => (value a).map (f a)) encA (encOption encC) :=
  optionMapWithInput (encB := encB) (encO := encOption encB) (encOC := encOption encC) hvalue hf

end Turing.MultiTapeTM.ComputableInPolyTime
