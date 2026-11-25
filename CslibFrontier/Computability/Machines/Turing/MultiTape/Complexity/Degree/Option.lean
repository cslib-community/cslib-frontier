/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import CslibFrontier.Foundations.Data.Option

/-!
# Options and list heads for `fun_prop`

`fun_prop` assembles `ComputableInDegree` certificates from rules for each operation. This module
adds rules for options and list heads so that a definition using them needs no restatement in terms
of tests and defaults:

* `Option.elim`, at arbitrary resource and output degrees (`optionElim_le`) and at degree one
  (`optionElim_one`), without an inhabitant of the element type, which is also the form
  `option_match_to_elim` gives a `match`, `bind` or `toList` on an option;
* `Option.toList`, without an inhabitant of the element type (`optionToList`);
* `List.head?` at degree one (`head?_one`);
* `Option.some`, `Option.getD`, `List.headD`, `List.tail` and `List.isEmpty`, registered as
  `fun_prop` rules.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.optionElim_le`, `.optionElim_one`: eliminating an option.
* `Turing.MultiTapeTM.ComputableInDegree.optionToList`: converting an option to a framed list.
* `Turing.MultiTapeTM.ComputableInDegree.head?_one`: the head of a framed list.
-/

public section

namespace Turing.MultiTapeTM.ComputableInDegree

attribute [fun_prop] optionSome getD headD tail isEmpty

/-- **Eliminating an option** with independent resource and output degrees: the handler of `some`
receives the input and the value. -/
@[fun_prop]
theorem optionElim_le {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    {dv ev dn en db eb d e : ℕ}
    (hv : ComputableInDegree value encA (encOption encB) dv ev)
    (hn : ComputableInDegree fallback encA encC dn en)
    (hb : ComputableInDegree (fun p : α × β => body p.1 p.2) (encPair encA encB) encC db eb)
    (hd : max (max 1 (max dv dn)) (max ev (max 1 ev * db)) ≤ d)
    (he : max (max 1 ev * eb) en ≤ e) :
    ComputableInDegree (fun a => (value a).elim (fallback a) (body a)) encA encC d e := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine (hn.mono (by omega) (by omega)).of_enc_eq fun a => ?_
    cases value a with
    | none => rfl
    | some b => exact isEmptyElim b
  · obtain ⟨b₀⟩ := hβ
    simp only [Option.elim_eq_if_isSome b₀]
    have hg : ComputableInDegree (fun a => (value a).getD b₀) encA encB (max dv ev) ev :=
      ((getD (enc₁ := encB) b₀).comp hv).mono (by omega) (by omega)
    have hsome : ComputableInDegree (fun a => body a ((value a).getD b₀)) encA encC
        (max (max 1 (max dv ev)) (max 1 ev * db)) (max 1 ev * eb) :=
      hb.comp (id'.prod hg)
    exact ite_le ((isSome encB).comp hv) hsome hn (by omega) (by omega)

/-- **Eliminating an option** in linear time and space: the handler of `some` receives the input
and the value. -/
theorem optionElim_one {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hv : ComputableInDegree value encA (encOption encB) 1 1)
    (hn : ComputableInDegree fallback encA encC 1 1)
    (hb : ComputableInDegree (fun p : α × β => body p.1 p.2) (encPair encA encB) encC 1 1) :
    ComputableInDegree (fun a => (value a).elim (fallback a) (body a)) encA encC 1 1 :=
  optionElim_le hv hn hb (by omega) (by omega)

/-- **Convert a standard encoded option to a framed list**, without an inhabitant of the element
type. -/
theorem optionToList {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (Option.toList (α := α)) (encOption enc) (encList enc) 1 1 := by
  have hraw : ComputableInDegree (encOption enc) (encOption enc) encBits 1 1 :=
    of_eq fun _ => rfl
  have htail : ComputableInDegree (fun o : Option α => (encOption enc o).tail)
      (encOption enc) encBits 1 1 :=
    (Internal.DecoderWords.tail_degree.comp hraw).mono
  have hframe : ComputableInDegree (fun o : Option α => frame (encOption enc o).tail)
      (encOption enc) encBits 1 1 :=
    ((of_frame (f := frame) (encIn := encBits) (encMid := encBits) fun _ => rfl).comp htail).mono
  exact (ite_le (isSome enc) hframe (const []) (by decide) (by decide)).of_enc_eq fun o => by
    cases o <;> simp [encList_cons]

/-- **The head of a framed list**, as an option, in linear time and space. -/
@[fun_prop]
theorem head?_one {β : Type} [Inhabited β] {enc : β ↪ List Bool} :
    ComputableInDegree (fun l : List β => l.head?) (encList enc) (encOption enc) 1 1 := by
  have h : (fun l : List β => l.head?) =
      fun l => if l.isEmpty then none else some (l.headD default) := by
    funext l
    cases l <;> rfl
  rw [h]
  fun_prop (disch := first | apply le_refl | lia)

end Turing.MultiTapeTM.ComputableInDegree
