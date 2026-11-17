/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Encoding.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words

-- vendored: layout-preserving aliases of Cslib.Encoding; machine certificates remain local.

/-!
# Tagged sum encodings

A Boolean tag selects the payload encoding: `false` for the left summand and `true` for the
right summand. This permits differently encoded, possibly empty summands without padding.
The shared right constructor, classifier and default extractor supply canonical option capabilities
without repeating the tag dispatch.

## Main definitions

* `Turing.MultiTapeTM.encSum`: a tagged sum of two supplied encodings.
-/

public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- Encode a sum with one tag bit followed by the corresponding payload. -/
abbrev encSum (left : α ↪ List Bool) (right : β ↪ List Bool) : α ⊕ β ↪ List Bool :=
  Cslib.Encoding.encSum left right

@[simp]
theorem encSum_inl (left : α ↪ List Bool) (right : β ↪ List Bool) (a : α) :
    encSum left right (.inl a) = false :: left a := rfl

@[simp]
theorem encSum_inr (left : α ↪ List Bool) (right : β ↪ List Bool) (b : β) :
    encSum left right (.inr b) = true :: right b := rfl

/-- The encoding charges the selected payload and exactly one tag bit. -/
theorem length_encSum (left : α ↪ List Bool) (right : β ↪ List Bool) (value : α ⊕ β) :
    (encSum left right value).length =
      value.elim (fun a => (left a).length) (fun b => (right b).length) + 1 := by
  cases value <;> simp

namespace ComputableInDegree

/-- Read the constructor bit, with constant encoded-output growth. -/
theorem sumIsRight (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree Sum.isRight (encSum left right) encBool 1 0 := by
  have h : ComputableInDegree Sum.isRight (encSum left right) encBool 1 1 :=
    .of_take_one fun value => by cases value <;> rfl
  exact ⟨h.1, 1, fun value => by cases value <;> simp⟩

/-- Prepend the right constructor bit to a payload. -/
@[fun_prop]
theorem inr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInDegree (Sum.inr (α := α) (β := β)) right (encSum left right) 1 1 :=
  .of_cons_true fun _ => rfl

/-- Extract the right payload, replacing a left value by an explicit default. -/
theorem sumRightD (left : α ↪ List Bool) (right : β ↪ List Bool) (default : β) :
    ComputableInDegree (Sum.elim (Function.const α default) id)
      (encSum left right) right 1 1 := by
  have payload : ComputableInDegree
      (fun value : {value : α ⊕ β // value.isRight = true} =>
        value.val.elim (Function.const α default) id)
      ((Function.Embedding.subtype fun value : α ⊕ β => value.isRight = true).trans
        (encSum left right)) right 1 1 :=
    ComputableInDegree.of_tail fun ⟨value, h⟩ => by
      cases value with
      | inl value => cases h
      | inr value => rfl
  convert ComputableInDegree.ite
    (f := Sum.elim (Function.const α default) id) (g := fun _ => default)
    (sumIsRight left right) payload
    ((ComputableInDegree.const (encIn := encSum left right) (encMid := right) default).restrict
      (fun value : α ⊕ β => value.isRight = false)) using 1
  · funext value
    cases value <;> rfl
  · decide
  · decide

end ComputableInDegree

end Turing.MultiTapeTM
