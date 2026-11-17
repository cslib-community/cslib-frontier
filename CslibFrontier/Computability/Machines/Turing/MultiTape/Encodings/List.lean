/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Encoding.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words

-- vendored: layout-preserving aliases of Cslib.Encoding; machine certificates remain local.

/-!
# Encodings of lists

`encList enc` encodes a list as the concatenation of its framed elements
(`Turing.MultiTapeTM.frame`), for any encoding `enc` of the elements. Lists of Booleans also have
the plain encoding `encBits`, the list itself, which is the concatenation of the elements encoded by
`Turing.MultiTapeTM.encBool`. Both have the capabilities of `Turing.MultiTapeTM.ListEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encList`: the concatenation of the framed elements.
* `Turing.MultiTapeTM.encBits`: lists of Booleans encoded as themselves.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Lists encoded as the concatenation of their framed elements. -/
public abbrev encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  Cslib.Encoding.encList enc

variable {enc : α ↪ List Bool}

@[simp]
public lemma encList_nil : encList enc [] = [] := rfl

@[simp]
public lemma encList_cons (a : α) (l : List α) :
    encList enc (a :: l) = frame (enc a) ++ encList enc l := rfl

/-- Concatenation of lists is concatenation of their framed encodings. -/
@[simp]
public lemma encList_append {α : Type*} (enc : α ↪ List Bool) (l₁ l₂ : List α) :
    encList enc (l₁ ++ l₂) = encList enc l₁ ++ encList enc l₂ :=
  Cslib.Encoding.encList_append enc l₁ l₂

public instance : ListEncoding enc (encList enc) where
  headD d := .of_isEmpty_ite d (fun l hl => by cases l <;> simp_all)
    (.of_unframe fun ⟨l, hl⟩ => by cases l <;> simp at hl ⊢)
  tail := .of_dropFrame fun l => by cases l <;> simp
  isEmpty := .of_isEmpty fun l => by cases l <;> simp

/-- Lists of Booleans encoded as themselves. -/
public abbrev encBits : List Bool ↪ List Bool := Cslib.Encoding.encBits

@[simp]
public lemma encBits_apply (l : List Bool) : encBits l = l := rfl

public instance : ListEncoding encBool encBits where
  headD d := .of_isEmpty_ite d (fun l hl => by simp_all)
    (.of_take_one fun ⟨l, hl⟩ => by cases l; exacts [by simp at hl, rfl])
  tail := .of_tail fun _ => rfl
  isEmpty := .of_isEmpty fun _ => rfl

end Turing.MultiTapeTM
