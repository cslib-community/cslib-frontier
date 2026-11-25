/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.SortedAssoc
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Comparator-polymorphic updates of sorted association lists

Insertion and erasure of `Cslib.SortedAssoc` written as left-to-right scans over an arbitrary
monad `m`, with a comparator `le : α → α → m Bool` and no order instance in scope, so that every
comparison of keys goes through `le`. They are the updates that go with the queries of
`Cslib.SortedAssoc.lookupM` and its siblings, and they compare in the same pattern as `lookupM`:
one question per entry up to and including the first key that is not below the query, and one
more at that entry to tell equality from a strictly larger key.

`insertM` replaces the entry where it stops if the keys are equal and inserts before it
otherwise, appending when it reaches the end of the list. `eraseM` drops the entry where it stops
if the keys are equal and otherwise leaves the list as it is.

With the comparator `Cslib.SortedAssoc.leI` of a linear order, the identity-monad instance of
`insertM` is `Cslib.SortedAssoc.insert` on every list: in a linear order the two recursions agree
branch by branch.
The instance of `eraseM` is `Cslib.SortedAssoc.erase` on a sorted list. Sortedness is needed
there: the scan removes at most one entry and stops early, whereas the model function, a filter,
removes every entry with the key.

A leaf of a B+-tree is a sorted association list, and these scans are its updates.

## Main definitions

* `Cslib.SortedAssoc.insertM`: insert-or-replace by a scan.
* `Cslib.SortedAssoc.eraseM`: erasure by a scan.

## Main results

* `Cslib.SortedAssoc.idRun_insertM`: the pure instance of `insertM` is `insert`.
* `Cslib.SortedAssoc.idRun_eraseM`: on a sorted list the pure instance of `eraseM` is `erase`.
* `Cslib.SortedAssoc.map_insertM`, `map_eraseM`: a monad morphism commutes with each scan.
-/

public section

universe w

namespace Cslib.SortedAssoc

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Insert-or-replace by a scan: stop at the first key not below `k` and test it for equality
with a second comparison; replace that entry if the keys are equal, and insert before it
otherwise. A scan that reaches the end of the list appends. -/
@[expose] def insertM (le : α → α → m Bool) (k : α) (v : β) : List (α × β) → m (List (α × β))
  | [] => pure [(k, v)]
  | (k', v') :: l => do
    if ← le k k' then
      if ← le k' k then pure ((k, v) :: l) else pure ((k, v) :: (k', v') :: l)
    else return (k', v') :: (← insertM le k v l)

/-- Erasure by a scan: stop at the first key not below `k` and test it for equality with a
second comparison; drop that entry if the keys are equal, and leave the list unchanged
otherwise. -/
@[expose] def eraseM (le : α → α → m Bool) (k : α) : List (α × β) → m (List (α × β))
  | [] => pure []
  | (k', v') :: l => do
    if ← le k k' then
      if ← le k' k then pure l else pure ((k', v') :: l)
    else return (k', v') :: (← eraseM le k l)

end Polymorphic

section Transfer

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the insert scan. -/
theorem map_insertM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (v : β)
    (l : List (α × β)) : f (insertM le k v l) = insertM (fun a b => f (le a b)) k v l := by
  induction l with
  | nil => simp only [insertM, hf.map_pure]
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [insertM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with the erase scan. -/
theorem map_eraseM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α) (l : List (α × β)) :
    f (eraseM le k l) = eraseM (fun a b => f (le a b)) k l := by
  induction l with
  | nil => simp only [eraseM, hf.map_pure]
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [eraseM, hf.map_bind, hf.map_pure, apply_ite f, ih]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {l : List (α × β)} {k k' : α} {v v' : β}

/-- The pure insert scan at an entry: stop at a key not below `k`, replacing it on equality, and
move on otherwise. -/
private theorem idRun_insertM_cons :
    Id.run (insertM leI k v ((k', v') :: l)) =
      if k ≤ k' then (if k' ≤ k then (k, v) :: l else (k, v) :: (k', v') :: l)
      else (k', v') :: Id.run (insertM leI k v l) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;>
    simp only [insertM, leI, Id.run_bind, Id.run_pure, decide_eq_true_eq, h₁, h₂, ↓reduceIte]

/-- The pure erase scan at an entry: stop at a key not below `k`, dropping it on equality, and
move on otherwise. -/
private theorem idRun_eraseM_cons :
    Id.run (eraseM leI k ((k', v') :: l)) =
      if k ≤ k' then (if k' ≤ k then l else (k', v') :: l)
      else (k', v') :: Id.run (eraseM leI k l) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;>
    simp only [eraseM, leI, Id.run_bind, Id.run_pure, decide_eq_true_eq, h₁, h₂, ↓reduceIte]

/-- The pure insert scan is `insert`, on any list. -/
theorem idRun_insertM (k : α) (v : β) (l : List (α × β)) :
    Id.run (insertM leI k v l) = insert k v l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    rw [idRun_insertM_cons, insert_cons, ih]
    rcases lt_trichotomy k k' with h | rfl | h
    · simp only [h, h.le, not_le.2 h, ↓reduceIte]
    · simp only [le_refl, lt_self_iff_false, ↓reduceIte]
    · simp only [not_le.2 h, not_lt.2 h.le, h.ne', ↓reduceIte]

/-- On a sorted list the pure erase scan is `erase`. -/
theorem idRun_eraseM (h : l.IsSortedAssoc) (k : α) : Id.run (eraseM leI k l) = erase k l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    rw [List.isSortedAssoc_cons_iff] at h
    rw [idRun_eraseM_cons, erase_cons]
    rcases lt_trichotomy k k' with h₁ | rfl | h₁
    · simp only [h₁.le, not_le.2 h₁, h₁.ne', ↓reduceIte]
      rw [erase_of_forall_ne fun q hq => (h₁.trans (h.1 q hq)).ne']
    · simp only [le_refl, ↓reduceIte]
      rw [erase_of_forall_ne fun q hq => (h.1 q hq).ne']
    · simp only [not_le.2 h₁, h₁.ne, ↓reduceIte, ih h.2]

end Pure

end Cslib.SortedAssoc
