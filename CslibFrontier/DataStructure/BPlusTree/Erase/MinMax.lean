/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Erase.Basic
public import CslibFrontier.DataStructure.BPlusTree.MinMax

/-!
# Removing the least and the greatest entry of a B+-tree

`eraseMinM` and `eraseMaxM` find the least or the greatest entry of a B+-tree of
`Cslib.DataStructure.BPlusTree` with `minM` or `maxM` and then erase its key with `eraseM`, as
the classic `Cslib.DataStructure.BTree.eraseMinM` does. Each is defined once over an arbitrary
monad, with a comparator and a node-visit action; `eraseMin?` and `eraseMax?` are the `Id`
instantiations. The tree is walked twice, once to find the entry and once to erase it. Costs are
not stated here.

## Main definitions

* `eraseMinM`, `eraseMaxM`: removal of the least and the greatest entry, polymorphic.
* `eraseMin?`, `eraseMax?`: the pure operations.

## Main results

* `map_eraseMinM`, `map_eraseMaxM`: a monad morphism commutes with the removals.
* `eraseMin?_eq`, `eraseMax?_eq`: on a well-formed tree, the first or the last entry together
  with the tree with its key erased.
* `eraseMin?_eq_some_iff`, `eraseMax?_eq_some_iff`: when an entry and a tree are returned.
* `toList_of_eraseMin?_eq_some`, `toList_of_eraseMax?_eq_some`: the returned tree has the entries
  after the first, or before the last.
* `IsWF.of_eraseMin?_eq_some`, `IsWF.of_eraseMax?_eq_some`: the returned tree is well-formed.

## References

* [D. Comer, *The Ubiquitous B-Tree*][Comer1979]

The statements here are not taken from a source.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Remove and return the least entry: find it with `minM`, then erase its key. -/
@[expose] def eraseMinM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BPlusTree α β) :
    m (Option ((α × β) × BPlusTree α β)) := do
  match ← minM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Remove and return the greatest entry: find it with `maxM`, then erase its key. -/
@[expose] def eraseMaxM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BPlusTree α β) :
    m (Option ((α × β) × BPlusTree α β)) := do
  match ← maxM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Removing the least entry finds it with `minM`, then erases its key. -/
theorem eraseMinM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BPlusTree α β) :
    eraseMinM t le visit tr = (do
      match ← minM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := (rfl)

/-- Removing the greatest entry finds it with `maxM`, then erases its key. -/
theorem eraseMaxM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BPlusTree α β) :
    eraseMaxM t le visit tr = (do
      match ← maxM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := (rfl)

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the removal of the least entry. -/
theorem map_eraseMinM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool) (visit : m Unit)
    (tr : BPlusTree α β) :
    f (eraseMinM t le visit tr) = eraseMinM t (fun a b => f (le a b)) (f visit) tr := by
  simp only [eraseMinM_def, hf.map_bind, map_minM hf]
  refine bind_congr fun o => ?_
  cases o <;> simp [hf.map_bind, hf.map_pure, map_eraseM hf]

/-- A monad morphism commutes with the removal of the greatest entry. -/
theorem map_eraseMaxM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool) (visit : m Unit)
    (tr : BPlusTree α β) :
    f (eraseMaxM t le visit tr) = eraseMaxM t (fun a b => f (le a b)) (f visit) tr := by
  simp only [eraseMaxM_def, hf.map_bind, map_maxM hf]
  refine bind_congr fun o => ?_
  cases o <;> simp [hf.map_bind, hf.map_pure, map_eraseM hf]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BPlusTree α β}

/-- Remove and return the least entry, pure. -/
@[expose] def eraseMin? (t : ℕ) (tr : BPlusTree α β) : Option ((α × β) × BPlusTree α β) :=
  Id.run (eraseMinM t leI (pure ()) tr)

/-- Remove and return the greatest entry, pure. -/
@[expose] def eraseMax? (t : ℕ) (tr : BPlusTree α β) : Option ((α × β) × BPlusTree α β) :=
  Id.run (eraseMaxM t leI (pure ()) tr)

/-- `eraseMin?` is the `Id` instantiation of `eraseMinM`. -/
theorem eraseMin?_def : eraseMin? t tr = Id.run (eraseMinM t leI (pure ()) tr) := (rfl)

/-- `eraseMax?` is the `Id` instantiation of `eraseMaxM`. -/
theorem eraseMax?_def : eraseMax? t tr = Id.run (eraseMaxM t leI (pure ()) tr) := (rfl)

/-- `eraseMin?` is the least entry together with the erasure of its key. -/
theorem eraseMin?_eq_map_min? : eraseMin? t tr = (min? tr).map fun p => (p, erase t p.1 tr) := by
  rw [min?_def]
  unfold eraseMin? eraseMinM
  -- In `Id`, bind is application and `pure` is the identity, so each branch of the monadic
  -- `match` on the found entry is the corresponding branch of `Option.map` by definition.
  cases minM (m := Id) (pure ()) tr <;> rfl

/-- `eraseMax?` is the greatest entry together with the erasure of its key. -/
theorem eraseMax?_eq_map_max? : eraseMax? t tr = (max? tr).map fun p => (p, erase t p.1 tr) := by
  rw [max?_def]
  unfold eraseMax? eraseMaxM
  -- as in `eraseMin?_eq_map_min?`
  cases maxM (m := Id) (pure ()) tr <;> rfl

/-- Model equation of `eraseMin?` on well-formed trees: the first entry and the tree with its key
erased. -/
theorem eraseMin?_eq (h : IsWF t tr) :
    eraseMin? t tr = tr.toList.head?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMin?_eq_map_min?, min?_eq h]

/-- Model equation of `eraseMax?` on well-formed trees: the last entry and the tree with its key
erased. -/
theorem eraseMax?_eq (h : IsWF t tr) :
    eraseMax? t tr = tr.toList.getLast?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMax?_eq_map_max?, max?_eq h]

/-- On a well-formed tree, `eraseMin?` returns `p` and `tr'` exactly when `p` is the first entry
and `tr'` the tree with its key erased. -/
theorem eraseMin?_eq_some_iff (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β} :
    eraseMin? t tr = some (p, tr') ↔ tr.toList.head? = some p ∧ tr' = erase t p.1 tr := by
  rw [eraseMin?_eq h, Option.map_eq_some_iff]
  simp only [Prod.mk.injEq]
  exact ⟨fun ⟨_, hq, rfl, htr⟩ => ⟨hq, htr.symm⟩, fun ⟨hp, htr⟩ => ⟨p, hp, rfl, htr.symm⟩⟩

/-- On a well-formed tree, `eraseMax?` returns `p` and `tr'` exactly when `p` is the last entry
and `tr'` the tree with its key erased. -/
theorem eraseMax?_eq_some_iff (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β} :
    eraseMax? t tr = some (p, tr') ↔ tr.toList.getLast? = some p ∧ tr' = erase t p.1 tr := by
  rw [eraseMax?_eq h, Option.map_eq_some_iff]
  simp only [Prod.mk.injEq]
  exact ⟨fun ⟨_, hq, rfl, htr⟩ => ⟨hq, htr.symm⟩, fun ⟨hp, htr⟩ => ⟨p, hp, rfl, htr.symm⟩⟩

/-- On a well-formed tree, the tree that `eraseMin?` returns has the entries after the first. -/
theorem toList_of_eraseMin?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β}
    (he : eraseMin? t tr = some (p, tr')) : tr'.toList = tr.toList.tail := by
  obtain ⟨hq, rfl⟩ := (eraseMin?_eq_some_iff h).1 he
  obtain ⟨l, hl⟩ := List.head?_eq_some_iff.1 hq
  have hs := h.sorted
  rw [hl, List.isSortedAssoc_cons_iff] at hs
  rw [toList_erase h, hl, SortedAssoc.erase_cons]
  simp only [↓reduceIte, List.tail_cons]
  exact SortedAssoc.erase_of_forall_ne fun r hr => (hs.1 r hr).ne'

/-- On a well-formed tree, the tree that `eraseMax?` returns has the entries before the last. -/
theorem toList_of_eraseMax?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β}
    (he : eraseMax? t tr = some (p, tr')) : tr'.toList = tr.toList.dropLast := by
  obtain ⟨hq, rfl⟩ := (eraseMax?_eq_some_iff h).1 he
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hq
  have hs := h.sorted
  rw [hl, List.isSortedAssoc_append_iff] at hs
  rw [toList_erase h, hl, SortedAssoc.erase_append,
    SortedAssoc.erase_of_forall_ne fun r hr => (hs.2.2 r hr p (by simp)).ne]
  simp [SortedAssoc.erase_cons]

/-- On a well-formed tree, the tree that `eraseMin?` returns is well-formed. -/
theorem IsWF.of_eraseMin?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β}
    (he : eraseMin? t tr = some (p, tr')) : IsWF t tr' :=
  ((eraseMin?_eq_some_iff h).1 he).2 ▸ h.erase _

/-- On a well-formed tree, the tree that `eraseMax?` returns is well-formed. -/
theorem IsWF.of_eraseMax?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BPlusTree α β}
    (he : eraseMax? t tr = some (p, tr')) : IsWF t tr' :=
  ((eraseMax?_eq_some_iff h).1 he).2 ▸ h.erase _

end Pure

end BPlusTree

end Cslib.DataStructure
