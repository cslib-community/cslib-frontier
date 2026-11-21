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

end Pure

end BPlusTree

end Cslib.DataStructure
