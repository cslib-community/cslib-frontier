/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Basic

/-!
# Search frontiers

The frontier of a best-first search ([RussellNorvig2020], §3.3.2) is a priority queue of nodes:
one can add an element, test for emptiness and pop an element of minimum priority. This module
states that interface abstractly, as a record `Frontier Q κ α` of operations on a carrier `Q`
holding elements of `α` under keys (priorities) of `κ`, together with an abstraction function to
the multiset of keyed elements it holds. `Frontier.Lawful` states the specification against that
multiset: the empty frontier holds nothing, insertion adds one keyed element, popping fails
exactly on an empty frontier, and otherwise removes an element whose key is at most every
remaining key. Emptiness is the failure of `popMin?`. Ties between equal keys are left to the
implementation.

The reference instance `Frontier.sortedList` keeps the keyed elements in a list sorted by key
(`List.orderedInsert`), and `Frontier.lawful_sortedList` proves it lawful. Among equal keys it pops
the most recently inserted element first.

## Main definitions

* `Cslib.Algorithms.Lean.Search.Frontier`: frontier operations with an abstraction function.
* `Frontier.Lawful`: the frontier specification.
* `SortedListFrontier`, `Frontier.sortedList`: the sorted-list reference instance.

## Main results

* `Frontier.lawful_sortedList`: the sorted-list frontier satisfies the specification.
* `Frontier.Lawful.exists_mem_of_popMin?`, `Frontier.Lawful.mem_of_mem_popMin?`,
  `Frontier.Lawful.mem_popMin?_of_ne`: membership before and after a pop.

## References

* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

universe u v w

/-- Frontier operations on a carrier `Q` holding elements of `α` with keys in `κ`: the empty
frontier, insertion of an element with a key, and removal of an element of minimum key
(`none` when the frontier is empty). The abstraction function `contents` gives the multiset of
keyed elements a frontier holds; it is used only to state `Frontier.Lawful`. -/
structure Frontier (Q : Type u) (κ : Type v) (α : Type w) where
  /-- The empty frontier. -/
  empty : Q
  /-- Insert an element with a key. -/
  insert : κ → α → Q → Q
  /-- Remove an element of minimum key and return it with the remaining frontier, or return
  `none` if the frontier is empty. -/
  popMin? : Q → Option (α × Q)
  /-- The keyed elements held by a frontier. -/
  contents : Q → Multiset (κ × α)

namespace Frontier

variable {Q : Type u} {κ : Type v} {α : Type w}

/-- The frontier specification: the empty frontier holds nothing; inserting adds the keyed
element; popping fails exactly when the frontier holds nothing; and a successful pop removes one
keyed element whose key is at most the key of every element left. -/
structure Lawful [LE κ] (F : Frontier Q κ α) : Prop where
  /-- The empty frontier holds nothing. -/
  contents_empty : F.contents F.empty = 0
  /-- Inserting adds the keyed element. -/
  contents_insert (k : κ) (a : α) (q : Q) : F.contents (F.insert k a q) = (k, a) ::ₘ F.contents q
  /-- Popping fails exactly on a frontier holding nothing. -/
  popMin?_eq_none_iff (q : Q) : F.popMin? q = none ↔ F.contents q = 0
  /-- A successful pop removes a keyed element whose key is at most every remaining key. -/
  exists_of_popMin?_eq_some {q q' : Q} {a : α} (h : F.popMin? q = some (a, q')) :
    ∃ k, F.contents q = (k, a) ::ₘ F.contents q' ∧ ∀ p ∈ F.contents q', k ≤ p.1

namespace Lawful

variable [LE κ] {F : Frontier Q κ α} {q q' : Q} {a : α}

/-- The element a successful pop returns was held, under some key, before the pop. -/
theorem exists_mem_of_popMin? (hF : F.Lawful) (h : F.popMin? q = some (a, q')) :
    ∃ k, (k, a) ∈ F.contents q := by
  obtain ⟨k, hq, -⟩ := hF.exists_of_popMin?_eq_some h
  exact ⟨k, by rw [hq]; exact Multiset.mem_cons_self _ _⟩

/-- Every keyed element held after a successful pop was held before it. -/
theorem mem_of_mem_popMin? (hF : F.Lawful) (h : F.popMin? q = some (a, q')) {p : κ × α}
    (hp : p ∈ F.contents q') : p ∈ F.contents q := by
  obtain ⟨k, hq, -⟩ := hF.exists_of_popMin?_eq_some h
  rw [hq]
  exact Multiset.mem_cons_of_mem hp

/-- A keyed element held before a successful pop, whose element is not the popped one, is held
after it. -/
theorem mem_popMin?_of_ne (hF : F.Lawful) (h : F.popMin? q = some (a, q')) {p : κ × α}
    (hp : p ∈ F.contents q) (hne : p.2 ≠ a) : p ∈ F.contents q' := by
  obtain ⟨k, hq, -⟩ := hF.exists_of_popMin?_eq_some h
  rw [hq, Multiset.mem_cons] at hp
  rcases hp with rfl | hp
  · exact absurd rfl hne
  · exact hp

end Lawful

end Frontier

/-- A list of keyed elements sorted by nondecreasing key: the carrier of the reference
frontier. -/
structure SortedListFrontier (κ : Type v) (α : Type w) [LinearOrder κ] where
  /-- The keyed elements, in nondecreasing order of key. -/
  toList : List (κ × α)
  /-- The keys are nondecreasing. -/
  pairwise : toList.Pairwise fun p q => p.1 ≤ q.1

namespace Frontier

variable {κ : Type v} {α : Type w} [LinearOrder κ]

/-- The sorted-list frontier: insertion places the keyed element before the first element of
greater or equal key, and popping removes the head. -/
@[expose] def sortedList : Frontier (SortedListFrontier κ α) κ α where
  empty := ⟨[], List.Pairwise.nil⟩
  insert k a q :=
    ⟨q.toList.orderedInsert (fun p q => p.1 ≤ q.1) (k, a),
      haveI : Std.Total fun p q : κ × α => p.1 ≤ q.1 := ⟨fun p q => le_total p.1 q.1⟩
      haveI : IsTrans (κ × α) fun p q => p.1 ≤ q.1 := ⟨fun _ _ _ => le_trans⟩
      q.pairwise.orderedInsert (k, a) _⟩
  popMin? q :=
    match q with
    | ⟨[], _⟩ => none
    | ⟨x :: l, h⟩ => some (x.2, ⟨l, (List.pairwise_cons.1 h).2⟩)
  contents q := q.toList

/-- The sorted-list frontier satisfies the frontier specification. -/
theorem lawful_sortedList : (sortedList : Frontier (SortedListFrontier κ α) κ α).Lawful where
  contents_empty := rfl
  contents_insert k a q := Multiset.coe_eq_coe.2 (List.perm_orderedInsert _ _ _)
  popMin?_eq_none_iff q := by
    rcases q with ⟨_ | ⟨x, l⟩, h⟩ <;> simp [sortedList]
  exists_of_popMin?_eq_some {q q' a} hpop := by
    rcases q with ⟨_ | ⟨x, l⟩, h⟩
    · simp [sortedList] at hpop
    · simp only [sortedList, Option.some.injEq, Prod.mk.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      refine ⟨x.1, rfl, fun p hp => (List.pairwise_cons.1 h).1 p hp⟩

end Frontier

end Cslib.Algorithms.Lean.Search
