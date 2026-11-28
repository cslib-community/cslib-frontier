/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Basic
public import CslibFrontier.Foundations.Data.List.SortedAssoc.Scan

/-!
# Search in B+-trees

Lookup in the B+-trees of `Cslib.DataStructure.BPlusTree`. Each operation is defined once over
an arbitrary monad `m`, with a comparator `le : α → α → m Bool` and a node-visit action
`visit : m Unit`, and no order instance in scope, so that every comparison of keys goes through
`le`. The pure operations are the `Id` instantiations with the comparator
`Cslib.SortedAssoc.leI` of a linear order and `visit := pure ()`. Costs are not stated here.

A search descends through the interior nodes by the separators and ends in a leaf. At an interior
node it passes the separators that are at most the query and enters the child introduced by the
last of them, or the first child when there is none; one comparison per separator passed, and
one more where it stops. In the leaf it runs the scan `Cslib.SortedAssoc.lookupM` of the entry
list. `visit` fires once at each node on the path, the leaf included. A separator equal to the
query does not end the search: separators are not entries.

`slotM` is the within-node separator search on its own: the number of separators that the search
passes, which is the position of the child it enters.

The model equation `lookup_eq` holds on well-formed trees. Sorted entries and the separator
convention are not enough for it: the search trusts a separator to bound every later child from
below, and that follows from the convention only through a key of the child the separator
introduces, so the children must not be empty. Occupancy at `2 ≤ t` provides that.

## Main definitions

* `slotM`, `slot`: the within-node separator search.
* `lookupM`, `containsM`: lookup and the membership test, polymorphic.
* `lookup`, `contains`: the pure operations.
* `SearchInvariant`: the premises shared by the ordered-list model proofs.

## Main results

* `map_slotM`, `map_lookupM`, `map_containsM`: a monad morphism commutes with the operations.
* `slot_eq_length_takeWhile`: the pure separator search counts the leading separators that are
  at most the query.
* `Occupied.size_pos`: an occupied tree has an entry when `2 ≤ t`.
* `lookup_eq`: on a well-formed tree, `lookup` is `List.lookup` on `toList`.
* `contains_iff`: on a well-formed tree, `contains` decides membership of the key.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node separator search: the number of leading separators that are at most `k`, which is
the position of the child a search for `k` enters. One comparison per separator passed, and one
more where it stops. -/
@[expose] def slotM (le : α → α → m Bool) (k : α) : List (Branch α β) → m ℕ
  | [] => pure 0
  | (s, _) :: rest => do
    if ← le s k then return (← slotM le k rest) + 1 else pure 0

/-- Lookup. At an interior node, pass the separators that are at most `k` and descend into the
child introduced by the last of them; in a leaf, scan the entries. `visit` fires once at each
node on the path. -/
@[expose] def lookupM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BPlusTree α β → m (Option β)
  | .leaf entries => do
    visit
    SortedAssoc.lookupM le k entries
  | .node first [] => do
    visit
    lookupM le visit k first
  | .node first ((s, c) :: rest) => do
    if ← le s k then
      lookupM le visit k (.node c rest)
    else
      visit
      lookupM le visit k first
termination_by tr => sizeOf tr

/-- Membership test: whether lookup succeeds. -/
@[expose] def containsM (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BPlusTree α β) :
    m Bool := do
  return (← lookupM le visit k tr).isSome

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the within-node separator search. -/
theorem map_slotM (hf : IsMonadHom m n f) (le : α → α → m Bool) (k : α)
    (rest : List (Branch α β)) : f (slotM le k rest) = slotM (fun a b => f (le a b)) k rest := by
  induction rest with
  | nil => simp [slotM, hf.map_pure]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp [slotM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with lookup. -/
theorem map_lookupM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    f (lookupM le visit k tr) = lookupM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction lookupM le visit k tr <;>
    simp [lookupM, hf.map_bind, apply_ite f, SortedAssoc.map_lookupM hf, *]

/-- A monad morphism commutes with the membership test. -/
theorem map_containsM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    f (containsM le visit k tr) = containsM (fun a b => f (le a b)) (f visit) k tr := by
  simp [containsM, hf.map_bind, hf.map_pure, map_lookupM hf]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BPlusTree α β} {k : α}

/-- Pure within-node separator search: the `Id` instantiation of `slotM`. -/
@[expose] def slot (k : α) (rest : List (Branch α β)) : ℕ := Id.run (slotM leI k rest)

/-- Pure lookup: the `Id` instantiation of `lookupM` with `visit := pure ()`. -/
def lookup (k : α) (tr : BPlusTree α β) : Option β := Id.run (lookupM leI (pure ()) k tr)

/-- Pure membership test: the `Id` instantiation of `containsM` with `visit := pure ()`. -/
def contains (k : α) (tr : BPlusTree α β) : Bool := Id.run (containsM leI (pure ()) k tr)

/-- `slot` is the `Id` instantiation of `slotM`. -/
theorem slot_def (k : α) (rest : List (Branch α β)) :
    slot k rest = Id.run (slotM leI k rest) := (rfl)

/-- `lookup` is the `Id` instantiation of `lookupM`. -/
theorem lookup_def (k : α) : lookup k tr = Id.run (lookupM leI (pure ()) k tr) := (rfl)

/-- `contains` is the `Id` instantiation of `containsM`. -/
theorem contains_def (k : α) : contains k tr = Id.run (containsM leI (pure ()) k tr) := (rfl)

/-- The separator search in a node without separators stops at position zero. -/
@[simp] theorem slot_nil (k : α) : slot (β := β) k [] = 0 := rfl

/-- The separator search passes a separator that is at most `k`, and stops otherwise. -/
@[simp] theorem slot_cons (k s : α) (c : BPlusTree α β) (rest : List (Branch α β)) :
    slot k ((s, c) :: rest) = if s ≤ k then slot k rest + 1 else 0 := by
  by_cases hk : s ≤ k <;> simp [slot, slotM, leI, hk]

/-- The pure separator search counts the leading separators that are at most `k`. -/
theorem slot_eq_length_takeWhile (k : α) (rest : List (Branch α β)) :
    slot k rest = (rest.takeWhile fun e => decide (e.1 ≤ k)).length := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    by_cases hk : s ≤ k <;> simp [hk, ih]

/-- Lookup in a leaf is the scan of its entries. -/
theorem lookup_leaf (k : α) (entries : List (α × β)) :
    lookup k (.leaf entries) = Id.run (SortedAssoc.lookupM leI k entries) := by
  simp [lookup, lookupM]

/-- Lookup in a node without separators descends into its only child. -/
@[simp] theorem lookup_node_nil (k : α) (first : BPlusTree α β) :
    lookup k (.node first []) = lookup k first := by
  simp [lookup, lookupM]

/-- Lookup at a node's first separator: pass it when it is at most the query, and otherwise
descend into the child before it. -/
@[simp] theorem lookup_node_cons (k s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    lookup k (.node first ((s, c) :: rest)) =
      if s ≤ k then lookup k (.node c rest) else lookup k first := by
  by_cases h : s ≤ k <;> simp [lookup, lookupM, leI, h]

/-- Membership is success of lookup. -/
@[simp] theorem contains_eq_isSome_lookup (k : α) : contains k tr = (lookup k tr).isSome := (rfl)

/-! ### The separator convention along a node -/

omit [LinearOrder α] in
/-- The entries of a node are those of its first child followed by those of the node without its
first child and separator. -/
theorem toList_node_cons {first c : BPlusTree α β} {s : α} {rest : List (Branch α β)} :
    (node first ((s, c) :: rest)).toList = first.toList ++ (node c rest).toList := by
  simp

/-- A separated node without its first child and separator is separated. -/
theorem Separated.tail {first c : BPlusTree α β} {s : α} {rest : List (Branch α β)}
    (h : Separated (.node first ((s, c) :: rest))) : Separated (.node c rest) := by
  have hp := List.pairwise_cons.1 h.pairwise
  exact .node (h.of_mem_rest (e := (s, c)) List.mem_cons_self)
    (fun e he => h.of_mem_rest (List.mem_cons_of_mem _ he))
    (fun e he p hp' => h.le_of_mem (List.mem_cons_of_mem _ he) hp') hp.2
    fun e he p hp' => hp.1 e he p hp'

omit [LinearOrder α] in
/-- An occupied tree has an entry when `2 ≤ t`: every leaf has at least `t - 1` entries. -/
theorem Occupied.size_pos {c : BPlusTree α β} (ht : 2 ≤ t) (ho : Occupied t c) : 0 < c.size := by
  induction c with
  | leaf entries =>
    have := ho.le_width
    simp only [width_leaf] at this
    simp only [size_leaf]
    omega
  | node first rest ih _ =>
    have := ih ho.first
    rw [size_node]
    omega

/-- In a separated node with sorted entries whose second child is not empty, the first separator
is at most every key after the first child: the keys of the second child are at least it by the
convention, and the later keys are above those. -/
theorem Separated.le_of_mem_tail {first c : BPlusTree α β} {s : α} {rest : List (Branch α β)}
    (h : Separated (.node first ((s, c) :: rest)))
    (hs : (BPlusTree.node first ((s, c) :: rest)).toList.IsSortedAssoc) (hc : 0 < c.size)
    {q : α × β} (hq : q ∈ (BPlusTree.node c rest).toList) : s ≤ q.1 := by
  rw [toList_node_cons, List.isSortedAssoc_append_iff] at hs
  have hcs := hs.2.1
  rw [toList_node, List.isSortedAssoc_append_iff] at hcs
  rw [toList_node, List.mem_append] at hq
  rcases hq with hq | hq
  · exact h.le_of_mem (e := (s, c)) List.mem_cons_self hq
  · obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos (l := c.toList) hc
    exact (h.le_of_mem (e := (s, c)) List.mem_cons_self hp).trans (hcs.2.2 p hp q hq).le

/-- Conditions needed to route a search in a B+-tree against its ordered list of entries.
They also hold for a suffix of an interior node, where the remaining root may have no separator. -/
structure SearchInvariant (t : ℕ) (tr : BPlusTree α β) : Prop where
  /-- The degree makes occupied children nonempty. -/
  two_le : 2 ≤ t
  /-- Separators divide the keys at each node. -/
  separated : Separated tr
  /-- The flattened entries are sorted by key. -/
  sorted : tr.toList.IsSortedAssoc
  /-- All immediate children are occupied. -/
  occupied : ∀ c ∈ tr.children, Occupied t c

/-- A well-formed tree satisfies the search invariant. -/
theorem IsWF.searchInvariant (h : IsWF t tr) : SearchInvariant t tr :=
  ⟨h.two_le, h.separated, h.sorted, h.occupied_of_mem_children⟩

/-- The search invariant passes to any child. -/
theorem SearchInvariant.child (h : SearchInvariant t tr) {c : BPlusTree α β}
    (hc : c ∈ tr.children) : SearchInvariant t c :=
  ⟨h.two_le, h.separated.of_mem_children hc, h.sorted.sublist (toList_sublist_of_mem_children hc),
    fun _ hx => (h.occupied c hc).of_mem_children hx⟩

/-- Passing the first separator preserves the search invariant on the remaining node. -/
theorem SearchInvariant.tail {first c : BPlusTree α β} {s : α} {rest : List (Branch α β)}
    (h : SearchInvariant t (.node first ((s, c) :: rest))) :
    SearchInvariant t (.node c rest) := by
  have hs := h.sorted
  rw [toList_node_cons, List.isSortedAssoc_append_iff] at hs
  refine ⟨h.two_le, h.separated.tail, hs.2.1, fun d hd => h.occupied d ?_⟩
  simp only [children_node, List.map_cons, List.mem_cons] at hd ⊢
  exact Or.inr hd

/-- Lookup against the model under the search invariant. -/
private theorem lookup_eq_of (k : α) :
    ∀ tr : BPlusTree α β, SearchInvariant t tr → lookup k tr = List.lookup k tr.toList
  | .leaf entries, h => by
    rw [lookup_leaf, toList_leaf]
    exact SortedAssoc.idRun_lookupM (by simpa using h.sorted) k
  | .node first [], h => by
    rw [lookup_node_nil, lookup_eq_of k first (h.child List.mem_cons_self)]
    simp
  | .node first ((s, c) :: rest), h => by
    rw [lookup_node_cons, toList_node_cons]
    by_cases hk : s ≤ k
    · simp only [hk, ↓reduceIte]
      rw [List.lookup_append_of_forall_lt fun p hp =>
        (h.separated.lt_of_mem_first (e := (s, c)) List.mem_cons_self hp).trans_le hk]
      exact lookup_eq_of k (.node c rest) h.tail
    · simp only [hk, ↓reduceIte]
      have hc := h.occupied c (by simp)
      rw [List.lookup_append_of_forall_gt fun q hq =>
        (lt_of_not_ge hk).trans_le (h.separated.le_of_mem_tail h.sorted (hc.size_pos h.two_le) hq)]
      exact lookup_eq_of k first (h.child List.mem_cons_self)
termination_by tr => sizeOf tr

/-- Model equation of lookup on well-formed trees. -/
theorem lookup_eq (h : IsWF t tr) (k : α) : lookup k tr = List.lookup k tr.toList :=
  lookup_eq_of k tr h.searchInvariant

/-- On a well-formed tree, lookup returns a value exactly when the entry belongs to the tree. -/
theorem lookup_eq_some_iff (h : IsWF t tr) {v : β} : lookup k tr = some v ↔ (k, v) ∈ tr := by
  rw [lookup_eq h, h.sorted.lookup_eq_some_iff, mem_def]

/-- On a well-formed tree, `contains` decides whether the key occurs. -/
theorem contains_iff (h : IsWF t tr) : contains k tr = true ↔ k ∈ tr.keys := by
  rw [contains_eq_isSome_lookup, Option.isSome_iff_exists, mem_keys]
  exact exists_congr fun v => lookup_eq_some_iff h

end Pure

end BPlusTree

end Cslib.DataStructure
