/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.MinMax

/-!
# Predecessor and successor queries in B+-trees

`predM` and `succM` return the entry with the greatest key strictly below the query, respectively
the least key strictly above it. Each follows the search of `lookupM` to a leaf and scans it with
`Cslib.SortedAssoc.predM`, respectively `Cslib.SortedAssoc.succM`.

The leaf that the search reaches need not hold the answer. Every key of that leaf may be at
least the query, and then the predecessor is the last entry of the leaf before it; every key may
be at most the query, and then the successor is the first entry of the leaf after it. The
operations here handle this by a sibling fallback: at the node where the descent into a child
yields nothing, they take the greatest entry of the child before it, respectively the least entry
of the child after it, with `maxM` and `minM`. In a well-formed tree that sibling is not empty,
so the fallback runs at most once, and the walk it adds visits at most one node on each level
below that node.

An implementation with chained leaves would instead step from the leaf to its neighbour. Modelling
that, by passing the neighbouring leaf down the descent and charging one visit when it is
consulted, is left as future work.

## Main definitions

* `predM`, `succM`: the queries, polymorphic.
* `pred?`, `succ?`: the pure operations.

## Main results

* `map_predM`, `map_succM`: a monad morphism commutes with the queries.
* `pred?_eq`, `succ?_eq`: on a well-formed tree, `pred?` and `succ?` are `SortedAssoc.pred?` and
  `SortedAssoc.succ?` on `toList`.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Strict predecessor. Pass the separators that are at most `k` and descend into the child
introduced by the last of them; in the leaf, scan the entries. Where the part of a node after a
separator yields nothing, return the greatest entry of the child before that separator. `visit`
fires once at each node on the path, and once at each node of the fallback walk. -/
@[expose] def predM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BPlusTree α β → m (Option (α × β))
  | .leaf entries => do
    visit
    SortedAssoc.predM le k entries
  | .node first [] => do
    visit
    predM le visit k first
  | .node first ((s, c) :: rest) => do
    if ← le s k then
      let r ← predM le visit k (.node c rest)
      if r.isSome then pure r else maxM visit first
    else
      visit
      predM le visit k first
termination_by tr => sizeOf tr

/-- Strict successor. Pass the separators that are at most `k` and descend into the child
introduced by the last of them; in the leaf, scan the entries. Where the child before a separator
yields nothing, return the least entry of the child that the separator introduces. `visit` fires
once at each node on the path, and once at each node of the fallback walk. -/
@[expose] def succM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BPlusTree α β → m (Option (α × β))
  | .leaf entries => do
    visit
    SortedAssoc.succM le k entries
  | .node first [] => do
    visit
    succM le visit k first
  | .node first ((s, c) :: rest) => do
    if ← le s k then
      succM le visit k (.node c rest)
    else
      visit
      let r ← succM le visit k first
      if r.isSome then pure r else minM visit c
termination_by tr => sizeOf tr

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the predecessor query. -/
theorem map_predM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    f (predM le visit k tr) = predM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction predM le visit k tr <;>
    simp [predM, hf.map_bind, hf.map_pure, apply_ite f, SortedAssoc.map_predM hf, map_maxM hf, *]

/-- A monad morphism commutes with the successor query. -/
theorem map_succM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    f (succM le visit k tr) = succM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction succM le visit k tr <;>
    simp [succM, hf.map_bind, hf.map_pure, apply_ite f, SortedAssoc.map_succM hf, map_minM hf, *]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BPlusTree α β} {k : α}

/-- Pure strict predecessor: the `Id` instantiation of `predM` with `visit := pure ()`. -/
def pred? (k : α) (tr : BPlusTree α β) : Option (α × β) := Id.run (predM leI (pure ()) k tr)

/-- Pure strict successor: the `Id` instantiation of `succM` with `visit := pure ()`. -/
def succ? (k : α) (tr : BPlusTree α β) : Option (α × β) := Id.run (succM leI (pure ()) k tr)

/-- `pred?` is the `Id` instantiation of `predM`. -/
theorem pred?_def (k : α) : pred? k tr = Id.run (predM leI (pure ()) k tr) := (rfl)

/-- `succ?` is the `Id` instantiation of `succM`. -/
theorem succ?_def (k : α) : succ? k tr = Id.run (succM leI (pure ()) k tr) := (rfl)

/-- The predecessor in a leaf is the scan of its entries. -/
theorem pred?_leaf (k : α) (entries : List (α × β)) :
    pred? k (.leaf entries) = Id.run (SortedAssoc.predM leI k entries) := by
  simp [pred?, predM]

/-- The predecessor in a node without separators is the predecessor in its only child. -/
@[simp] theorem pred?_node_nil (k : α) (first : BPlusTree α β) :
    pred? k (.node first []) = pred? k first := by
  simp [pred?, predM]

/-- The predecessor at a node's first separator: when it is at most the query, look after it
and fall back on the greatest entry of the child before it; otherwise descend into that child. -/
@[simp] theorem pred?_node_cons (k s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    pred? k (.node first ((s, c) :: rest)) =
      if s ≤ k then (pred? k (.node c rest)).or (max? first) else pred? k first := by
  by_cases h : s ≤ k <;>
    simp [pred?, predM, leI, h, max?_def, apply_ite Id.run, Option.or_eq_ite]

/-- The successor in a leaf is the scan of its entries. -/
theorem succ?_leaf (k : α) (entries : List (α × β)) :
    succ? k (.leaf entries) = Id.run (SortedAssoc.succM leI k entries) := by
  simp [succ?, succM]

/-- The successor in a node without separators is the successor in its only child. -/
@[simp] theorem succ?_node_nil (k : α) (first : BPlusTree α β) :
    succ? k (.node first []) = succ? k first := by
  simp [succ?, succM]

/-- The successor at a node's first separator: when it is at most the query, look after it;
otherwise descend into the child before it and fall back on the least entry of the child that the
separator introduces. -/
@[simp] theorem succ?_node_cons (k s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    succ? k (.node first ((s, c) :: rest)) =
      if s ≤ k then succ? k (.node c rest) else (succ? k first).or (min? c) := by
  by_cases h : s ≤ k <;>
    simp [succ?, succM, leI, h, min?_def, apply_ite Id.run, Option.or_eq_ite]

private theorem neighbors_eq_of (ht : 2 ≤ t) (k : α) :
    ∀ tr : BPlusTree α β, Separated tr → tr.toList.IsSortedAssoc →
      (∀ c ∈ tr.children, Occupied t c) →
      pred? k tr = SortedAssoc.pred? k tr.toList ∧
        succ? k tr = SortedAssoc.succ? k tr.toList
  | .leaf entries, _, hs, _ => by
    rw [pred?_leaf, succ?_leaf, toList_leaf]
    exact ⟨SortedAssoc.idRun_predM (by simpa using hs) k, SortedAssoc.idRun_succM k entries⟩
  | .node first [], hp, hs, ho => by
    have hf : Occupied t first := ho first (by simp)
    simpa using neighbors_eq_of ht k first hp.first (by simpa using hs)
      (fun c hc => hf.of_mem_children hc)
  | .node first ((s, c) :: rest), hp, hs, ho => by
    have hf : Occupied t first := ho first (by simp)
    have hc : Occupied t c := ho c (by simp)
    have hs' := List.isSortedAssoc_append_iff.1 (toList_node_cons ▸ hs)
    rw [pred?_node_cons, succ?_node_cons, toList_node_cons, SortedAssoc.pred?_append,
      SortedAssoc.succ?_append]
    by_cases hk : s ≤ k
    · obtain ⟨hpred, hsucc⟩ :=
        neighbors_eq_of ht k (.node c rest) hp.tail hs'.2.1 (fun d hd => ho d (.tail _ hd))
      have hlt : ∀ p ∈ first.toList, p.1 < k := fun p hp' =>
        lt_of_lt_of_le (hp.lt_of_mem_first (e := (s, c)) List.mem_cons_self hp') hk
      simp only [hk, ↓reduceIte, hpred, hsucc]
      constructor
      · rw [hf.max?_eq ht, SortedAssoc.pred?_def (l := first.toList),
          List.filter_eq_self.2 fun p hp' => by simpa using hlt p hp']
      · rw [SortedAssoc.succ?_eq_none_iff.2 (fun p hp' => (hlt p hp').le), Option.none_or]
    · obtain ⟨hpred, hsucc⟩ :=
        neighbors_eq_of ht k first hp.first hs'.1 (fun d hd => hf.of_mem_children hd)
      have hgt : ∀ q ∈ (BPlusTree.node c rest).toList, k < q.1 := fun q hq =>
        lt_of_lt_of_le (lt_of_not_ge hk) (hp.le_of_mem_tail hs (hc.size_pos ht) hq)
      simp only [hk, ↓reduceIte, hpred, hsucc]
      constructor
      · rw [SortedAssoc.pred?_eq_none_iff.2 (fun q hq => (hgt q hq).le), Option.none_or]
      · rw [hc.min?_eq ht, SortedAssoc.succ?_def (l := (BPlusTree.node c rest).toList),
          List.filter_eq_self.2 fun q hq => by simpa using hgt q hq, toList_node,
          List.head?_append_of_ne_nil _ (hc.toList_ne_nil ht)]
termination_by tr => sizeOf tr

/-- Model equation of the predecessor on well-formed trees. -/
theorem pred?_eq (h : IsWF t tr) (k : α) : pred? k tr = SortedAssoc.pred? k tr.toList :=
  (neighbors_eq_of h.two_le k tr h.separated h.sorted h.occupied_of_mem_children).1

/-- Model equation of the successor on well-formed trees. -/
theorem succ?_eq (h : IsWF t tr) (k : α) : succ? k tr = SortedAssoc.succ? k tr.toList :=
  (neighbors_eq_of h.two_le k tr h.separated h.sorted h.occupied_of_mem_children).2

end Pure

end BPlusTree

end Cslib.DataStructure
