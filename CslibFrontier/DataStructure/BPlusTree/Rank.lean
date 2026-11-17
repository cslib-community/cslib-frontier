/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Lookup

/-!
# Rank queries in B+-trees

`rankM` counts the entries with key strictly below the query by one descent, following the
search of `lookupM`. Each separator passed contributes the size of the child before it, and the
leaf at the end of the path contributes the rank of the query in its entry list, by the scan
`Cslib.SortedAssoc.rankM`. The sizes of the children passed are pure subtree sizes: computing
them is uncharged client computation, as in the classic tree. `visit` fires once at each node on
the path, the leaf included.

## Main definitions

* `rankM`, `rank`: the number of entries with key strictly below the query.

## Main results

* `map_rankM`: a monad morphism commutes with the query.
* `rank_eq`: on a well-formed tree, `rank` is `SortedAssoc.rank` on `toList`.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Rank by a single descent. Pass the separators that are at most `k`, adding the pure size of
the child before each; descend into the child introduced by the last of them; in the leaf, scan
the entries. `visit` fires once at each node on the path. -/
@[expose] def rankM (le : α → α → m Bool) (visit : m Unit) (k : α) : BPlusTree α β → m ℕ
  | .leaf entries => do
    visit
    SortedAssoc.rankM le k entries
  | .node first [] => do
    visit
    rankM le visit k first
  | .node first ((s, c) :: rest) => do
    if ← le s k then
      return first.size + (← rankM le visit k (.node c rest))
    else
      visit
      rankM le visit k first
termination_by tr => sizeOf tr

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the rank query. -/
theorem map_rankM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    f (rankM le visit k tr) = rankM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction rankM le visit k tr <;>
    simp [rankM, hf.map_bind, hf.map_pure, apply_ite f, SortedAssoc.map_rankM hf, *]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BPlusTree α β} {k : α}

/-- Pure rank: the `Id` instantiation of `rankM` with `visit := pure ()`. -/
def rank (k : α) (tr : BPlusTree α β) : ℕ := Id.run (rankM leI (pure ()) k tr)

/-- `rank` is the `Id` instantiation of `rankM`. -/
theorem rank_def (k : α) : rank k tr = Id.run (rankM leI (pure ()) k tr) := (rfl)

/-- Rank in a leaf is the scan of its entries. -/
theorem rank_leaf (k : α) (entries : List (α × β)) :
    rank k (.leaf entries) = Id.run (SortedAssoc.rankM leI k entries) := by
  simp [rank, rankM]

/-- Rank in a node without separators is rank in its only child. -/
@[simp] theorem rank_node_nil (k : α) (first : BPlusTree α β) :
    rank k (.node first []) = rank k first := by
  simp [rank, rankM]

/-- Rank at a node's first separator: when it is at most the query, count the child before it
and pass it; otherwise descend into that child. -/
@[simp] theorem rank_node_cons (k s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    rank k (.node first ((s, c) :: rest)) =
      if s ≤ k then first.size + rank k (.node c rest) else rank k first := by
  by_cases h : s ≤ k <;> simp [rank, rankM, leI, h]

/-- Rank against the model, under what the search uses: the separator convention, sorted entries,
and occupied children at `2 ≤ t`. -/
private theorem rank_eq_of (ht : 2 ≤ t) (k : α) :
    ∀ tr : BPlusTree α β, Separated tr → tr.toList.IsSortedAssoc →
      (∀ c ∈ tr.children, Occupied t c) → rank k tr = SortedAssoc.rank k tr.toList
  | .leaf entries, _, hs, _ => by
    rw [rank_leaf, toList_leaf]
    exact SortedAssoc.idRun_rankM (by simpa using hs) k
  | .node first [], hp, hs, ho => by
    have hf : Occupied t first := ho first (by simp)
    rw [rank_node_nil,
      rank_eq_of ht k first hp.first (by simpa using hs) fun c hc => hf.of_mem_children hc]
    simp
  | .node first ((s, c) :: rest), hp, hs, ho => by
    have hf : Occupied t first := ho first (by simp)
    have hc : Occupied t c := ho c (by simp)
    have hs' := hs
    rw [toList_node_cons, List.isSortedAssoc_append_iff] at hs'
    rw [rank_node_cons, toList_node_cons, SortedAssoc.rank_append]
    by_cases hk : s ≤ k
    · simp only [hk, ↓reduceIte]
      rw [SortedAssoc.rank_eq_length_iff.2 fun p hp' =>
        lt_of_lt_of_le (hp.lt_of_mem_first (e := (s, c)) List.mem_cons_self hp') hk,
        length_toList]
      congr 1
      exact rank_eq_of ht k (.node c rest) hp.tail hs'.2.1 fun d hd => ho d (by
        simp only [children_node, List.map_cons, List.mem_cons] at hd ⊢
        exact Or.inr hd)
    · simp only [hk, ↓reduceIte]
      rw [SortedAssoc.rank_eq_zero_iff.2 fun q hq =>
        (lt_of_lt_of_le (lt_of_not_ge hk) (hp.le_of_mem_tail hs (hc.size_pos ht) hq)).le,
        Nat.add_zero]
      exact rank_eq_of ht k first hp.first hs'.1 fun d hd => hf.of_mem_children hd
termination_by tr => sizeOf tr

/-- Model equation of rank on well-formed trees. -/
theorem rank_eq (h : IsWF t tr) (k : α) : rank k tr = SortedAssoc.rank k tr.toList :=
  rank_eq_of h.two_le k tr h.separated h.sorted h.occupied_of_mem_children

end Pure

end BPlusTree

end Cslib.DataStructure
