/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.BinarySearch
import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Comparison lower bound for B-tree rank search

Information-theoretic `⌈log₂(n + 1)⌉` comparison lower bound for rank queries on B-trees over an
infinite key type, in CSLib's `FreeM (LEQuery α)` query-complexity framework ([Knuth1998],
Section 6.2.1).

A comparison-based rank program can achieve logarithmic query complexity only when the input
tree's keys are strictly increasing under the oracle's linear order: a search that descends into
a single child per level misses out-of-order keys in sibling subtrees, and ranking an arbitrary
unsorted list of `n` keys requires `n` comparisons. Accordingly, `IsRank` requires that under any
oracle implementing a linear order `r` for which `(tree.toList.map Prod.fst)` is strictly
`r`-increasing, the program returns the number of entries strictly `r`-below the query key `k`.
Both B-tree rank implementations—`rankQ` (linear in-node scan) and `rankBinQ` (binary in-node
search)—satisfy `IsRank` (`rankQ_isRank`, `rankBinQ_isRank`).

Given any tree `tree` of size `n` with duplicate-free keys `xs = tree.toList.map Prod.fst` and a
fresh key `k ∉ xs` (obtained from `[Infinite α]`), inserting `k` at each of the `n + 1` gap
positions `0, …, n` of `xs` defines `n + 1` linear orders `PrefixOrder` on `α`. Every one of
these `n + 1` linear orders keeps `xs` strictly increasing while giving `k` a distinct rank in
`{0, …, n}`. Applying `FreeM.exists_countQueries_ge_clog` to the binary-response query type
`LEQuery α` shows that at least one of those `n + 1` oracles forces `⌈log₂(n + 1)⌉` comparisons
(`rank_lowerBound_infinite`). Bulk-loading `n` distinct keys via `ofSortedList` lifts this
per-tree bound to `Cslib.Query.LowerBound` both over arbitrary `BTree α β × α` inputs
(`IsRank.lowerBound_infinite`, requiring no ambient order on `α`) and over well-formed trees
`WFInput α β t` of minimum degree `t ≥ 2` (`IsRank.lowerBound_wfInput_infinite`, matching
`rankBinQ_upperBound_size` so `LowerBound.le_upperBound` applies directly).

This module covers comparison-based `rank` in `FreeM (LEQuery α)` (not machine-instruction lower
bounds); the companion comparison lower bound for `lookup` (which requires total preorders with
ties in `FreeM (LEQuery α)`) remains open under `#3674`.

## Main definitions

* `Cslib.DataStructure.BTree.IsRank`: correctness predicate for comparison-based B-tree rank
  programs against linear-order oracles on trees whose keys are strictly increasing.

## Main results

* `Cslib.DataStructure.BTree.rankQ_isRank`, `Cslib.DataStructure.BTree.rankBinQ_isRank`: linear
  and binary in-node B-tree rank queries satisfy `IsRank`.
* `Cslib.DataStructure.BTree.rank_lowerBound_infinite`: on any tree of size `n` with distinct
  keys over an infinite key type, any `IsRank` program makes at least `⌈log₂(n + 1)⌉`
  comparisons on some query key and comparison oracle.
* `Cslib.DataStructure.BTree.IsRank.lowerBound_infinite`: `Cslib.Query.LowerBound` of
  `⌈log₂(n + 1)⌉` over `BTree α β × α` with size `p.1.size`.
* `Cslib.DataStructure.BTree.IsRank.lowerBound_wfInput_infinite`: `Cslib.Query.LowerBound` of
  `⌈log₂(n + 1)⌉` over well-formed inputs `WFInput α β t` (`2 ≤ t`) with size `p.val.1.size`.

## References

* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*][Knuth1998],
  Section 6.2.1.
-/

public section

namespace Cslib.DataStructure.BTree

open Cslib (FreeM)
open Cslib.Query (LEQuery LowerBound)

section Specification

variable {α β : Type}

/-- `IsRank rankProg` asserts that against every oracle implementing a linear order `r` under
which the keys of `tree.toList` are strictly increasing, `rankProg k tree` evaluates to the
number of entries of `tree.toList` whose key is strictly `r`-below `k`. -/
structure IsRank (rankProg : α → BTree α β → FreeM (LEQuery α) ℕ) : Prop where
  /-- Under a linear-order oracle that strictly orders `tree.toList`'s keys, `rankProg k tree`
  counts the entries strictly below `k`. -/
  correct : ∀ (k : α) (tree : BTree α β) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r],
    (∀ a b, oracle (.le a b) = decide (r a b)) →
    (tree.toList.map Prod.fst).Pairwise (fun a b => r a b ∧ ¬ r b a) →
    (rankProg k tree).eval oracle =
      (tree.toList.filter fun x => r x.1 k ∧ ¬ r k x.1).length

/-- Package a decidable relation satisfying `IsLinearOrder α r` as a `LinearOrder α` whose
`(· ≤ ·)` and `(· < ·)` are definitionally `r` and `fun a b => r a b ∧ ¬ r b a`. -/
@[instance_reducible]
private def linearOrderOfRel (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r] :
    LinearOrder α where
  le := r
  lt a b := r a b ∧ ¬ r b a
  le_refl a := (Std.Total.total (r := r) a a).elim id id
  le_trans _ _ _ := IsTrans.trans _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ := Std.Antisymm.antisymm _ _
  le_total := Std.Total.total (r := r)
  toDecidableLE := inferInstance

private theorem oracle_eq_orderOracle (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) :
    let _ := linearOrderOfRel r
    (fun {ι} => oracle (ι := ι)) = fun {ι} => orderOracle (ι := ι) := by
  let _ := linearOrderOfRel r
  funext ι q
  cases q
  exact horacle _ _

private theorem isRank_of_eval_eq_rank {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ}
    (heval : ∀ [LinearOrder α] (k : α) (tree : BTree α β),
      tree.toList.IsSortedAssoc → (rankProg k tree).eval orderOracle = rank k tree) :
    IsRank rankProg where
  correct k tree oracle r _ _ horacle hsorted := by
    let _ := linearOrderOfRel r
    have horc := oracle_eq_orderOracle r oracle horacle
    have hs : tree.toList.IsSortedAssoc := List.isSortedAssoc_iff_pairwise.mpr hsorted
    rw [horc, heval k tree hs, rank_eq_of_isSortedAssoc hs, Cslib.SortedAssoc.rank_def]
    congr 1

/-- `rankQ` (linear in-node search) is a correct comparison-based rank program. -/
theorem rankQ_isRank : IsRank (rankQ (α := α) (β := β)) :=
  isRank_of_eval_eq_rank fun k tree _ => eval_rankQ (tr := tree) k

/-- `rankBinQ` (binary in-node search) is a correct comparison-based rank program. -/
theorem rankBinQ_isRank : IsRank (rankBinQ (α := α) (β := β)) :=
  isRank_of_eval_eq_rank fun k tree hs =>
    (eval_rankBinQ (tr := tree) k).trans (rankBin_eq_rank hs k)

end Specification

section LowerBound

variable {α β : Type}

private def listEmbedding {L : List α} (h : L.Nodup) : Fin L.length ↪ α :=
  ⟨fun i => L.get i, fun _ _ hij => (List.Nodup.get_inj_iff h).mp hij⟩

private noncomputable def listPrefix {L : List α} (h : L.Nodup) : α → Fin L.length ⊕ α :=
  Function.extend (listEmbedding h) .inl .inr

@[simp]
private theorem listPrefix_embedded {L : List α} (h : L.Nodup) (i : Fin L.length) :
    listPrefix h L[i.val] = .inl i :=
  (listEmbedding h).injective.extend_apply _ _ _

private theorem listPrefix_injective {L : List α} (h : L.Nodup) :
    Function.Injective (listPrefix h) :=
  (listEmbedding h).injective.extend_of_disjoint Sum.inl_injective Sum.inr_injective
    Set.isCompl_range_inl_range_inr.disjoint

private noncomputable def PrefixOrder {L : List α} (h : L.Nodup) : α → α → Prop :=
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  InvImage (Sum.Lex (· ≤ · : Fin L.length → Fin L.length → Prop) (· ≤ ·)) (listPrefix h)

private noncomputable instance {L : List α} (h : L.Nodup) :
    DecidableRel (PrefixOrder h) := Classical.decRel _

private instance {L : List α} (h : L.Nodup) :
    IsTrans α (PrefixOrder h) := by
  unfold PrefixOrder; infer_instance

private instance {L : List α} (h : L.Nodup) :
    Std.Total (PrefixOrder h) := by
  unfold PrefixOrder; infer_instance

private instance {L : List α} (h : L.Nodup) :
    Std.Antisymm (PrefixOrder h) := by
  let _ := IsWellOrder.linearOrder (α := α) WellOrderingRel
  have : Std.Antisymm (Sum.Lex (· ≤ · : Fin L.length → Fin L.length → Prop)
      (· ≤ · : α → α → Prop)) :=
    inferInstance
  exact (listPrefix_injective h).antisymm_onFun _

private instance {L : List α} (h : L.Nodup) :
    IsLinearOrder α (PrefixOrder h) where

private theorem prefixOrder_get_iff {L : List α} (h : L.Nodup) (a b : Fin L.length) :
    PrefixOrder h L[a.val] L[b.val] ↔ a ≤ b := by
  simp only [PrefixOrder, InvImage, listPrefix_embedded, Sum.lex_inl_inl]

private theorem prefixOrder_lt_getElem_iff {L : List α} (h : L.Nodup) (a b : ℕ)
    (ha : a < L.length) (hb : b < L.length) :
    (PrefixOrder h L[a] L[b] ∧ ¬ PrefixOrder h L[b] L[a]) ↔ a < b := by
  have h1 := prefixOrder_get_iff h ⟨a, ha⟩ ⟨b, hb⟩
  have h2 := prefixOrder_get_iff h ⟨b, hb⟩ ⟨a, ha⟩
  simp only [Fin.mk_le_mk] at h1 h2
  rw [h1, h2]
  omega

private theorem pairwise_prefixOrder_self {L : List α} (h : L.Nodup) :
    L.Pairwise (fun a b => PrefixOrder h a b ∧ ¬ PrefixOrder h b a) :=
  List.pairwise_iff_getElem.mpr fun a b ha hb hab =>
    (prefixOrder_lt_getElem_iff h a b ha hb).mpr hab

private theorem sublist_insertIdx {xs : List α} (k : α) :
    ∀ {i : ℕ}, i ≤ xs.length → xs.Sublist (xs.insertIdx i k) := by
  induction xs with
  | nil => rintro _ hi; simp [Nat.le_zero.mp hi]
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => exact List.sublist_cons_self k (x :: xs)
    | succ i => exact (ih (Nat.le_of_succ_le_succ hi)).cons_cons x

private theorem length_filter_prefixOrder {xs : List α} {k : α} (h_nodup : xs.Nodup) (hk : k ∉ xs)
    (i : ℕ) (hi : i ≤ xs.length) :
    let L_i := xs.insertIdx i k
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    (xs.filter fun x => PrefixOrder h_nodup_i x k ∧ ¬ PrefixOrder h_nodup_i k x).length = i := by
  intro L_i h_nodup_i
  let p : α → Bool := fun x => decide (PrefixOrder h_nodup_i x k ∧ ¬ PrefixOrder h_nodup_i k x)
  change (xs.filter fun x => p x).length = i
  have hL_len : L_i.length = xs.length + 1 := List.length_insertIdx_of_le_length hi k
  have hi_lt : i < L_i.length := by omega
  have hLi : L_i[i] = k := List.getElem_insertIdx_self hi_lt
  have h_take : (xs.take i).filter p = xs.take i := by
    rw [List.filter_eq_self]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [List.length_take_of_le hi] at hj
    have hj_lt_L : j < L_i.length := by omega
    have hLj : L_i[j] = (xs.take i)[j] := by rw [List.getElem_take, List.getElem_insertIdx_of_lt hj]
    simp only [p, decide_eq_true_eq, ← hLj, ← hLi]
    exact (prefixOrder_lt_getElem_iff h_nodup_i j i hj_lt_L hi_lt).mpr hj
  have h_drop : (xs.drop i).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [List.length_drop] at hj
    have hj_lt_L : i + j + 1 < L_i.length := by omega
    have hLj : L_i[i + j + 1] = (xs.drop i)[j] := by
      rw [List.getElem_drop, List.getElem_insertIdx_of_gt (by omega)]
      rfl
    simp only [p, decide_eq_true_eq, ← hLj, ← hLi,
      prefixOrder_lt_getElem_iff h_nodup_i (i + j + 1) i hj_lt_L hi_lt]
    omega
  have h_split : xs.filter p = (xs.take i).filter p ++ (xs.drop i).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [h_split, h_take, h_drop, List.append_nil, List.length_take_of_le hi]

/-- **Per-tree comparison lower bound for rank.** On any B-tree `tree` with distinct keys over an
infinite key type `α`, any `IsRank` program makes at least `⌈log₂(tree.size + 1)⌉` comparisons
for some query key `k` and comparison oracle. -/
theorem rank_lowerBound_infinite [Infinite α]
    {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ} (h_corr : IsRank rankProg)
    (tree : BTree α β) (h_nodup : (tree.toList.map Prod.fst).Nodup) :
    ∃ (k : α) (oracle : {ι : Type} → LEQuery α ι → ι),
      Nat.clog 2 (tree.size + 1) ≤ (rankProg k tree).countQueries oracle := by
  let xs := tree.toList.map Prod.fst
  have hxs : xs.length = tree.size := by simp [xs, ← length_toList]
  obtain ⟨k, hk⟩ : ∃ k : α, k ∉ xs := by
    classical
    simpa using Infinite.exists_notMem_finset xs.toFinset
  let n := tree.size
  let progOracles : Fin (n + 1) → ({ι : Type} → LEQuery α ι → ι) := fun i =>
    let L_i := xs.insertIdx (i : ℕ) k
    have hi_le : (i : ℕ) ≤ xs.length := by omega
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi_le).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    LEQuery.oracleOf fun a b => decide (PrefixOrder h_nodup_i a b)
  have eval_eq (i : Fin (n + 1)) : (rankProg k tree).eval (progOracles i) = i := by
    let L_i := xs.insertIdx (i : ℕ) k
    have hi_le : (i : ℕ) ≤ xs.length := by omega
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi_le).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    have h_sorted_i : xs.Pairwise (fun a b => PrefixOrder h_nodup_i a b ∧
        ¬ PrefixOrder h_nodup_i b a) :=
      (pairwise_prefixOrder_self h_nodup_i).sublist (sublist_insertIdx k hi_le)
    have h_corr_i := h_corr.correct k tree (progOracles i) (PrefixOrder h_nodup_i)
      (fun a b => by simp [progOracles]) h_sorted_i
    rw [h_corr_i]
    have h_filter :
        (tree.toList.filter fun x => PrefixOrder h_nodup_i x.1 k ∧
          ¬ PrefixOrder h_nodup_i k x.1).length =
          (xs.filter fun y => PrefixOrder h_nodup_i y k ∧ ¬ PrefixOrder h_nodup_i k y).length := by
      simp [xs, List.filter_map, Function.comp_def]
    exact h_filter.trans (length_filter_prefixOrder h_nodup hk i hi_le)
  have h_inj : Function.Injective (fun i => (rankProg k tree).eval (progOracles i)) :=
    fun i j h => Fin.ext ((eval_eq i).symm.trans (h.trans (eval_eq j)))
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2 LEQuery.cardResponse_le_two
    (rankProg k tree) progOracles (by omega) h_inj
  exact ⟨k, progOracles i, hi⟩

/-- **Comparison lower bound for B-tree rank (`Cslib.Query.LowerBound`).** Any `IsRank` program on
an infinite key type `α` and nonempty value type `β` has worst-case comparison query complexity at
least `⌈log₂(n + 1)⌉` on trees of size at most `n`. -/
theorem IsRank.lowerBound_infinite [Infinite α] [Nonempty β]
    {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ} (h_corr : IsRank rankProg) :
    LowerBound (fun p : BTree α β × α => rankProg p.2 p.1) (fun p => p.1.size)
      (fun n => Nat.clog 2 (n + 1)) := by
  intro n
  let v : β := Classical.arbitrary β
  let l : List (α × β) := (List.range n).map fun i => (Infinite.natEmbedding α i, v)
  let tree : BTree α β := ofSortedList 2 l
  have hmap : tree.toList.map Prod.fst = (List.range n).map (Infinite.natEmbedding α) := by
    simp [tree, l, toList_ofSortedList, Function.comp_def]
  have hnodup : (tree.toList.map Prod.fst).Nodup :=
    hmap ▸ List.nodup_range.map (Infinite.natEmbedding α).injective
  have hsize : tree.size = n := by simp [← length_toList, tree, l]
  obtain ⟨k, oracle, hi⟩ := rank_lowerBound_infinite h_corr tree hnodup
  rw [hsize] at hi
  exact ⟨(tree, k), hsize.le, oracle, hi⟩

/-- **Comparison lower bound for B-tree rank over well-formed inputs (`WFInput`).** When `2 ≤ t`,
any `IsRank` program restricted to well-formed B-trees of minimum degree `t` (`WFInput α β t`,
matching `rankBinQ_upperBound_size`) still has worst-case comparison query complexity at least
`⌈log₂(n + 1)⌉` at every input size `n`. -/
theorem IsRank.lowerBound_wfInput_infinite [LinearOrder α] [Infinite α] [Nonempty β]
    {t : ℕ} (ht : 2 ≤ t) {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ}
    (h_corr : IsRank rankProg) :
    LowerBound (fun p : WFInput α β t => rankProg p.val.2 p.val.1) (fun p => p.val.1.size)
      (fun n => Nat.clog 2 (n + 1)) := by
  intro n
  let v : β := Classical.arbitrary β
  let rawKeys : List α := (List.range n).map (Infinite.natEmbedding α)
  let sortedKeys : List α := rawKeys.mergeSort
  have hnodup_sorted : sortedKeys.Nodup :=
    (List.mergeSort_perm rawKeys _).nodup_iff.mpr
      (List.Nodup.map (Infinite.natEmbedding α).injective List.nodup_range)
  have hle_sorted : sortedKeys.Pairwise (· ≤ ·) := by
    simpa using List.pairwise_mergeSort' (· ≤ ·) rawKeys
  have hlt_sorted : sortedKeys.Pairwise (· < ·) :=
    (hle_sorted.and hnodup_sorted).imp fun h => h.1.lt_of_ne h.2
  let l : List (α × β) := sortedKeys.map fun x => (x, v)
  have hl_map : l.map Prod.fst = sortedKeys := by simp [l, Function.comp_def]
  have hl_sorted : l.IsSortedAssoc := by rwa [List.isSortedAssoc_iff_pairwise, hl_map]
  let tree : BTree α β := ofSortedList t l
  have hwf : IsWF t tree := isWF_ofSortedList ht hl_sorted
  have hnodup_tree : (tree.toList.map Prod.fst).Nodup := by rwa [toList_ofSortedList, hl_map]
  have hsize : tree.size = n := by simp [← length_toList, tree, l, sortedKeys, rawKeys]
  obtain ⟨k, oracle, hi⟩ := rank_lowerBound_infinite h_corr tree hnodup_tree
  rw [hsize] at hi
  exact ⟨⟨(tree, k), hwf⟩, hsize.le, oracle, hi⟩

end LowerBound

end Cslib.DataStructure.BTree
