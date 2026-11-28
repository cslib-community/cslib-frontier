/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.BinarySearch
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Sum.Order
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
positions `0, …, n` of `xs` defines `n + 1` linear orders on `α`. Every one of
these `n + 1` linear orders keeps `xs` strictly increasing while giving `k` a distinct rank in
`{0, …, n}`. Applying `FreeM.exists_countQueries_ge_clog` to the binary-response query type
`LEQuery α` shows that at least one of those `n + 1` oracles forces `⌈log₂(n + 1)⌉` comparisons
(`rank_lowerBound_infinite`). Bulk-loading `n` distinct keys via `ofSortedList` lifts this
per-tree bound to `Cslib.Query.LowerBound` both over arbitrary `BTree α β × α` inputs
(`IsRank.lowerBound_infinite`, requiring no ambient order on `α`) and over well-formed trees
`WFInput α β t` of minimum degree `t ≥ 2` (`IsRank.lowerBound_wfInput_infinite`, matching
`rankBinQ_upperBound_size` so `LowerBound.le_upperBound` applies directly). The trees come from
`exists_isWF_toList_map_snd_eq`, which bulk-loads any prescribed list of values under distinct
increasing keys; the form over arbitrary inputs follows from the well-formed one under any linear
order on `α`.

This module covers comparison-based `rank` in `FreeM (LEQuery α)` (not machine-instruction lower
bounds). The companion comparison lower bound for `lookup`, in
`CslibFrontier.DataStructure.BTree.Comparisons.LookupLowerBound`, is proved for trees with
distinct values (its `Cslib.Query.LowerBound` forms assume an infinite value type); sets, whose
values are not distinct, are not covered and remain open under `#3674`. It needs oracles with
ties, because under linear orders alone equality is outside the oracle and a lookup program can
be correct without asking.

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

@[instance_reducible]
private noncomputable def prefixOrder {L : List α} (h : L.Nodup) : LinearOrder α :=
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  LinearOrder.lift' (fun a => toLex (listPrefix h a)) (listPrefix_injective h)

private theorem pairwise_prefixOrder {L : List α} (h : L.Nodup) :
    letI := prefixOrder h
    L.Pairwise (· < ·) := by
  let _ := IsWellOrder.linearOrder (α := α) WellOrderingRel
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  change toLex (listPrefix h L[i]) < toLex (listPrefix h L[j])
  simpa only [listPrefix_embedded h ⟨i, hi⟩, listPrefix_embedded h ⟨j, hj⟩,
    Sum.Lex.inl_lt_inl_iff, Fin.mk_lt_mk] using hij

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
  let beforeKeys (i : Fin (tree.size + 1)) := xs.take i
  let afterKeys (i : Fin (tree.size + 1)) := xs.drop i
  have splitKeys (i : Fin (tree.size + 1)) : beforeKeys i ++ afterKeys i = xs :=
    List.take_append_drop i xs
  have hnodup (i : Fin (tree.size + 1)) : (beforeKeys i ++ k :: afterKeys i).Nodup :=
    List.perm_middle.nodup_iff.mpr (by
      rw [splitKeys i, List.nodup_cons]
      exact ⟨hk, h_nodup⟩)
  let progOracles (i : Fin (tree.size + 1)) := @orderOracle α (prefixOrder (hnodup i))
  have eval_eq (i : Fin (tree.size + 1)) : (rankProg k tree).eval (progOracles i) = i := by
    let _ := prefixOrder (hnodup i)
    have hsorted := pairwise_prefixOrder (hnodup i)
    have hxsSorted : xs.Pairwise (· < ·) := by
      rw [← splitKeys i]
      exact hsorted.sublist ((List.sublist_cons_self k (afterKeys i)).append_left (beforeKeys i))
    rw [h_corr.correct k tree (progOracles i) (· ≤ ·) (fun _ _ => rfl)
      (hxsSorted.imp fun h => lt_iff_le_not_ge.mp h)]
    simp only [← lt_iff_le_not_ge, ← List.countP_eq_length_filter]
    change tree.toList.countP ((fun x : α => decide (x < k)) ∘ Prod.fst) = (i : ℕ)
    rw [← List.countP_map, List.countP_eq_length_filter]
    change (xs.filter (· < k)).length = (i : ℕ)
    rw [← splitKeys i, List.filter_append]
    obtain ⟨-, hAfter, hBefore⟩ := List.pairwise_append.mp hsorted
    have hpre : (beforeKeys i).filter (· < k) = beforeKeys i :=
      List.filter_eq_self.mpr fun x hx => decide_eq_true (hBefore x hx k (List.mem_cons_self ..))
    have hsuf : (afterKeys i).filter (· < k) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx => by
        simpa only [decide_eq_true_eq] using
          ((List.pairwise_cons.mp hAfter).1 x hx).not_gt
    simp [hpre, hsuf, beforeKeys, List.length_take_of_le (show (i : ℕ) ≤ xs.length by omega)]
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2 LEQuery.cardResponse_le_two
    (rankProg k tree) progOracles (by omega)
    fun i j h => Fin.ext ((eval_eq i).symm.trans (h.trans (eval_eq j)))
  exact ⟨k, progOracles i, hi⟩

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
  obtain ⟨tree, hwf, hsize, hnodup, -⟩ :=
    exists_isWF_toList_map_snd_eq (α := α) ht (List.replicate n (Classical.arbitrary β))
  rw [List.length_replicate] at hsize
  obtain ⟨k, oracle, hi⟩ := rank_lowerBound_infinite h_corr tree hnodup
  exact ⟨⟨(tree, k), hwf⟩, hsize.le, oracle, hsize ▸ hi⟩

/-- **Comparison lower bound for B-tree rank (`Cslib.Query.LowerBound`).** Any `IsRank` program on
an infinite key type `α` and nonempty value type `β` has worst-case comparison query complexity at
least `⌈log₂(n + 1)⌉` on trees of size at most `n`. -/
theorem IsRank.lowerBound_infinite [Infinite α] [Nonempty β]
    {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ} (h_corr : IsRank rankProg) :
    LowerBound (fun p : BTree α β × α => rankProg p.2 p.1) (fun p => p.1.size)
      (fun n => Nat.clog 2 (n + 1)) :=
  -- Forget well-formedness under some linear order on `α`.
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  fun n =>
    let ⟨x, hx, oracle, hi⟩ := h_corr.lowerBound_wfInput_infinite (t := 2) le_rfl n
    ⟨x.val, hx, oracle, hi⟩

end LowerBound

end Cslib.DataStructure.BTree
