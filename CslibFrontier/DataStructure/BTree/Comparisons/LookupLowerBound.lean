/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.KeyOracle
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Order

/-!
# Comparison lower bound for B-tree lookup

Information-theoretic `⌈log₂(n + 1)⌉` comparison lower bound for lookup on B-trees with distinct
values over an infinite key type, in CSLib's `FreeM (LEQuery α)` query-complexity framework; sets
(`β = Unit`), whose values are not distinct, are not covered (`#3674`). The argument is an
adaptation of the rank lower bound of
`CslibFrontier.DataStructure.BTree.Comparisons.LowerBound`: information-theoretic counting over
`n + 1` oracles that force `n + 1` distinct outcomes. The formulation through oracles with ties
is original to this library.

`IsLookup prog` requires that, under the comparison oracle `LEQuery.keyOracle key` of any key
function `key : α → W` into a linear order under which the keys of `tree.toList` are strictly
increasing, `prog k tree` returns the value stored under the key that `key` identifies with
`k`, or `none`. Both B-tree lookup implementations, `lookupQ` (linear in-node scan) and
`lookupBinQ` (binary in-node search), satisfy `IsLookup` (`lookupQ_isLookup`,
`lookupBinQ_isLookup`).

The statement deviates in two ways from the plain claim that lookup needs `⌈log₂(n + 1)⌉`
comparisons, stated in the shape of the rank bound.

1. **Oracles with ties instead of linear orders.** Under a linear order two keys are equivalent
   only when they are equal, so a correctness predicate quantified over linear-order oracles
   leaves equality outside the oracle: for `α = ℕ` the program
   `fun k tree => pure (tree.toList.lookup k)` is correct under every linear-order oracle and asks
   nothing, and no lower bound holds. A lower bound needs equality to be the oracle's business,
   so the oracle must be able to answer both `k ≤ x` and `x ≤ k` for `k ≠ x`. `IsLookup`
   therefore quantifies over the key oracles `LEQuery.keyOracle key`, which have ties: every
   total preorder on `α` is the comparison of such a key function (its quotient by ties).
2. **Distinct values.** The `n + 1` distinct answers that force the bound are the `n` stored
   values and absence, so the per-tree bound `lookup_lowerBound_infinite` assumes that the values
   of the tree are distinct, and the `Cslib.Query.LowerBound` forms assume `[Infinite β]`. Sets
   (`β = Unit`) are therefore not covered; the bound for sets is open under `#3674`, since it needs
   a counting argument over distinct comparison transcripts rather than distinct results.

Given a tree of size `n` with distinct keys `xs` and distinct values, and a fresh key `k ∉ xs`,
the `n + 1` key functions that send `xs[j]` to `2 * j` and `k` either to `2 * i` for some `i < n`
or to the odd number `2 * n + 1` keep `xs` strictly increasing. Under the `i`-th one the lookup of
`k` must return the `i`-th value, and under the last one `none`. Applying
`FreeM.exists_countQueries_ge_clog` to the binary-response query type `LEQuery α` shows that one
of these oracles forces `⌈log₂(n + 1)⌉` comparisons (`lookup_lowerBound_infinite`). Bulk-loading
`n` distinct keys with `n` distinct values via `exists_isWF_toList_map_snd_eq` lifts this to
`Cslib.Query.LowerBound` over arbitrary inputs `BTree α β × α` (`IsLookup.lowerBound_infinite`)
and over well-formed trees `WFInput α β t` of minimum degree `t ≥ 2`
(`IsLookup.lowerBound_wfInput_infinite`).

This module covers comparisons in `FreeM (LEQuery α)`, not machine-instruction lower bounds.

## Main definitions

* `Cslib.DataStructure.BTree.IsLookup`: correctness predicate for comparison-based B-tree lookup
  programs against the comparison oracles of key functions into linear orders.

## Main results

* `Cslib.DataStructure.BTree.lookupQ_isLookup`, `Cslib.DataStructure.BTree.lookupBinQ_isLookup`:
  linear and binary in-node B-tree lookup satisfy `IsLookup`.
* `Cslib.DataStructure.BTree.lookup_lowerBound_infinite`: on any tree of size `n` with distinct
  keys and distinct values over an infinite key type, any `IsLookup` program makes at least
  `⌈log₂(n + 1)⌉` comparisons on some query key and comparison oracle.
* `Cslib.DataStructure.BTree.IsLookup.lowerBound_infinite`: for `[Infinite α] [Infinite β]`,
  `Cslib.Query.LowerBound` of `⌈log₂(n + 1)⌉` over `BTree α β × α` with size `p.1.size`.
* `Cslib.DataStructure.BTree.IsLookup.lowerBound_wfInput_infinite`: for
  `[Infinite α] [Infinite β]`, `Cslib.Query.LowerBound` of `⌈log₂(n + 1)⌉` over well-formed inputs
  `WFInput α β t` (`2 ≤ t`) with size `p.val.1.size`.
-/

public section

namespace Cslib.DataStructure.BTree

open Cslib (FreeM)
open Cslib.Query (LEQuery LowerBound)

variable {α β : Type}

section Specification

/-- `IsLookup prog` asserts that against the comparison oracle `LEQuery.keyOracle key` of every key
function `key : α → W` into a linear order under which the keys of `tree.toList` are strictly
increasing, `prog k tree` evaluates to the lookup of `key k` in the entries of `tree` with keys
mapped by `key`: the value of the entry whose key `key` identifies with `k`, or `none`.

The key oracles have ties: every total preorder on `α` is the comparison of such a key function
(its quotient by ties). Quantifying over linear orders instead, as `IsRank` does, would leave
equality outside the oracle: for `α = ℕ` the program `fun k tree => pure (tree.toList.lookup k)`
would be correct and ask nothing. With ties the oracle can answer both `k ≤ x` and `x ≤ k` for
`k ≠ x`, so whether the query key is present is decided by comparisons, and the lower bound
`lookup_lowerBound_infinite` holds. That bound also needs distinct values, since its `n + 1`
distinct answers are the `n` stored values and absence; sets (`β = Unit`) are not covered, and the
bound for them, which needs a counting argument over distinct comparison transcripts rather than
distinct results, is open under `#3674`. -/
structure IsLookup (prog : α → BTree α β → FreeM (LEQuery α) (Option β)) : Prop where
  /-- Under the oracle of a key function that strictly orders `tree.toList`'s keys, `prog k tree`
  is the lookup of `key k` among the entries with mapped keys. -/
  correct : ∀ {W : Type} [LinearOrder W] (key : α → W) (k : α) (tree : BTree α β),
    (tree.toList.map fun x => key x.1).Pairwise (· < ·) →
    (prog k tree).eval (LEQuery.keyOracle key) =
      (tree.toList.map fun x => (key x.1, x.2)).lookup (key k)

/-- A tree whose keys are strictly increasing under `key` has sorted entries once its keys are
mapped by `key`. -/
private theorem isSortedAssoc_mapKeys {W : Type} [LinearOrder W] (key : α → W)
    (tree : BTree α β) (h : (tree.toList.map fun x => key x.1).Pairwise (· < ·)) :
    (tree.mapKeys key).toList.IsSortedAssoc := by
  rw [toList_mapKeys, List.isSortedAssoc_iff_pairwise, List.map_map]
  exact h

/-- `lookupQ` (linear in-node search) is a correct comparison-based lookup program. -/
theorem lookupQ_isLookup : IsLookup (lookupQ (α := α) (β := β)) where
  correct key k tree h := by
    rw [eval_lookupQ_keyOracle, lookup_eq_of_isSortedAssoc (isSortedAssoc_mapKeys key tree h),
      toList_mapKeys]

/-- `lookupBinQ` (binary in-node search) is a correct comparison-based lookup program. -/
theorem lookupBinQ_isLookup : IsLookup (lookupBinQ (α := α) (β := β)) where
  correct key k tree h := by
    have hs := isSortedAssoc_mapKeys key tree h
    rw [eval_lookupBinQ_keyOracle, lookupBin_eq_lookup hs, lookup_eq_of_isSortedAssoc hs,
      toList_mapKeys]

end Specification

section LowerBound

/-- **Per-tree comparison lower bound for lookup.** On any B-tree `tree` with distinct keys and
distinct values over an infinite key type `α`, any `IsLookup` program makes at least
`⌈log₂(tree.size + 1)⌉` comparisons for some query key `k` and comparison oracle. -/
theorem lookup_lowerBound_infinite [Infinite α]
    {prog : α → BTree α β → FreeM (LEQuery α) (Option β)} (h : IsLookup prog)
    (tree : BTree α β) (hkeys : (tree.toList.map Prod.fst).Nodup)
    (hvals : (tree.toList.map Prod.snd).Nodup) :
    ∃ (k : α) (oracle : {ι : Type} → LEQuery α ι → ι),
      Nat.clog 2 (tree.size + 1) ≤ (prog k tree).countQueries oracle := by
  classical
  let l := tree.toList
  let xs := l.map Prod.fst
  let n := tree.size
  have hn : l.length = n := length_toList
  obtain ⟨k, hk⟩ : ∃ k : α, k ∉ xs := by
    simpa using Infinite.exists_notMem_finset xs.toFinset
  let key : Fin (n + 1) → α → ℕ := fun i a =>
    if a = k then (if (i : ℕ) < n then 2 * i else 2 * n + 1) else 2 * xs.idxOf a
  have key_getElem (i : Fin (n + 1)) (j : ℕ) (hj : j < l.length) : key i l[j].1 = 2 * j := by
    have hxs : xs[j]'(by rwa [List.length_map]) = l[j].1 := List.getElem_map ..
    have hne : l[j].1 ≠ k := fun he => hk (he ▸ hxs ▸ List.getElem_mem _)
    simp only [key, hne, ↓reduceIte]
    rw [← hxs]
    exact congrArg (2 * ·) (hkeys.idxOf_getElem j _)
  have hsorted (i : Fin (n + 1)) : (l.map fun x => key i x.1).Pairwise (· < ·) := by
    refine List.pairwise_iff_getElem.mpr fun a b ha hb hab => ?_
    rw [List.length_map] at ha hb
    rw [List.getElem_map, List.getElem_map, key_getElem i a ha, key_getElem i b hb]
    omega
  let ans : Fin (n + 1) → Option β := fun i =>
    if hi : (i : ℕ) < n then some (l[(i : ℕ)]'(by omega)).2 else none
  have heval (i : Fin (n + 1)) : (prog k tree).eval (LEQuery.keyOracle (key i)) = ans i := by
    rw [h.correct (key i) k tree (hsorted i)]
    by_cases hi : (i : ℕ) < n
    · have hki : key i k = 2 * i := by simp [key, hi]
      have hnodup : ((l.map fun x => (key i x.1, x.2)).map Prod.fst).Nodup := by
        rw [List.map_map]
        exact (hsorted i).imp Nat.ne_of_lt
      have hans : ans i = some (l[(i : ℕ)]'(by omega)).2 := by simp only [ans, hi, ↓reduceDIte]
      rw [hki, hans, List.lookup_eq_some_iff_mem hnodup]
      exact List.mem_map.mpr ⟨l[(i : ℕ)]'(by omega), List.getElem_mem _, by
        rw [key_getElem i i (by omega)]⟩
    · have hki : key i k = 2 * n + 1 := by simp [key, hi]
      have hans : ans i = none := by simp only [ans, hi, ↓reduceDIte]
      rw [hki, hans]
      refine List.lookup_eq_none_of_forall_ne fun p hp => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [key_getElem i j hj]
      omega
  have hans : Function.Injective ans := by
    intro i j hij
    have hi' := i.isLt
    have hj' := j.isLt
    simp only [ans] at hij
    split_ifs at hij with hi hj
    · have hget : (l.map Prod.snd)[(i : ℕ)]'(by rw [List.length_map]; omega) =
          (l.map Prod.snd)[(j : ℕ)]'(by rw [List.length_map]; omega) := by
        rw [List.getElem_map, List.getElem_map]
        exact Option.some.inj hij
      exact Fin.ext (hvals.getElem_inj_iff.mp hget)
    · exact Fin.ext (by omega)
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2 LEQuery.cardResponse_le_two
    (prog k tree) (fun i => LEQuery.keyOracle (key i)) (by omega)
    fun i j hij => hans ((heval i).symm.trans (hij.trans (heval j)))
  exact ⟨k, LEQuery.keyOracle (key i), hi⟩

/-- **Comparison lower bound for B-tree lookup over well-formed inputs (`WFInput`).** When
`2 ≤ t`, any `IsLookup` program restricted to well-formed B-trees of minimum degree `t`
(`WFInput α β t`) on an infinite key type `α` and infinite value type `β` still has worst-case
comparison query complexity at least `⌈log₂(n + 1)⌉` at every input size `n`. -/
theorem IsLookup.lowerBound_wfInput_infinite [LinearOrder α] [Infinite α] [Infinite β]
    {t : ℕ} (ht : 2 ≤ t) {prog : α → BTree α β → FreeM (LEQuery α) (Option β)}
    (h : IsLookup prog) :
    LowerBound (fun p : WFInput α β t => prog p.val.2 p.val.1) (fun p => p.val.1.size)
      (fun n => Nat.clog 2 (n + 1)) := by
  intro n
  let vs := (List.range n).map (Infinite.natEmbedding β)
  obtain ⟨tree, hwf, hsize, hkeys, hvals⟩ := exists_isWF_toList_map_snd_eq (α := α) ht vs
  rw [List.length_map, List.length_range] at hsize
  obtain ⟨k, oracle, hi⟩ := lookup_lowerBound_infinite h tree hkeys
    (hvals ▸ List.nodup_range.map (Infinite.natEmbedding β).injective)
  exact ⟨⟨(tree, k), hwf⟩, hsize.le, oracle, hsize ▸ hi⟩

/-- **Comparison lower bound for B-tree lookup (`Cslib.Query.LowerBound`).** Any `IsLookup` program
on an infinite key type `α` and infinite value type `β` has worst-case comparison query complexity
at least `⌈log₂(n + 1)⌉` on trees of size at most `n`. -/
theorem IsLookup.lowerBound_infinite [Infinite α] [Infinite β]
    {prog : α → BTree α β → FreeM (LEQuery α) (Option β)} (h : IsLookup prog) :
    LowerBound (fun p : BTree α β × α => prog p.2 p.1) (fun p => p.1.size)
      (fun n => Nat.clog 2 (n + 1)) :=
  -- Forget well-formedness under some linear order on `α`.
  letI := IsWellOrder.linearOrder (α := α) WellOrderingRel
  fun n =>
    let ⟨x, hx, oracle, hi⟩ := h.lowerBound_wfInput_infinite (t := 2) le_rfl n
    ⟨x.val, hx, oracle, hi⟩

end LowerBound

end Cslib.DataStructure.BTree
