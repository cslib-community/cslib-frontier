/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.Range

/-!
# Comparison cost of B-tree closed-interval queries

`rangeQ` instantiates `rangeM` in CSLib's query-complexity framework, at `FreeM (LEQuery α)` with
the comparison query `LEQuery.ask` and the trivial `visit := pure ()`. `eval_rangeQ` identifies
its value under `orderOracle` with `range`, through the transfer lemma
`Cslib.IsMonadHom.map_rangeM`.

The scan of a node compares each separator it reaches with both bounds, so one visited node can
cost `2 * (2 * t - 1)` comparisons: the per-node bound of `2 * t` behind the point-query bounds
fails, and the node-visit bound of `time_rangeT` cannot simply be multiplied by it. The count is
bounded instead by charging two comparisons to every returned entry and the rest to the two
boundary paths. `countQueries_rangeQ_of_occupied` proves at most `4 * t * height + 2 * k`
comparisons, where `k` is the length of the output, on any tree with sorted entries, at most
`2 * t - 1` root keys and children occupied for some `t > 0`, through three auxiliary bounds by
recursion on the tree:

* a subtree whose entries all lie in the interval costs two comparisons per returned entry;
* a subtree whose keys are all at least `lo` costs at most two more per level, for the
  separator above `hi` that stops each scan on the path towards `hi`;
* a subtree whose keys are all at most `hi` costs at most `2 * (2 * t - 1)` more per level, for
  the separators below `lo` on the path towards `lo`.

`countQueries_rangeQ_le` restates the bound on well-formed trees as
`2 * t * (2 * height + k)`, and `countQueries_rangeQ_le_log` composes it with
`IsWF.height_le_log`. The bounds are stated at the order's oracle only: under another oracle
the output is not the output under `≤`, so a bound in its length is not meaningful.

## Main definitions

* `rangeQ`: B-tree closed-interval query counting comparisons.

## Main results

* `countQueries_rangeQ_le`: the number of comparisons made by `rangeQ` is at most
  `2 * t * (2 * tr.height + (range lo hi tr).length)`.
* `eval_rangeQ`: the value of `rangeQ` evaluated at the order oracle matches `range`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from cslib-community/EpsilonEridani PR #39 at commit 9425389c8.
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery)

namespace Cslib.DataStructure.BTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Closed-interval query, issuing one query per key comparison. -/
def rangeQ (lo hi : α) (tr : BTree α β) : FreeM (LEQuery α) (List (α × β)) :=
  rangeM LEQuery.ask (pure ()) lo hi tr

/-- `rangeQ` is `rangeM` with the comparison query and free visits. -/
theorem rangeQ_def (lo hi : α) : rangeQ lo hi tr = rangeM LEQuery.ask (pure ()) lo hi tr := (rfl)

/-- A per-level charge `m` covers two comparisons per root key and the levels below the root. -/
private theorem two_mul_rootKeys_add_le {m : ℕ} (c : BTree α β) (hr : 2 * c.rootKeys ≤ m) :
    2 * c.rootKeys + m * (c.height - 1) ≤ m * c.height := by
  cases c with
  | leaf => simp
  | node first rest =>
    obtain ⟨h, hh⟩ := Nat.exists_eq_succ_of_ne_zero (n := (node first rest).height)
      (by have := height_first_succ_le (first := first) (rest := rest); omega)
    rw [hh, Nat.succ_sub_one, Nat.mul_succ]
    omega

/-- For an occupied first child of a node and per-level charge `m ≥ 4 * t - 2`, the child's
budget fits below the root of its parent. -/
private theorem first_budget_le {m : ℕ} {first : BTree α β} (rest : List (Triple α β))
    (hfirst : Occupied t first) (hm : 4 * t - 2 ≤ m) :
    2 * first.rootKeys + m * (first.height - 1) ≤ m * ((node first rest).height - 1) := by
  have := hfirst.rootKeys_le
  exact (two_mul_rootKeys_add_le first (by omega)).trans (Nat.mul_le_mul_left m
    (by have := height_first_succ_le (first := first) (rest := rest); omega))

/-- A per-level charge below the root of the node without its first child and separator fits
below the root of the original node. -/
private theorem mul_height_node_sub_one_le (m : ℕ) (first : BTree α β) (k : α) (v : β)
    (c : BTree α β) (rest : List (α × β × BTree α β)) :
    m * ((node c rest).height - 1) ≤ m * ((node first ((k, v, c) :: rest)).height - 1) :=
  Nat.mul_le_mul_left m
    (Nat.sub_le_sub_right (height_node_le_height_node_cons (first := first) (k := k) (v := v)) 1)

variable [LinearOrder α]

/-- Under the order's oracle, `rangeQ` evaluates to `range`. -/
@[simp] theorem eval_rangeQ (lo hi : α) : (rangeQ lo hi tr).eval orderOracle = range lo hi tr := by
  simpa [range_def, rangeQ] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_rangeM LEQuery.ask (pure ()) lo hi tr)

/-- The empty tree costs no comparison. -/
@[simp] theorem countQueries_rangeQ_leaf (lo hi : α) :
    (rangeQ lo hi (.leaf : BTree α β)).countQueries orderOracle = 0 := by
  simp [rangeQ, rangeM_leaf]

/-- A node without keys costs what its only child costs. -/
@[simp] theorem countQueries_rangeQ_node_nil (lo hi : α) (first : BTree α β) :
    (rangeQ lo hi (.node first [])).countQueries orderOracle =
      (rangeQ lo hi first).countQueries orderOracle := by
  simp [rangeQ, rangeM_node, rangeRestM_nil]

/-- The first separator is compared with both bounds; the child before it is searched when the
separator is at least `lo`, and the remaining triples are scanned, as the node without its first
child and separator, when the separator is at most `hi`. -/
@[simp] theorem countQueries_rangeQ_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (α × β × BTree α β)) :
    (rangeQ lo hi (.node first ((k, v, c) :: rest))).countQueries orderOracle =
      2 + (if lo ≤ k then (rangeQ lo hi first).countQueries orderOracle else 0) +
        (if k ≤ hi then (rangeQ lo hi (.node c rest)).countQueries orderOracle else 0) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;>
    simp [rangeQ, rangeM_node, rangeRestM_cons, hlo, hhi] <;> omega

/-! ### Auxiliary bounds -/

variable {lo hi : α}

/-- A query whose interval contains every entry costs two comparisons per entry returned. -/
private theorem countQueries_rangeQ_le_of_forall_mem {lo hi : α} {tr : BTree α β}
    (hs : tr.toList.IsSortedAssoc) (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeQ lo hi tr).countQueries orderOracle ≤ 2 * (range lo hi tr).length := by
  induction hs using induction_isSortedAssoc with
  | leaf => simp
  | node_nil _ _ ih => simpa using ih (by simpa using hin)
  | node_cons first k v c rest _ _ _ _ ih₁ ih₂ =>
    rw [toList_node_cons, List.forall_mem_append, List.forall_mem_cons] at hin
    obtain ⟨hinf, hk, hinn⟩ := hin
    have := ih₁ hinf; have := ih₂ hinn
    simp only [countQueries_rangeQ_node_cons, length_range_node_cons, hk.1, hk.2, ↓reduceIte]
    omega

/-- A query on a tree whose keys are all at least `lo` costs at most two comparisons per level
beyond two per entry returned: the separator above `hi` that stops the scan on the path towards
`hi`. -/
private theorem countQueries_rangeQ_le_of_forall_lo_le {lo hi : α} {tr : BTree α β}
    (hs : tr.toList.IsSortedAssoc) (hlo : ∀ p ∈ tr.toList, lo ≤ p.1) :
    (rangeQ lo hi tr).countQueries orderOracle ≤ 2 * tr.height + 2 * (range lo hi tr).length := by
  induction hs using induction_isSortedAssoc with
  | leaf => simp
  | node_nil first _ ih =>
    have := ih (by simpa using hlo)
    have := height_first_succ_le (first := first) (rest := [])
    simp only [countQueries_rangeQ_node_nil, range_node_nil]; omega
  | node_cons first k v c rest hsf _ hlt _ ih₁ ih₂ =>
    rw [toList_node_cons, List.forall_mem_append, List.forall_mem_cons] at hlo
    obtain ⟨hlof, hk, hlon⟩ := hlo
    have := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    by_cases hhi : k ≤ hi
    · have := countQueries_rangeQ_le_of_forall_mem hsf
        fun p hp => ⟨hlof p hp, ((hlt p hp).trans_le hhi).le⟩
      have := ih₂ hlon
      simp only [hk, hhi, ↓reduceIte]; omega
    · have := ih₁ hlof
      simp only [hk, hhi, ↓reduceIte]; omega

/-- Below the root, a level needs only `4 * t - 2` comparisons when all keys are at most `hi`.
Allowing two more comparisons per level also covers the search path that stops at `hi`.
In either case, the bound charges two comparisons per root key and per returned entry. -/
private theorem countQueries_rangeQ_le_rootKeys {lo hi : α} {tr : BTree α β} (ht : 0 < t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    {m : ℕ} (hm : 4 * t - 2 ≤ m) (hmode : (∀ p ∈ tr.toList, p.1 ≤ hi) ∨ 4 * t ≤ m) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * tr.rootKeys + m * (tr.height - 1) + 2 * (range lo hi tr).length := by
  induction hs using induction_isSortedAssoc generalizing m with
  | leaf => simp
  | node_nil first _ ih =>
    have hfirst : Occupied t first := hc first List.mem_cons_self
    have hchild := ih (fun _ h => hfirst.of_mem_children h) hm (by simpa using hmode)
    have hbudget := first_budget_le [] hfirst hm
    simp only [countQueries_rangeQ_node_nil, range_node_nil, rootKeys_node, List.length_nil]
    clear * - hchild hbudget
    lia
  | node_cons first k v c rest hsf hsn hlt hgt ih₁ ih₂ =>
    obtain ⟨hfirst, hcf, hcn⟩ := occupied_children_node_cons hc
    rw [toList_node_cons, List.forall_mem_append, List.forall_mem_cons] at hmode
    rw [countQueries_rangeQ_node_cons, length_range_node_cons lo hi]
    simp only [rootKeys_node, List.length_cons]
    by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
    · have hleft := ih₁ hcf (m := 4 * t - 2) le_rfl
        (Or.inl fun p hp => ((hlt p hp).trans_le hhi).le)
      have hbudget := first_budget_le ((k, v, c) :: rest) hfirst (m := 4 * t - 2) le_rfl
      rcases hmode with ⟨_, _, hright⟩ | hwide
      · have hrightCost := countQueries_rangeQ_le_of_forall_mem hsn
          fun p hp => ⟨hlo.trans (hgt p hp).le, hright p hp⟩
        have hbudget_le := Nat.mul_le_mul_right
          ((node first ((k, v, c) :: rest)).height - 1) hm
        simp only [hlo, hhi, ↓reduceIte]
        clear * - hleft hrightCost hbudget hbudget_le
        lia
      · have hrightCost := countQueries_rangeQ_le_of_forall_lo_le (hi := hi) hsn
          fun p hp => (hlo.trans_lt (hgt p hp)).le
        have htailHeight := height_node_le_height_node_cons (first := first) (k := k)
          (v := v) (c := c) (rest := rest)
        let levels := (node first ((k, v, c) :: rest)).height - 1
        have hscale := Nat.mul_le_mul_right levels hwide
        have hsplit := Nat.add_mul (4 * t - 2) 2 levels
        have ht4 : 4 ≤ 4 * t := by simpa using Nat.mul_le_mul_left 4 ht
        rw [Nat.sub_add_cancel ((by decide : 2 ≤ 4).trans ht4)] at hsplit
        simp only [hlo, hhi, ↓reduceIte]
        clear * - hleft hrightCost hbudget htailHeight hscale hsplit
        lia
    · have hleft := ih₁ hcf hm (hmode.imp And.left id)
      have hbudget := first_budget_le ((k, v, c) :: rest) hfirst hm
      simp only [hlo, hhi, ↓reduceIte]
      clear * - hleft hbudget
      lia
    · have hright := ih₂ hcn hm (hmode.imp (fun h => h.2.2) id)
      have hbudget := mul_height_node_sub_one_le m first k v c rest
      simp only [rootKeys_node] at hright
      simp only [hlo, hhi, ↓reduceIte]
      clear * - hright hbudget
      lia
    · simp only [hlo, hhi, ↓reduceIte]
      clear * -
      lia

/-! ### Comparison bounds -/

/-- A closed-interval query makes at most `4 * t * height + 2 * k` comparisons, where `k` is the
number of entries it returns, on any tree with sorted entries, at most `2 * t - 1` root keys and
children occupied for some `t > 0`. Each returned entry costs two comparisons; at each level,
the path towards `lo` costs at most `2 * (2 * t - 1)` more and the path towards `hi` at most
two. -/
theorem countQueries_rangeQ_of_occupied {tr : BTree α β} (ht : 0 < t)
    (hr : tr.rootKeys ≤ 2 * t - 1) (hc : ∀ c ∈ tr.children, Occupied t c)
    (hs : tr.toList.IsSortedAssoc) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      4 * t * tr.height + 2 * (range lo hi tr).length := by
  have hcost := countQueries_rangeQ_le_rootKeys (lo := lo) (hi := hi) ht hc hs
    (Nat.sub_le (4 * t) 2) (Or.inr le_rfl)
  have hbudget := two_mul_rootKeys_add_le tr (m := 4 * t) (by lia)
  exact hcost.trans (Nat.add_le_add_right hbudget _)

/-- A closed-interval query on a well-formed tree makes at most `2 * t * (2 * height + k)`
comparisons, where `k` is the number of entries it returns: the node-visit bound `2 * height + k`
of `time_rangeT` times `2 * t`. A single node can cost more than `2 * t` comparisons, so this is
a consequence of `countQueries_rangeQ_of_occupied`, not a per-node bound. -/
theorem countQueries_rangeQ_le (h : IsWF t tr) (lo hi : α) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * t * (2 * tr.height + (range lo hi tr).length) := by
  have := countQueries_rangeQ_of_occupied (lo := lo) (hi := hi) (by have := h.two_le; omega)
    h.rootKeys_le h.occupied_of_mem_children h.sorted
  have := Nat.mul_le_mul_right (range lo hi tr).length (show 2 ≤ 2 * t by have := h.two_le; omega)
  grind

/-- A closed-interval query on a well-formed tree makes logarithmically many comparisons beyond
`2 * t` per entry it returns. -/
theorem countQueries_rangeQ_le_log (h : IsWF t tr) (lo hi : α) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * t * (2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (range lo hi tr).length) :=
  (countQueries_rangeQ_le h lo hi).trans
    (Nat.mul_le_mul_left _ (by have := h.height_le_log; omega))

end Comparisons

end Cslib.DataStructure.BTree
