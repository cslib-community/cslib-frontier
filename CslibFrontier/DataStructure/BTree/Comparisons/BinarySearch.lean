/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.BinarySearch
public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.OfSortedList
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence

/-!
# Comparison costs of B-tree queries with binary in-node search

This file instantiates `lookupBinM` and `rankBinM` in CSLib's query-complexity framework, at
`FreeM (LEQuery α)` with the comparison query `LEQuery.ask` and the trivial `visit := pure ()`,
as `Comparisons.Query` does for the linear scans. Every key comparison is a query.

Bisecting `n` keys takes at most `⌈log₂ (n + 1)⌉` comparisons, on any list and under any
oracle (`countQueries_slotBinM_le`). A node of a well-formed tree of minimum degree `t` holds at
most `2 * t - 1` keys, so the search costs at most `⌈log₂ (2 * t)⌉` comparisons per node. Rank
needs nothing more; lookup spends one further comparison to test the key found for equality.
`le_mul_height_of_node_le` sums the per-node cost along the descent. The bounds hold for every
oracle, since the shape of the tree does not depend on the answers. Under `orderOracle` the
programs evaluate to the pure `lookupBin` and `rankBin`, which are `lookup` and `rank` on trees
with sorted entries (`lookupBin_eq_lookup`, `rankBin_eq_rank`).

The linear scans of `Comparisons.Query` are bounded by `2 * t * height` comparisons, so
bisection replaces the factor `2 * t` by `⌈log₂ (2 * t)⌉ + 1`.

Composed with the height bound `IsWF.height_le_log`, the counts become bounds in the number `n`
of entries: at most `(⌈log₂ (2 * t)⌉ + 1) * (log_t ((n + 1) / 2) + 1)` comparisons for lookup
and `⌈log₂ (2 * t)⌉ * (log_t ((n + 1) / 2) + 1)` for rank, with the dependence on `t`
explicit. For fixed `t` and `n ≥ 1` both are within a constant factor of `⌈log₂ (n + 1)⌉`.
They are stated for every well-formed tree, and as `UpperBound` statements whose size function
is `size`. They are also stated for the tree bulk-loaded from any list of `n` entries, sorted or
not: like the answers of the oracle, the order of the keys does not change the shape of the
tree, and the counts need only the shape (`countQueries_lookupBinQ_le_of_occupied`,
`countQueries_rankBinQ_le_of_occupied`).

The statements are original to this development; no lower bound is proved here.

## Main definitions

* `lookupBinQ`, `rankBinQ`: lookup and rank by binary in-node search, counting comparisons.

## Main results

* `countQueries_slotBinM_le`: bisecting `n` keys makes at most `⌈log₂ (n + 1)⌉` comparisons.
* `countQueries_lookupBinQ_le`, `lookupBinQ_upperBound`: `lookupBinQ` makes at most
  `(⌈log₂ (2 * t)⌉ + 1) * height` comparisons on a well-formed tree.
* `countQueries_rankBinQ_le`, `rankBinQ_upperBound`: `rankBinQ` makes at most
  `⌈log₂ (2 * t)⌉ * height` comparisons on a well-formed tree.
* `countQueries_lookupBinQ_le_log`, `countQueries_rankBinQ_le_log`: the same counts in the number
  of entries, through `IsWF.height_le_log`.
* `countQueries_lookupBinQ_le_of_occupied`, `countQueries_rankBinQ_le_of_occupied`: the counts
  per level from the shape of the tree alone, without sorted keys.
* `countQueries_lookupBinQ_ofSortedList_le`, `countQueries_rankBinQ_ofSortedList_le`: the counts
  on a tree bulk-loaded from any list, in the length of the list.
* `lookupBinQ_upperBound_size`, `rankBinQ_upperBound_size`: the bounds in the number of entries
  over all oracles.
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Lookup by binary in-node search, issuing one query per key comparison. -/
def lookupBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupBinM LEQuery.ask (pure ()) k tr

/-- `lookupBinQ` is the `FreeM (LEQuery α)` instantiation of `lookupBinM`. -/
theorem lookupBinQ_def (k : α) : lookupBinQ k tr = lookupBinM LEQuery.ask (pure ()) k tr := (rfl)

/-- Rank by binary in-node search, issuing one query per key comparison. -/
def rankBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) ℕ :=
  rankBinM LEQuery.ask (pure ()) k tr

/-- `rankBinQ` is the `FreeM (LEQuery α)` instantiation of `rankBinM`. -/
theorem rankBinQ_def (k : α) : rankBinQ k tr = rankBinM LEQuery.ask (pure ()) k tr := (rfl)

section Transfer

variable [LinearOrder α]

/-- Under the order's oracle, `lookupBinQ` evaluates to the pure `lookupBin`. -/
@[simp] theorem eval_lookupBinQ (k : α) :
    (lookupBinQ k tr).eval orderOracle = lookupBin k tr := by
  simpa [lookupBinQ, lookupBin_def] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_lookupBinM LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `rankBinQ` evaluates to the pure `rankBin`. -/
@[simp] theorem eval_rankBinQ (k : α) : (rankBinQ k tr).eval orderOracle = rankBin k tr := by
  simpa [rankBinQ, rankBin_def] using
    Id.ext_iff.1 ((FreeM.isMonadHom_pure_eval orderOracle).map_rankBinM LEQuery.ask (pure ()) k tr)

end Transfer

/-! ### Comparison counts -/

variable (oracle : {ι : Type} → LEQuery α ι → ι)

/-- The within-node binary search makes at most `⌈log₂ (n + 1)⌉` comparisons on `n` keys, sorted
or not, under every oracle. -/
theorem countQueries_slotBinM_le (k : α) (rest : List (Triple α β)) :
    (slotBinM LEQuery.ask k rest).countQueries oracle ≤ Nat.clog 2 (rest.length + 1) := by
  induction hn : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    rcases rest with _ | ⟨e, l⟩
    · simp
    · simp only [List.length_cons] at hn
      have hsub : ∀ l' : List (Triple α β), l'.length ≤ (l.length + 1) / 2 →
          (slotBinM LEQuery.ask k l').countQueries oracle + 1 ≤ Nat.clog 2 (n + 1) :=
        fun l' hl' => (Nat.add_le_add_right (ih _ (by omega) l' rfl) 1).trans
          (Nat.clog_two_lt_clog_two_of_le_half (by omega) (by omega))
      have ht := hsub ((e :: l).take ((l.length + 1) / 2)) (by simp)
      have hd := hsub (l.drop ((l.length + 1) / 2)) (by simp; omega)
      rw [slotBinM_cons]
      by_cases h : oracle (.le k ((e :: l)[(l.length + 1) / 2]'(by simp; omega)).1) = true <;>
        simp [h] <;> omega

private theorem countQueries_bin_le_of_occupied {γ : Type} {d : ℕ}
    {q : BTree α β → FreeM (LEQuery α) γ} (ht : 0 < t) (k : α)
    (hleaf : (q .leaf).countQueries oracle = 0)
    (hstep : ∀ first (rest : List (Triple α β)) B,
      (∀ (i : ℕ), ∀ c ∈ (node first rest).children[i]?, (q c).countQueries oracle ≤ B) →
      (q (node first rest)).countQueries oracle ≤
        (slotBinM LEQuery.ask k rest).countQueries oracle + d + B)
    (hk : tr.rootKeys ≤ 2 * t - 1) (hc : ∀ c ∈ tr.children, Occupied t c) :
    (q tr).countQueries oracle ≤ (Nat.clog 2 (2 * t) + d) * tr.height :=
  le_mul_height_of_node_le (c := Nat.clog 2 (2 * t) + d) hleaf
    (fun first rest B hl hB => by
      have hs := (countQueries_slotBinM_le oracle k rest).trans
        (Nat.clog_mono_right 2 (m := 2 * t) (by omega))
      have hstep' := hstep first rest B fun _ c hci => hB c (List.mem_of_getElem? hci)
      omega)
    hk hc

/-- Lookup by binary in-node search makes at most `⌈log₂ (2 * t)⌉ + 1` comparisons per level,
under every oracle, in a tree whose root holds at most `2 * t - 1` keys and whose children are
occupied. The keys need not be sorted. -/
theorem countQueries_lookupBinQ_le_of_occupied (ht : 0 < t) (hk : tr.rootKeys ≤ 2 * t - 1)
    (hc : ∀ c ∈ tr.children, Occupied t c) (k : α) :
    (lookupBinQ k tr).countQueries oracle ≤ (Nat.clog 2 (2 * t) + 1) * tr.height :=
  countQueries_bin_le_of_occupied (d := 1) oracle ht k (by simp [lookupBinQ, lookupBinM_leaf])
    (fun first rest B hB => by
      simp only [lookupBinQ] at hB
      simp only [lookupBinQ, lookupBinM_node, FreeM.countQueries_bind, FreeM.countQueries_pure,
        zero_add]
      generalize (slotBinM LEQuery.ask k rest).eval oracle = i
      rcases hc' : (node first rest).children[i]? with _ | c
      · rcases rest[i]? with _ | e <;> simp <;> grind
      · have := hB i c hc'; rcases rest[i]? with _ | e <;> simp <;> grind)
    hk hc

/-- Rank by binary in-node search makes at most `⌈log₂ (2 * t)⌉` comparisons per level, under
every oracle, in a tree whose root holds at most `2 * t - 1` keys and whose children are
occupied. The keys need not be sorted. -/
theorem countQueries_rankBinQ_le_of_occupied (ht : 0 < t) (hk : tr.rootKeys ≤ 2 * t - 1)
    (hc : ∀ c ∈ tr.children, Occupied t c) (k : α) :
    (rankBinQ k tr).countQueries oracle ≤ Nat.clog 2 (2 * t) * tr.height :=
  countQueries_bin_le_of_occupied (d := 0) oracle ht k (by simp [rankBinQ, rankBinM_leaf])
    (fun first rest B hB => by
      simp only [rankBinQ] at hB
      simp only [rankBinQ, rankBinM_node, FreeM.countQueries_bind, FreeM.countQueries_pure,
        zero_add]
      rcases hc' : (node first rest).children[(slotBinM LEQuery.ask k rest).eval oracle]? with
        _ | c
      · simp
      · have := hB _ c hc'; simp; omega)
    hk hc

/-- Lookup by binary in-node search in the tree bulk-loaded from a list of `n` entries makes at
most `(⌈log₂ (2 * t)⌉ + 1) * (log_t ((n + 1) / 2) + 1)` comparisons, under every oracle. The
list need not be sorted: the shape of the tree does not depend on the keys. -/
theorem countQueries_lookupBinQ_ofSortedList_le (ht : 2 ≤ t) (l : List (α × β)) (k : α) :
    (lookupBinQ k (ofSortedList t l)).countQueries oracle ≤
      (Nat.clog 2 (2 * t) + 1) * (Nat.log t ((l.length + 1) / 2) + 1) :=
  (countQueries_lookupBinQ_le_of_occupied oracle (by omega) (rootKeys_ofSortedList_le ht l)
    (fun _ hc => occupied_of_mem_children_ofSortedList ht l hc) k).trans
    (Nat.mul_le_mul_left _ (height_ofSortedList_le ht l))

/-- Rank by binary in-node search in the tree bulk-loaded from a list of `n` entries makes at
most `⌈log₂ (2 * t)⌉ * (log_t ((n + 1) / 2) + 1)` comparisons, under every oracle. The list
need not be sorted. -/
theorem countQueries_rankBinQ_ofSortedList_le (ht : 2 ≤ t) (l : List (α × β)) (k : α) :
    (rankBinQ k (ofSortedList t l)).countQueries oracle ≤
      Nat.clog 2 (2 * t) * (Nat.log t ((l.length + 1) / 2) + 1) :=
  (countQueries_rankBinQ_le_of_occupied oracle (by omega) (rootKeys_ofSortedList_le ht l)
    (fun _ hc => occupied_of_mem_children_ofSortedList ht l hc) k).trans
    (Nat.mul_le_mul_left _ (height_ofSortedList_le ht l))

variable [LinearOrder α]

/-- Lookup by binary in-node search in a well-formed tree makes at most `⌈log₂ (2 * t)⌉ + 1`
comparisons per level, under every oracle. -/
theorem countQueries_lookupBinQ_le (h : IsWF t tr) (k : α) :
    (lookupBinQ k tr).countQueries oracle ≤ (Nat.clog 2 (2 * t) + 1) * tr.height :=
  countQueries_lookupBinQ_le_of_occupied oracle (by have := h.two_le; omega) h.rootKeys_le
    h.occupied_of_mem_children k

/-- Rank by binary in-node search in a well-formed tree makes at most `⌈log₂ (2 * t)⌉`
comparisons per level, under every oracle. -/
theorem countQueries_rankBinQ_le (h : IsWF t tr) (k : α) :
    (rankBinQ k tr).countQueries oracle ≤ Nat.clog 2 (2 * t) * tr.height :=
  countQueries_rankBinQ_le_of_occupied oracle (by have := h.two_le; omega) h.rootKeys_le
    h.occupied_of_mem_children k

/-! ### Bounds in the number of entries -/

/-- Lookup by binary in-node search in a well-formed tree of `n` entries makes at most
`(⌈log₂ (2 * t)⌉ + 1) * (log_t ((n + 1) / 2) + 1)` comparisons, under every oracle. -/
theorem countQueries_lookupBinQ_le_log (h : IsWF t tr) (k : α) :
    (lookupBinQ k tr).countQueries oracle ≤
      (Nat.clog 2 (2 * t) + 1) * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_lookupBinQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Rank by binary in-node search in a well-formed tree of `n` entries makes at most
`⌈log₂ (2 * t)⌉ * (log_t ((n + 1) / 2) + 1)` comparisons, under every oracle. -/
theorem countQueries_rankBinQ_le_log (h : IsWF t tr) (k : α) :
    (rankBinQ k tr).countQueries oracle ≤
      Nat.clog 2 (2 * t) * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_rankBinQ_le oracle h k).trans (Nat.mul_le_mul_left _ h.height_le_log)

end Comparisons

/-! ### Upper bounds over all oracles -/

section UpperBounds

variable {α β : Type} [LinearOrder α] {t : ℕ}

/-- Lookup by binary in-node search makes at most `⌈log₂ (2 * t)⌉ + 1` comparisons at each of at
most `height` nodes. -/
theorem lookupBinQ_upperBound :
    UpperBound (fun p : WFInput α β t => lookupBinQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => (Nat.clog 2 (2 * t) + 1) * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_lookupBinQ_le oracle p.property p.val.2

/-- Rank by binary in-node search makes at most `⌈log₂ (2 * t)⌉` comparisons at each of at most
`height` nodes. -/
theorem rankBinQ_upperBound :
    UpperBound (fun p : WFInput α β t => rankBinQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => Nat.clog 2 (2 * t) * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_rankBinQ_le oracle p.property p.val.2

/-- Lookup by binary in-node search in a well-formed tree of at most `n` entries makes at most
`(⌈log₂ (2 * t)⌉ + 1) * (log_t ((n + 1) / 2) + 1)` comparisons. -/
theorem lookupBinQ_upperBound_size :
    UpperBound (fun p : WFInput α β t => lookupBinQ p.val.2 p.val.1) (fun p => p.val.1.size)
      (fun n => (Nat.clog 2 (2 * t) + 1) * (Nat.log t ((n + 1) / 2) + 1)) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right (by omega))))
    fun oracle p => countQueries_lookupBinQ_le_log oracle p.property p.val.2

/-- Rank by binary in-node search in a well-formed tree of at most `n` entries makes at most
`⌈log₂ (2 * t)⌉ * (log_t ((n + 1) / 2) + 1)` comparisons. -/
theorem rankBinQ_upperBound_size :
    UpperBound (fun p : WFInput α β t => rankBinQ p.val.2 p.val.1) (fun p => p.val.1.size)
      (fun n => Nat.clog 2 (2 * t) * (Nat.log t ((n + 1) / 2) + 1)) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right (by omega))))
    fun oracle p => countQueries_rankBinQ_le_log oracle p.property p.val.2

end UpperBounds

end Cslib.DataStructure.BTree
