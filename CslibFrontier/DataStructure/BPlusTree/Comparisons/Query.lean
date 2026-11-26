/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Height
public import CslibFrontier.DataStructure.BPlusTree.PredSucc
public import CslibFrontier.DataStructure.BPlusTree.Rank
public import CslibFrontier.DataStructure.BTree.Comparisons.Query

/-!
# Comparison costs of B+-tree point queries

The point queries of `Cslib.DataStructure.BPlusTree` are defined once over a monad, with a
comparator and a node-visit action. This file instantiates them in CSLib's query-complexity
framework, at `FreeM (LEQuery α)` with the comparison query `LEQuery.ask` and the trivial
`visit := pure ()`, so that every key comparison is a query and node visits are free: `lookupQ`,
`containsQ`, `minQ`, `maxQ`, `predQ`, `succQ` and `rankQ`.

## Main definitions

* `lookupQ`, `containsQ`, `minQ`, `maxQ`, `predQ`, `succQ`, `rankQ`: B+-tree point queries
  counting comparisons.

## Main results

* `eval_lookupQ`: the value of `lookupQ` evaluated at the order oracle matches `lookup`.
* (and similarly for the other queries)

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BPlusTree

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BPlusTree α β}

/-- Lookup, issuing one query per key comparison. -/
def lookupQ (k : α) (tr : BPlusTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupM LEQuery.ask (pure ()) k tr

/-- `lookupQ` is `lookupM` with the comparison query and free visits. -/
theorem lookupQ_def (k : α) : lookupQ k tr = lookupM LEQuery.ask (pure ()) k tr := (rfl)

/-- Membership test, issuing one query per key comparison. -/
def containsQ (k : α) (tr : BPlusTree α β) : FreeM (LEQuery α) Bool :=
  containsM LEQuery.ask (pure ()) k tr

/-- `containsQ` is `containsM` with the comparison query and free visits. -/
theorem containsQ_def (k : α) : containsQ k tr = containsM LEQuery.ask (pure ()) k tr := (rfl)

/-- Least entry in the comparison model, where it asks nothing. -/
def minQ (tr : BPlusTree α β) : FreeM (LEQuery α) (Option (α × β)) := minM (pure ()) tr

/-- `minQ` is `minM` with free visits. -/
theorem minQ_def : minQ tr = minM (pure ()) tr := (rfl)

/-- Greatest entry in the comparison model, where it asks nothing. -/
def maxQ (tr : BPlusTree α β) : FreeM (LEQuery α) (Option (α × β)) := maxM (pure ()) tr

/-- `maxQ` is `maxM` with free visits. -/
theorem maxQ_def : maxQ tr = maxM (pure ()) tr := (rfl)

/-- Strict predecessor, issuing one query per key comparison. -/
def predQ (k : α) (tr : BPlusTree α β) : FreeM (LEQuery α) (Option (α × β)) :=
  predM LEQuery.ask (pure ()) k tr

/-- `predQ` is `predM` with the comparison query and free visits. -/
theorem predQ_def (k : α) : predQ k tr = predM LEQuery.ask (pure ()) k tr := (rfl)

/-- Strict successor, issuing one query per key comparison. -/
def succQ (k : α) (tr : BPlusTree α β) : FreeM (LEQuery α) (Option (α × β)) :=
  succM LEQuery.ask (pure ()) k tr

/-- `succQ` is `succM` with the comparison query and free visits. -/
theorem succQ_def (k : α) : succQ k tr = succM LEQuery.ask (pure ()) k tr := (rfl)

/-- Rank, issuing one query per key comparison. -/
def rankQ (k : α) (tr : BPlusTree α β) : FreeM (LEQuery α) ℕ := rankM LEQuery.ask (pure ()) k tr

/-- `rankQ` is `rankM` with the comparison query and free visits. -/
theorem rankQ_def (k : α) : rankQ k tr = rankM LEQuery.ask (pure ()) k tr := (rfl)

/-! ### Transfer: `eval` at the order's oracle is the pure operation -/

/-- Under any oracle, `minQ` evaluates to `min?`. -/
@[simp] theorem eval_minQ (oracle : {ι : Type} → LEQuery α ι → ι) :
    (minQ tr).eval oracle = min? tr := by
  simpa [min?_def, minQ] using
    Id.ext_iff.1 (map_minM (FreeM.isMonadHom_pure_eval oracle) (pure ()) tr)

/-- Under any oracle, `maxQ` evaluates to `max?`. -/
@[simp] theorem eval_maxQ (oracle : {ι : Type} → LEQuery α ι → ι) :
    (maxQ tr).eval oracle = max? tr := by
  simpa [max?_def, maxQ] using
    Id.ext_iff.1 (map_maxM (FreeM.isMonadHom_pure_eval oracle) (pure ()) tr)

section Transfer

variable [LinearOrder α]

/-- Under the order's oracle, `lookupQ` evaluates to `lookup`. -/
@[simp] theorem eval_lookupQ (k : α) : (lookupQ k tr).eval BTree.orderOracle = lookup k tr := by
  simpa [lookup_def, lookupQ] using
    Id.ext_iff.1
      (map_lookupM (FreeM.isMonadHom_pure_eval BTree.orderOracle) LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `containsQ` evaluates to `contains`. -/
@[simp] theorem eval_containsQ (k : α) :
    (containsQ k tr).eval BTree.orderOracle = contains k tr := by
  simp [containsQ, containsM, ← lookupQ_def]

/-- Under the order's oracle, `predQ` evaluates to `pred?`. -/
@[simp] theorem eval_predQ (k : α) : (predQ k tr).eval BTree.orderOracle = pred? k tr := by
  simpa [pred?_def, predQ] using
    Id.ext_iff.1
      (map_predM (FreeM.isMonadHom_pure_eval BTree.orderOracle) LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `succQ` evaluates to `succ?`. -/
@[simp] theorem eval_succQ (k : α) : (succQ k tr).eval BTree.orderOracle = succ? k tr := by
  simpa [succ?_def, succQ] using
    Id.ext_iff.1
      (map_succM (FreeM.isMonadHom_pure_eval BTree.orderOracle) LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `rankQ` evaluates to `rank`. -/
@[simp] theorem eval_rankQ (k : α) : (rankQ k tr).eval BTree.orderOracle = rank k tr := by
  simpa [rank_def, rankQ] using
    Id.ext_iff.1
      (map_rankM (FreeM.isMonadHom_pure_eval BTree.orderOracle) LEQuery.ask (pure ()) k tr)

end Transfer

/-! ### Comparison counts -/

variable (oracle : {ι : Type} → LEQuery α ι → ι)

/-- The within-node separator search makes at most one comparison per separator. -/
theorem countQueries_slotM_le (k : α) (rest : List (Branch α β)) :
    (slotM LEQuery.ask k rest).countQueries oracle ≤ rest.length := by
  induction rest with
  | nil => simp [slotM]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    by_cases h : oracle (.le s k) = true
    · simp [slotM, h]; omega
    · simp [slotM, h]

/-- The minimum search makes no comparison. -/
@[simp] theorem countQueries_minQ (tr : BPlusTree α β) : (minQ tr).countQueries oracle = 0 := by
  rw [minQ]
  fun_induction minM (pure () : FreeM (LEQuery α) Unit) tr <;> simp [*]

/-- The maximum search makes no comparison. -/
@[simp] theorem countQueries_maxQ (tr : BPlusTree α β) : (maxQ tr).countQueries oracle = 0 := by
  rw [maxQ]
  fun_induction maxM (pure () : FreeM (LEQuery α) Unit) tr <;> simp [*]

/-- The membership test makes as many comparisons as lookup. -/
@[simp] theorem countQueries_containsQ (k : α) :
    (containsQ k tr).countQueries oracle = (lookupQ k tr).countQueries oracle := by
  simp [containsQ, containsM, lookupQ]

private theorem countQueries_scan_lookupM_le (k : α) (l : List (α × β)) :
    (SortedAssoc.lookupM LEQuery.ask k l).countQueries oracle ≤ l.length + 1 := by
  induction l with
  | nil => simp [SortedAssoc.lookupM]
  | cons e l ih =>
    obtain ⟨k', v⟩ := e
    by_cases h : oracle (.le k k') = true
    · by_cases h' : oracle (.le k' k) = true <;> simp [SortedAssoc.lookupM, h, h']
    · simp [SortedAssoc.lookupM, h]; omega

private theorem countQueries_scan_rankM_le (k : α) (l : List (α × β)) :
    (SortedAssoc.rankM LEQuery.ask k l).countQueries oracle ≤ l.length := by
  induction l with
  | nil => simp [SortedAssoc.rankM]
  | cons e l ih =>
    by_cases h : oracle (.le k e.1) = true
    · simp [SortedAssoc.rankM, h]
    · simp [SortedAssoc.rankM, h]; omega

private theorem countQueries_scan_predM_le (k : α) (l : List (α × β)) :
    (SortedAssoc.predM LEQuery.ask k l).countQueries oracle ≤ l.length := by
  induction l with
  | nil => simp [SortedAssoc.predM]
  | cons e l ih =>
    by_cases h : oracle (.le k e.1) = true
    · simp [SortedAssoc.predM, h]
    · simp [SortedAssoc.predM, h]; omega

private theorem countQueries_scan_succM_le (k : α) (l : List (α × β)) :
    (SortedAssoc.succM LEQuery.ask k l).countQueries oracle ≤ l.length := by
  induction l with
  | nil => simp [SortedAssoc.succM]
  | cons e l ih =>
    by_cases h : oracle (.le e.1 k) = true
    · simp [SortedAssoc.succM, h]; omega
    · simp [SortedAssoc.succM, h]

/-- Lookup in a leaf makes at most one comparison per entry and one more to test equality. -/
theorem countQueries_lookupQ_leaf_le (k : α) (entries : List (α × β)) :
    (lookupQ k (.leaf entries)).countQueries oracle ≤ entries.length + 1 := by
  simpa [lookupQ, lookupM] using countQueries_scan_lookupM_le oracle k entries

/-- Rank in a leaf makes at most one comparison per entry. -/
theorem countQueries_rankQ_leaf_le (k : α) (entries : List (α × β)) :
    (rankQ k (.leaf entries)).countQueries oracle ≤ entries.length := by
  simpa [rankQ, rankM] using countQueries_scan_rankM_le oracle k entries

/-- Predecessor search in a leaf makes at most one comparison per entry. -/
theorem countQueries_predQ_leaf_le (k : α) (entries : List (α × β)) :
    (predQ k (.leaf entries)).countQueries oracle ≤ entries.length := by
  simpa [predQ, predM] using countQueries_scan_predM_le oracle k entries

/-- Successor search in a leaf makes at most one comparison per entry. -/
theorem countQueries_succQ_leaf_le (k : α) (entries : List (α × β)) :
    (succQ k (.leaf entries)).countQueries oracle ≤ entries.length := by
  simpa [succQ, succM] using countQueries_scan_succM_le oracle k entries

private theorem countQueries_node_le_of_step {f : BPlusTree α β → ℕ}
    (hnil : ∀ first, f (node first []) = f first)
    (hcons : ∀ first s c rest,
      f (node first ((s, c) :: rest)) ≤ 1 + max (f first) (f (node c rest)))
    (first : BPlusTree α β) (rest : List (Branch α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, f c ≤ B) :
    f (node first rest) ≤ rest.length + B := by
  induction rest generalizing first with
  | nil => have := hB first List.mem_cons_self; rw [hnil]; omega
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    have := hcons first s c rest
    have := hB first List.mem_cons_self
    have := ih c fun c' hc' => hB c' (List.mem_cons_of_mem _ hc')
    simp only [List.length_cons] at this ⊢
    omega

/-- Lookup at a node makes at most one comparison per separator beyond what it makes in the
child it descends into. -/
theorem countQueries_lookupQ_node_le (k : α) (first : BPlusTree α β)
    (rest : List (Branch α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (lookupQ k c).countQueries oracle ≤ B) :
    (lookupQ k (node first rest)).countQueries oracle ≤ rest.length + B :=
  countQueries_node_le_of_step (fun _ => by simp [lookupQ, lookupM])
    (fun _ s _ _ => by
      by_cases h : oracle (.le s k) = true <;> simp [lookupQ, lookupM, h])
    first rest hB

/-- Predecessor search at a node makes at most one comparison per separator beyond what it makes
in the child it descends into: the sibling fallback is a maximum search, which asks nothing. -/
theorem countQueries_predQ_node_le (k : α) (first : BPlusTree α β)
    (rest : List (Branch α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (predQ k c).countQueries oracle ≤ B) :
    (predQ k (node first rest)).countQueries oracle ≤ rest.length + B :=
  countQueries_node_le_of_step (fun _ => by simp [predQ, predM])
    (fun _ s _ _ => by
      by_cases h : oracle (.le s k) = true <;> simp [predQ, predM, h, ← maxQ_def])
    first rest hB

/-- Successor search at a node makes at most one comparison per separator beyond what it makes
in the child it descends into: the sibling fallback is a minimum search, which asks nothing. -/
theorem countQueries_succQ_node_le (k : α) (first : BPlusTree α β)
    (rest : List (Branch α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (succQ k c).countQueries oracle ≤ B) :
    (succQ k (node first rest)).countQueries oracle ≤ rest.length + B :=
  countQueries_node_le_of_step (fun _ => by simp [succQ, succM])
    (fun _ s _ _ => by
      by_cases h : oracle (.le s k) = true <;> simp [succQ, succM, h, ← minQ_def])
    first rest hB

/-- Rank at a node makes at most one comparison per separator beyond what it makes in the child
it descends into. -/
theorem countQueries_rankQ_node_le (k : α) (first : BPlusTree α β)
    (rest : List (Branch α β)) {B : ℕ}
    (hB : ∀ c ∈ (node first rest).children, (rankQ k c).countQueries oracle ≤ B) :
    (rankQ k (node first rest)).countQueries oracle ≤ rest.length + B :=
  countQueries_node_le_of_step (fun _ => by simp [rankQ, rankM])
    (fun _ s _ _ => by
      by_cases h : oracle (.le s k) = true <;> simp [rankQ, rankM, h])
    first rest hB

/-! ### Comparison bounds -/

section Bounds

variable [LinearOrder α]

/-- Lookup in a well-formed tree makes at most `2 * t - 1` comparisons per level and one more,
under every oracle. -/
theorem countQueries_lookupQ_le (h : IsWF t tr) (k : α) :
    (lookupQ k tr).countQueries oracle ≤ (2 * t - 1) * tr.height + 1 :=
  le_mul_height_add_of_scan (countQueries_lookupQ_leaf_le oracle k)
    (fun _ _ _ => countQueries_lookupQ_node_le oracle k _ _) h.width_le h.occupied_of_mem_children

/-- The membership test in a well-formed tree makes at most `2 * t - 1` comparisons per level and
one more, under every oracle. -/
theorem countQueries_containsQ_le (h : IsWF t tr) (k : α) :
    (containsQ k tr).countQueries oracle ≤ (2 * t - 1) * tr.height + 1 := by
  rw [countQueries_containsQ]
  exact countQueries_lookupQ_le oracle h k

/-- Predecessor search in a well-formed tree makes at most `2 * t - 1` comparisons per level,
under every oracle. -/
theorem countQueries_predQ_le (h : IsWF t tr) (k : α) :
    (predQ k tr).countQueries oracle ≤ (2 * t - 1) * tr.height :=
  le_mul_height_add_of_scan (c := 0) (countQueries_predQ_leaf_le oracle k)
    (fun _ _ _ => countQueries_predQ_node_le oracle k _ _) h.width_le h.occupied_of_mem_children

/-- Successor search in a well-formed tree makes at most `2 * t - 1` comparisons per level,
under every oracle. -/
theorem countQueries_succQ_le (h : IsWF t tr) (k : α) :
    (succQ k tr).countQueries oracle ≤ (2 * t - 1) * tr.height :=
  le_mul_height_add_of_scan (c := 0) (countQueries_succQ_leaf_le oracle k)
    (fun _ _ _ => countQueries_succQ_node_le oracle k _ _) h.width_le h.occupied_of_mem_children

/-- Rank in a well-formed tree makes at most `2 * t - 1` comparisons per level, under every
oracle. -/
theorem countQueries_rankQ_le (h : IsWF t tr) (k : α) :
    (rankQ k tr).countQueries oracle ≤ (2 * t - 1) * tr.height :=
  le_mul_height_add_of_scan (c := 0) (countQueries_rankQ_leaf_le oracle k)
    (fun _ _ _ => countQueries_rankQ_node_le oracle k _ _) h.width_le h.occupied_of_mem_children

end Bounds

end Comparisons

end Cslib.DataStructure.BPlusTree
