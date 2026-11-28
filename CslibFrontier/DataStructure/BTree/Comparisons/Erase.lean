/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import CslibFrontier.DataStructure.BTree.Erase.MinMax

/-!
# Comparison costs of B-tree erasure

`eraseQ`, `eraseMinQ` and `eraseMaxQ` instantiate `eraseM`, `eraseMinM` and `eraseMaxM` at
`FreeM (LEQuery α)` with the query interface `LEQuery.ask` and `visit := pure ()`, in the
comparison-query model of `Cslib.DataStructure.BTree.Comparisons.Query`.

Erasure compares keys only while it scans the nodes of its search path, one node per level: at
most one comparison per triple passed and a second at the triple where the scan stops, so at most
`rest.length + 1` at a node. Everything else it does is free of comparisons. The repairs
`rebalanceRightM` and `rebalanceLastM` and the removal `popMinM` of the successor of an interior
key take no comparator, and neither do `minM` and `maxM`, which find the entry that `eraseMinM`
and `eraseMaxM` remove. The comparison bound of all three operations is therefore that of
insertion, `2 * t * height`, and not the node-visit counts `2 * height` and `3 * height`
times the per-node bound `2 * t`: the siblings that a
repair visits, the path to the successor and the pass to the extreme entry are visited without
comparing keys.

The bounds hold under every oracle, but only on well-formed trees: a node of a raw tree may hold
more than `2 * t - 1` keys.

## Main definitions

* `eraseQ`, `eraseMinQ`, `eraseMaxQ`: the instrumented erasures.

## Main results

* `eval_eraseQ`, `eval_eraseMinQ`, `eval_eraseMaxQ`: the values under `orderOracle` are `erase`,
  `eraseMin?` and `eraseMax?`.
* `countQueries_eraseQ_le`, `countQueries_eraseMinQ_le`, `countQueries_eraseMaxQ_le`: at most
  `2 * t * height` comparisons on a well-formed tree, under any oracle.
* `countQueries_eraseQ_le_log`, `countQueries_eraseMinQ_le_log`, `countQueries_eraseMaxQ_le_log`:
  with `IsWF.height_le_log`.
* `eraseQ_upperBound`, `eraseMinQ_upperBound`, `eraseMaxQ_upperBound`: the `UpperBound`
  packaging.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
* [N. Mündler, *A Verified Imperative Implementation of B-Trees*][Mundler2021]
-/

public section

open Cslib (FreeM)
open Cslib.Query (LEQuery UpperBound)

namespace Cslib.DataStructure.BTree

open Cslib.SortedAssoc (leI)

variable {α β : Type} {t : ℕ} {k : α} {tr : BTree α β}

/-- Erasure, counting comparisons. -/
def eraseQ (t : ℕ) (k : α) (tr : BTree α β) : FreeM (LEQuery α) (BTree α β) :=
  eraseM t LEQuery.ask (pure ()) k tr

/-- `eraseQ` is `eraseM` with `LEQuery.ask` and free visits. -/
theorem eraseQ_def : eraseQ t k tr = eraseM t LEQuery.ask (pure ()) k tr := (rfl)

/-- Removal of the least entry, counting comparisons. -/
def eraseMinQ (t : ℕ) (tr : BTree α β) : FreeM (LEQuery α) (Option ((α × β) × BTree α β)) :=
  eraseMinM t LEQuery.ask (pure ()) tr

/-- `eraseMinQ` is `eraseMinM` with `LEQuery.ask` and free visits. -/
theorem eraseMinQ_def : eraseMinQ t tr = eraseMinM t LEQuery.ask (pure ()) tr := (rfl)

/-- Removal of the greatest entry, counting comparisons. -/
def eraseMaxQ (t : ℕ) (tr : BTree α β) : FreeM (LEQuery α) (Option ((α × β) × BTree α β)) :=
  eraseMaxM t LEQuery.ask (pure ()) tr

/-- `eraseMaxQ` is `eraseMaxM` with `LEQuery.ask` and free visits. -/
theorem eraseMaxQ_def : eraseMaxQ t tr = eraseMaxM t LEQuery.ask (pure ()) tr := (rfl)

section Transfer

variable [LinearOrder α]

/-- Under the order's oracle, `eraseQ` evaluates to the pure erasure `erase`. -/
@[simp] theorem eval_eraseQ : (eraseQ t k tr).eval orderOracle = erase t k tr := by
  simpa [erase_def, eraseQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_eraseM t LEQuery.ask (pure ()) k tr)

/-- Under the order's oracle, `eraseMinQ` evaluates to `eraseMin?`. -/
@[simp] theorem eval_eraseMinQ : (eraseMinQ t tr).eval orderOracle = eraseMin? t tr := by
  simpa [eraseMin?_def, eraseMinQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_eraseMinM t LEQuery.ask (pure ()) tr)

/-- Under the order's oracle, `eraseMaxQ` evaluates to `eraseMax?`. -/
@[simp] theorem eval_eraseMaxQ : (eraseMaxQ t tr).eval orderOracle = eraseMax? t tr := by
  simpa [eraseMax?_def, eraseMaxQ, leI] using
    Id.ext_iff.1
      ((FreeM.isMonadHom_pure_eval orderOracle).map_eraseMaxM t LEQuery.ask (pure ()) tr)

end Transfer

section Counts

variable (oracle : {ι : Type} → LEQuery α ι → ι)

/-- A repair against the right sibling compares no keys. -/
private theorem countQueries_rebalanceRightM (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) :
    (rebalanceRightM t (pure () : FreeM (LEQuery α) Unit) c k v s rest).countQueries oracle
      = 0 := by
  rw [rebalanceRightM_def]
  split <;> simp

/-- A repair against the left sibling compares no keys. -/
private theorem countQueries_rebalanceLastM (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    (rebalanceLastM t (pure () : FreeM (LEQuery α) Unit) prev k v c).countQueries oracle = 0 := by
  rw [rebalanceLastM_def]
  split <;> simp

/-- Removing the least entry of a subtree compares no keys. -/
private theorem countQueries_popMinM (tr : BTree α β) :
    (popMinM t (pure () : FreeM (LEQuery α) Unit) tr).countQueries oracle = 0 := by
  match tr with
  | .leaf => simp
  | .node first rest =>
    simp only [popMinM_node, FreeM.countQueries_bind, FreeM.countQueries_pure,
      countQueries_popMinM first, zero_add]
    split <;> simp [countQueries_rebalanceRightM]
termination_by sizeOf tr

/-- The scan of a node's triples makes one comparison per triple passed and at most two where it
stops, and erases from at most one child: at most `rest.length + 1` comparisons beyond a bound
`B` on the erasure from each child. -/
private theorem countQueries_eraseRestM_le (k : α) (B : ℕ) (rest : List (Triple α β))
    (prev : BTree α β) (prevErased : Unit → FreeM (LEQuery α) (BTree α β))
    (hpe : (prevErased ()).countQueries oracle ≤ B)
    (hc : ∀ e ∈ rest,
      (eraseSubtreeM t LEQuery.ask (pure ()) k e.child).countQueries oracle ≤ B) :
    (eraseRestM t LEQuery.ask (pure ()) k prev prevErased rest).countQueries oracle
      ≤ rest.length + 1 + B := by
  induction rest generalizing prev prevErased with
  | nil =>
    simp only [eraseRestM_nil, bind_pure_comp, FreeM.countQueries_map, List.length_nil]; omega
  | cons head tail ih =>
    obtain ⟨k', v', c⟩ := head
    have hcc : (eraseSubtreeM t LEQuery.ask (pure ()) k c).countQueries oracle ≤ B :=
      hc (k', v', c) List.mem_cons_self
    rw [eraseRestM_cons]
    by_cases hk : oracle (LEQuery.le k k') = true
    · by_cases hk' : oracle (LEQuery.le k' k) = true
      · simp only [LEQuery.ask, FreeM.countQueries_bind, FreeM.countQueries_lift,
          FreeM.eval_lift, hk, hk', ↓reduceIte, countQueries_popMinM, List.length_cons]
        split
        · simp; omega
        · split <;> simp [countQueries_rebalanceLastM, countQueries_rebalanceRightM]
          omega
      · simp [LEQuery.ask, hk, hk', countQueries_rebalanceRightM]; omega
    · cases tail with
      | nil => simp [LEQuery.ask, hk, countQueries_rebalanceLastM]; omega
      | cons e tail' =>
        have := ih c (fun _ => eraseSubtreeM t LEQuery.ask (pure ()) k c) hcc
          fun e he => hc e (List.mem_cons_of_mem _ he)
        simp only [List.length_cons] at this
        simp [LEQuery.ask, hk]; omega

/-- Erasure from the empty tree makes no comparisons. -/
@[simp] theorem countQueries_eraseQ_leaf :
    (eraseQ t k (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [eraseQ]

/-- Removing the least entry of the empty tree makes no comparisons. -/
@[simp] theorem countQueries_eraseMinQ_leaf :
    (eraseMinQ t (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [eraseMinQ]

/-- Removing the greatest entry of the empty tree makes no comparisons. -/
@[simp] theorem countQueries_eraseMaxQ_leaf :
    (eraseMaxQ t (.leaf : BTree α β)).countQueries oracle = 0 := by
  simp [eraseMaxQ]

variable [LinearOrder α]

/-- Erasure from a subtree of a well-formed tree makes at most `2 * t` comparisons per level. -/
private theorem countQueries_eraseSubtreeM_le (h : IsWF t tr) :
    (eraseSubtreeM t LEQuery.ask (pure ()) k tr).countQueries oracle ≤ 2 * t * tr.height :=
  le_mul_height_of_scan
    (f := fun c => (eraseSubtreeM t LEQuery.ask (pure ()) k c).countQueries oracle)
    (by have := h.two_le; omega) (by simp)
    (fun first rest B hB => by
      have := countQueries_eraseRestM_le oracle k B rest first
        (fun _ => eraseSubtreeM t LEQuery.ask (pure ()) k first) (hB first (by simp [children]))
        fun e he => hB e.child (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
      simp only [eraseSubtreeM_node, FreeM.countQueries_bind, FreeM.countQueries_pure]
      omega)
    h.rootKeys_le h.occupied_of_mem_children

/-- Erasure makes at most `2 * t * height` comparisons: it scans one node per level, and its
repairs and the removal of a successor compare no keys. -/
theorem countQueries_eraseQ_le (h : IsWF t tr) :
    (eraseQ t k tr).countQueries oracle ≤ 2 * t * tr.height := by
  simpa [eraseQ, eraseM_def] using countQueries_eraseSubtreeM_le (k := k) oracle h

/-- Removing the least entry makes at most `2 * t * height` comparisons: finding it makes none,
and the rest is the erasure of its key. -/
theorem countQueries_eraseMinQ_le (h : IsWF t tr) :
    (eraseMinQ t tr).countQueries oracle ≤ 2 * t * tr.height := by
  have h₀ := countQueries_minQ (oracle := oracle) tr
  have h₁ := eval_minQ (tr := tr) oracle
  rw [minQ_def] at h₀ h₁
  simp only [eraseMinQ, eraseMinM_def, FreeM.countQueries_bind, h₀, h₁, zero_add]
  cases min? tr with
  | none => simp
  | some p => simpa [eraseQ] using countQueries_eraseQ_le (k := p.1) oracle h

/-- Removing the greatest entry makes at most `2 * t * height` comparisons: finding it makes
none, and the rest is the erasure of its key. -/
theorem countQueries_eraseMaxQ_le (h : IsWF t tr) :
    (eraseMaxQ t tr).countQueries oracle ≤ 2 * t * tr.height := by
  have h₀ := countQueries_maxQ (oracle := oracle) tr
  have h₁ := eval_maxQ (tr := tr) oracle
  rw [maxQ_def] at h₀ h₁
  simp only [eraseMaxQ, eraseMaxM_def, FreeM.countQueries_bind, h₀, h₁, zero_add]
  cases max? tr with
  | none => simp
  | some p => simpa [eraseQ] using countQueries_eraseQ_le (k := p.1) oracle h

/-- Erasure from a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_eraseQ_le_log (h : IsWF t tr) :
    (eraseQ t k tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_eraseQ_le oracle h).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Removing the least entry of a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_eraseMinQ_le_log (h : IsWF t tr) :
    (eraseMinQ t tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_eraseMinQ_le oracle h).trans (Nat.mul_le_mul_left _ h.height_le_log)

/-- Removing the greatest entry of a well-formed tree makes logarithmically many comparisons. -/
theorem countQueries_eraseMaxQ_le_log (h : IsWF t tr) :
    (eraseMaxQ t tr).countQueries oracle ≤ 2 * t * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (countQueries_eraseMaxQ_le oracle h).trans (Nat.mul_le_mul_left _ h.height_le_log)

end Counts

section Bounds

variable [LinearOrder α]

/-- `UpperBound` packaging for `eraseQ`, on well-formed trees. -/
theorem eraseQ_upperBound :
    UpperBound (fun p : WFInput α β t => eraseQ t p.val.2 p.val.1)
      (fun p => p.val.1.height) (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_eraseQ_le oracle p.property

/-- `UpperBound` packaging for `eraseMinQ`, on well-formed trees. -/
theorem eraseMinQ_upperBound :
    UpperBound (fun p : {tr : BTree α β // IsWF t tr} => eraseMinQ t p.val)
      (fun p => p.val.height) (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_eraseMinQ_le oracle p.property

/-- `UpperBound` packaging for `eraseMaxQ`, on well-formed trees. -/
theorem eraseMaxQ_upperBound :
    UpperBound (fun p : {tr : BTree α β // IsWF t tr} => eraseMaxQ t p.val)
      (fun p => p.val.height) (fun h => 2 * t * h) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.mul_le_mul_left _ h)
    fun oracle p => countQueries_eraseMaxQ_le oracle p.property

end Bounds

end Cslib.DataStructure.BTree
