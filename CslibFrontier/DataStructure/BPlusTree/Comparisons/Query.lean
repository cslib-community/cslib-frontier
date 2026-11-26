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

end Comparisons

end Cslib.DataStructure.BPlusTree
