/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.Comparisons.Query

/-!
# B+-tree comparison cost examples

Checked examples for the comparison counts of the point queries of
`Cslib.DataStructure.BPlusTree`: values and the transfer lemmas under the order's oracle; counts
on a tree where the lookup and rank bounds are attained, on a root that is a leaf, on a node
with no separators, on a predecessor search that takes the sibling fallback, and under two
oracles that are not orders; and the bounds applied to a well-formed tree.
-/

public section

namespace CslibFrontierTests.BPlusTreeComparisons

open Cslib
open Cslib.DataStructure Cslib.DataStructure.BPlusTree
open Cslib.Query (LEQuery UpperBound)
open Cslib.SortedAssoc (leI)

/-- Height `2` at `t = 2`, full along its rightmost path: three separators, a last leaf of three
entries. -/
def full : BPlusTree ℕ String :=
  .node (.leaf [(1, "a")])
    [(2, .leaf [(2, "b")]), (3, .leaf [(3, "c")]), (4, .leaf [(4, "d"), (5, "e"), (6, "f")])]

/-- Height `3` at `t = 2`. The key `4` is absent. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

/-- The separator `2` is not a key, as after erasing `2`. -/
def gap : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(3, "c")])]

theorem isWF_full : IsWF 2 full := by decide
theorem isWF_twoLevels : IsWF 2 twoLevels := by decide
theorem isWF_gap : IsWF 2 gap := by decide

/-! ### Values under the order's oracle -/

example : (lookupQ 6 full).eval BTree.orderOracle = some "f" := by
  simp [full, lookup_leaf, SortedAssoc.lookupM, leI]

/-- A separator that is not a key does not end the search. -/
example : (lookupQ 2 gap).eval BTree.orderOracle = none := by
  simp [gap, lookup_leaf, SortedAssoc.lookupM, leI]

example : (containsQ 4 twoLevels).eval BTree.orderOracle = false := by
  simp [twoLevels, lookup_leaf, SortedAssoc.lookupM, leI]

example : (minQ full).eval BTree.orderOracle = some (1, "a") := by simp [full]

example : (maxQ full).eval BTree.orderOracle = some (6, "f") := by simp [full]

/-- The sibling fallback: the search for `3` ends in the first leaf of the second subtree. -/
example : (predQ 3 twoLevels).eval BTree.orderOracle = some (2, "b") := by
  simp [twoLevels, pred?_leaf, SortedAssoc.predM, leI]

example : (succQ 2 gap).eval BTree.orderOracle = some (3, "c") := by
  simp [gap, succ?_leaf, SortedAssoc.succM, leI]

example : (rankQ 7 full).eval BTree.orderOracle = 6 := by
  simp [full, rank_leaf, SortedAssoc.rankM, leI]

/-! ### The transfer lemmas -/

example : (lookupQ 2 gap).eval BTree.orderOracle = lookup 2 gap := eval_lookupQ 2

example : (containsQ 4 twoLevels).eval BTree.orderOracle = contains 4 twoLevels :=
  eval_containsQ 4

example (oracle : {ι : Type} → LEQuery ℕ ι → ι) : (minQ full).eval oracle = min? full :=
  eval_minQ oracle

example (oracle : {ι : Type} → LEQuery ℕ ι → ι) : (maxQ full).eval oracle = max? full :=
  eval_maxQ oracle

example : (predQ 3 twoLevels).eval BTree.orderOracle = pred? 3 twoLevels := eval_predQ 3

example : (succQ 2 gap).eval BTree.orderOracle = succ? 2 gap := eval_succQ 2

example : (rankQ 7 full).eval BTree.orderOracle = rank 7 full := eval_rankQ 7

/-! ### Comparison counts -/

/-- The constantly true oracle, which is not the oracle of an order on `ℕ`. -/
def trueOracle : {ι : Type} → LEQuery ℕ ι → ι := LEQuery.oracleOf fun _ _ => true

/-- The constantly false oracle, which is not the oracle of an order on `ℕ`. -/
def falseOracle : {ι : Type} → LEQuery ℕ ι → ι := LEQuery.oracleOf fun _ _ => false

/-- Looking up the greatest key of `full` passes three separators, scans the three entries of the
last leaf and tests the last of them for equality. -/
example : (lookupQ 6 full).countQueries BTree.orderOracle = 7 := by
  simp [full, lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- The lookup bound is attained. -/
example : (lookupQ 6 full).countQueries BTree.orderOracle = (2 * 2 - 1) * full.height + 1 := by
  simp [full, lookupQ_def, lookupM, SortedAssoc.lookupM, heightRest]

example : (rankQ 7 full).countQueries BTree.orderOracle = 6 := by
  simp [full, rankQ_def, rankM, SortedAssoc.rankM]

/-- The rank bound is attained. -/
example : (rankQ 7 full).countQueries BTree.orderOracle = (2 * 2 - 1) * full.height := by
  simp [full, rankQ_def, rankM, SortedAssoc.rankM, heightRest]

example : (predQ 7 full).countQueries BTree.orderOracle = 6 := by
  simp [full, predQ_def, predM, SortedAssoc.predM]

example : (succQ 7 full).countQueries BTree.orderOracle = 6 := by
  simp [full, succQ_def, succM, SortedAssoc.succM]

example : (lookupQ 6 twoLevels).countQueries BTree.orderOracle = 5 := by
  simp [twoLevels, lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- The search for `3` takes the sibling fallback, which asks nothing: the count is that of the
descent. -/
example : (predQ 3 twoLevels).countQueries BTree.orderOracle = 3 := by
  simp [twoLevels, predQ_def, predM, SortedAssoc.predM, ← maxQ_def]

example : (lookupQ 2 gap).countQueries BTree.orderOracle = 3 := by
  simp [gap, lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- Under an oracle that is not an order the value is wrong, but the count stays within the
bound. -/
example : (lookupQ 6 full).countQueries trueOracle = 5 := by
  simp [full, lookupQ_def, lookupM, SortedAssoc.lookupM, trueOracle]

example : (lookupQ 6 full).countQueries falseOracle = 2 := by
  simp [full, lookupQ_def, lookupM, SortedAssoc.lookupM, falseOracle]

example : (minQ full).countQueries falseOracle = 0 ∧ (maxQ full).countQueries falseOracle = 0 := by
  simp

/-- A root that is an empty leaf asks nothing. -/
example : (lookupQ 1 (.leaf [] : BPlusTree ℕ String)).countQueries trueOracle = 0 := by
  simp [lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- A root that is a leaf. -/
example :
    (lookupQ 1 (.leaf [(1, "a")] : BPlusTree ℕ String)).countQueries BTree.orderOracle = 2 := by
  simp [lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- A node with no separators, which is not well-formed, costs what its only child costs. -/
example :
    (lookupQ 1 (.node (.leaf [(1, "a")]) [] : BPlusTree ℕ String)).countQueries
      BTree.orderOracle = 2 := by
  simp [lookupQ_def, lookupM, SortedAssoc.lookupM]

/-- The bounds applied to a well-formed tree, under every oracle and for every key. -/
example (oracle : {ι : Type} → LEQuery ℕ ι → ι) (k : ℕ) :
    (lookupQ k full).countQueries oracle ≤ 7 :=
  countQueries_lookupQ_le oracle isWF_full k

example (oracle : {ι : Type} → LEQuery ℕ ι → ι) (k : ℕ) :
    (rankQ k full).countQueries oracle ≤ 6 :=
  countQueries_rankQ_le oracle isWF_full k

/-! ### Upper bounds over all oracles -/

/-- At `t = 2`, lookup asks at most `3 * height + 1` comparisons. -/
example :
    UpperBound (fun p : WFInput ℕ String 2 => lookupQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 3 * h + 1) :=
  lookupQ_upperBound

/-- At `t = 2`, rank asks at most `3 * height` comparisons. -/
example :
    UpperBound (fun p : WFInput ℕ String 2 => rankQ p.val.2 p.val.1) (fun p => p.val.1.height)
      (fun h => 3 * h) :=
  rankQ_upperBound

end CslibFrontierTests.BPlusTreeComparisons
