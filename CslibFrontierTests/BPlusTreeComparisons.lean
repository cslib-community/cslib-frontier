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

end CslibFrontierTests.BPlusTreeComparisons
