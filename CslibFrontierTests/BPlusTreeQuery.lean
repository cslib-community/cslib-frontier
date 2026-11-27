/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.PredSucc
public import CslibFrontier.DataStructure.BPlusTree.Rank

/-!
# B+-tree point query examples

Checked examples for the point queries of `Cslib.DataStructure.BPlusTree`: the separator search,
lookup, membership, least and greatest entry, strict predecessor and successor, and rank. The
queries are evaluated by their constructor equations, on a well-formed tree of height `3`, and
on a tree with an empty child where lookup and the model disagree.
-/

public section

namespace CslibFrontierTests.BPlusTreeQuery

open Cslib Cslib.DataStructure Cslib.DataStructure.BPlusTree

open Cslib.SortedAssoc (leI)

/-- A tree of height `3` at `t = 2`: four leaves under two interior nodes. The key `4` is absent,
and the separators `2`, `3` and `5` are keys. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

/-- A tree whose separator `2` is not a key. -/
def gap : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(3, "c")])]

/-- A tree with an empty child. It satisfies the separator convention and its entries are sorted,
but it is not well-formed. -/
def hollow : BPlusTree ℕ String :=
  .node (.leaf [(1, "a")]) [(5, .leaf []), (3, .leaf [(3, "c")])]

theorem isWF_twoLevels : IsWF 2 twoLevels := by decide

/-! ### Separator search -/

/-- The search passes the separators that are at most the query, a separator equal to the query
included, and stops at the first one above it. -/
example :
    slot 0 [(2, gap), (4, gap), (6, gap)] = 0 ∧ slot 4 [(2, gap), (4, gap), (6, gap)] = 2 ∧
      slot 5 [(2, gap), (4, gap), (6, gap)] = 2 ∧ slot 9 [(2, gap), (4, gap), (6, gap)] = 3 := by
  simp

/-! ### Lookup and membership -/

/-- Lookup of keys in the first and the last leaf, of a key equal to a separator, and of an
absent key. -/
example :
    lookup 1 twoLevels = some "a" ∧ lookup 6 twoLevels = some "f" ∧
      lookup 3 twoLevels = some "c" ∧ lookup 4 twoLevels = none := by
  simp [twoLevels, lookup_leaf, SortedAssoc.lookupM, leI]

/-- A separator equal to the query does not end the search: separators are not entries. -/
example : lookup 2 gap = none ∧ lookup 3 gap = some "c" := by
  simp [gap, lookup_leaf, SortedAssoc.lookupM, leI]

example : contains 5 twoLevels = true ∧ contains 4 twoLevels = false := by
  simp [twoLevels, lookup_leaf, SortedAssoc.lookupM, leI]

/-- The model equation applied to a well-formed tree. -/
example (k : ℕ) : lookup k twoLevels = List.lookup k twoLevels.toList :=
  lookup_eq isWF_twoLevels k

/-- Occupancy matters to the model equation. `hollow` satisfies the separator convention and has
sorted entries, yet lookup misses the key `3`: the separator `5` introduces an empty child, so
nothing forces the keys after it to be at least `5`. -/
example :
    Separated hollow ∧ hollow.toList.IsSortedAssoc ∧ ¬ IsWF 2 hollow ∧
      List.lookup 3 hollow.toList = some "c" := by
  decide

example : lookup 3 hollow = none := by
  simp [hollow, lookup_leaf, SortedAssoc.lookupM, leI]

/-! ### Least and greatest entry -/

example : min? twoLevels = some (1, "a") ∧ max? twoLevels = some (6, "f") := by
  simp [twoLevels]

/-- The empty tree has neither. -/
example :
    min? (BPlusTree.leaf [] : BPlusTree ℕ String) = none ∧
      max? (BPlusTree.leaf [] : BPlusTree ℕ String) = none := by
  simp

/-- Without occupancy the walk can end in an empty leaf although the tree has entries. -/
example :
    max? (BPlusTree.node (α := ℕ) (β := String) (.leaf [(1, "a")]) [(2, .leaf [])]) = none := by
  simp

/-! ### Predecessor and successor -/

/-- Predecessors found in the leaf that the search reaches, and no predecessor of the least
key. -/
example : pred? 7 twoLevels = some (6, "f") ∧ pred? 6 twoLevels = some (5, "e") ∧
    pred? 1 twoLevels = none := by
  simp [twoLevels, pred?_leaf, SortedAssoc.predM, leI]

/-- The sibling fallback. The search for `5` ends in the leaf `[(5, "e"), (6, "f")]`, which has
no key below `5`; the answer is the last entry of the leaf before it, under the same parent. The
search for `3` ends in the leaf `[(3, "c")]`, the first leaf of the second subtree of the root;
the answer is the greatest entry of the first subtree. -/
example : pred? 5 twoLevels = some (3, "c") ∧ pred? 3 twoLevels = some (2, "b") := by
  simp [twoLevels, pred?_leaf, SortedAssoc.predM, leI]

/-- Successors found in the leaf that the search reaches, and no successor of the greatest
key. -/
example : succ? 0 twoLevels = some (1, "a") ∧ succ? 5 twoLevels = some (6, "f") ∧
    succ? 6 twoLevels = none := by
  simp [twoLevels, succ?_leaf, SortedAssoc.succM, leI]

/-- The sibling fallback. The search for `3` ends in the leaf `[(3, "c")]`, which has no key
above `3`; the answer is the first entry of the next leaf, under the same parent. The search for
`2` ends in the leaf `[(2, "b")]`, the last leaf of the first subtree of the root; the answer is
the least entry of the second subtree. -/
example : succ? 3 twoLevels = some (5, "e") ∧ succ? 2 twoLevels = some (3, "c") := by
  simp [twoLevels, succ?_leaf, SortedAssoc.succM, leI]

/-- The model equations applied to a well-formed tree. -/
example (k : ℕ) :
    pred? k twoLevels = SortedAssoc.pred? k twoLevels.toList ∧
      succ? k twoLevels = SortedAssoc.succ? k twoLevels.toList :=
  ⟨pred?_eq isWF_twoLevels k, succ?_eq isWF_twoLevels k⟩

/-! ### Rank -/

/-- The rank of a key counts the keys strictly below it; an absent key and a key above all
others are counted the same way. -/
example :
    rank 1 twoLevels = 0 ∧ rank 3 twoLevels = 2 ∧ rank 4 twoLevels = 3 ∧
      rank 9 twoLevels = 5 := by
  simp [twoLevels, rank_leaf, SortedAssoc.rankM, leI, size_node]

/-- The model equation applied to a well-formed tree. -/
example (k : ℕ) : rank k twoLevels = SortedAssoc.rank k twoLevels.toList :=
  rank_eq isWF_twoLevels k

end CslibFrontierTests.BPlusTreeQuery
