/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.Range

/-!
# B+-tree range query examples

Checked examples for `Cslib.DataStructure.BPlusTree.range`: the query evaluated by its
constructor equations on a well-formed tree of height `3`, the model equation, and the
decomposition of the leaves into a prefix, a contributing run and a suffix.
-/

public section

namespace CslibFrontierTests.BPlusTreeRange

open Cslib Cslib.DataStructure Cslib.DataStructure.BPlusTree

open Cslib.SortedAssoc (leI)

/-- A tree of height `3` at `t = 2`: four leaves under two interior nodes. The key `4` is
absent. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

theorem isWF_twoLevels : IsWF 2 twoLevels := by decide

/-- An interval across the two subtrees of the root; its bounds are a key and an absent key. -/
example : range 2 4 twoLevels = [(2, "b"), (3, "c")] := by
  simp [twoLevels, range_node_cons, range_leaf, SortedAssoc.rangeM, SortedAssoc.takeUpToM, leI]

/-- An interval that ends inside the last leaf, and one that covers every key. -/
example :
    range 3 5 twoLevels = [(3, "c"), (5, "e")] ∧
      range 0 9 twoLevels = [(1, "a"), (2, "b"), (3, "c"), (5, "e"), (6, "f")] := by
  simp [twoLevels, range_node_cons, range_leaf, SortedAssoc.rangeM, SortedAssoc.takeUpToM, leI]

/-- An interval between two keys, an interval above every key, and an empty interval. -/
example : range 4 4 twoLevels = [] ∧ range 7 9 twoLevels = [] ∧ range 5 2 twoLevels = [] := by
  simp [twoLevels, range_node_cons, range_leaf, SortedAssoc.rangeM, SortedAssoc.takeUpToM, leI]

/-- The model equation applied to a well-formed tree. -/
example (lo hi : ℕ) : range lo hi twoLevels = SortedAssoc.range lo hi twoLevels.toList :=
  range_eq isWF_twoLevels lo hi

/-- The run of leaves behind `range 2 5`: the first leaf is left out, the leaves `[(2, "b")]` and
`[(3, "c")]` are returned whole, and the last leaf is cut at `5`. -/
example :
    twoLevels.leaves = [[(1, "a")]] ++ [[(2, "b")], [(3, "c")], [(5, "e"), (6, "f")]] ++ [] ∧
      ([[(2, "b")], [(3, "c")], [(5, "e"), (6, "f")]].map (SortedAssoc.range 2 5)).flatten =
        [(2, "b"), (3, "c"), (5, "e")] := by
  decide

/-- The decomposition exists for every interval. -/
example (lo hi : ℕ) :
    ∃ pre run post : List (List (ℕ × String)), twoLevels.leaves = pre ++ run ++ post ∧
      range lo hi twoLevels = (run.map (SortedAssoc.range lo hi)).flatten ∧
      (∀ l ∈ run, SortedAssoc.range lo hi l ≠ []) ∧
      ∀ l ∈ (run.drop 1).dropLast, SortedAssoc.range lo hi l = l :=
  range_eq_flatten_run isWF_twoLevels lo hi

/-- The empty tree has one leaf, which is empty, and an empty run. -/
example (lo hi : ℕ) : range lo hi (BPlusTree.leaf [] : BPlusTree ℕ String) = [] := by
  simp [range_leaf, SortedAssoc.rangeM]

end CslibFrontierTests.BPlusTreeRange
