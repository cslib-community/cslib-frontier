/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.TreeMap

/-!
# B+-tree bulk loading examples

Checked examples for bulk loading of `Cslib.DataStructure.BPlusTree`: the sizes of the leaves,
loads of one, two and three levels at minimum degree `2` and of two levels at minimum degree `3`,
the empty list, minimum degrees below `2`, a list that is not sorted, and the two output bridges.
-/

public section

namespace CslibFrontierTests.BPlusTreeBulk

open Cslib Cslib.DataStructure Cslib.DataStructure.BPlusTree

/-- The sorted list with keys `1` to `n`. -/
def unit (n : ℕ) : List (ℕ × Unit) := (List.range n).map fun i => (i + 1, ())

/-! ### Leaf sizes -/

example : chunkSizes 2 4 4 = [3, 1] := by decide
example : chunkSizes 2 7 7 = [3, 3, 1] := by decide
example : chunkSizes 3 6 6 = [2, 4] := by decide
example : chunkSizes 3 7 7 = [5, 2] := by decide

/-! ### Loads -/

example : ofSortedList 2 ([] : List (ℕ × Unit)) = .leaf [] := rfl
example : ofSortedList 5 ([] : List (ℕ × Unit)) = .leaf [] := rfl
example : (ofSortedList 2 (unit 3)).height = 1 := by decide
example :
    (ofSortedList 2 (unit 7)).leaves = [unit 3, (unit 6).drop 3, (unit 7).drop 6] := by decide
example : (ofSortedList 2 (unit 7)).height = 2 := by decide
example : (ofSortedList 2 (unit 13)).leaves.map List.length = [3, 3, 3, 3, 1] := by decide
example : (ofSortedList 2 (unit 13)).height = 3 := by decide
/-- The root of the three-level load holds one separator. -/
example : (ofSortedList 2 (unit 13)).width = 1 := by decide
example : IsWF 2 (ofSortedList 2 (unit 13)) := by decide
example : IsWF 3 (ofSortedList 3 (unit 13)) := by decide

/-- Below `2` the loader uses minimum degree `2`. -/
example (l : List (ℕ × Unit)) : ofSortedList 0 l = ofSortedList 2 l := rfl
example (l : List (ℕ × Unit)) : ofSortedList 1 l = ofSortedList 2 l := rfl

/-- Every list keeps its entries, sorted or not. -/
example :
    (ofSortedList 2 [(3, ()), (1, ()), (3, ()), (2, ())]).toList =
      [(3, ()), (1, ()), (3, ()), (2, ())] := by
  decide

/-! ### Theorem instances -/

theorem isSortedAssoc_unit_seven : (unit 7).IsSortedAssoc := by decide

example : IsWF 2 (ofSortedList 2 (unit 7)) := isWF_ofSortedList le_rfl isSortedAssoc_unit_seven

/-- The height bound depends on the shape only, so it needs no sortedness. -/
example : (ofSortedList 2 (unit 7).reverse).height ≤ Nat.log 2 (unit 7).reverse.length + 1 :=
  height_ofSortedList_le le_rfl _

/-- Lookup needs no bound on the minimum degree. -/
example : lookup 4 (ofSortedList 0 (unit 7)) = (unit 7).lookup 4 :=
  lookup_ofSortedList isSortedAssoc_unit_seven 4

/-! ### Bridges -/

example : (ofSortedList 2 (unit 7)).toList = (BTree.ofSortedList 2 (unit 7)).toList := by decide

example : (ofSortedList 2 (unit 7)).toList = (BTree.ofSortedList 2 (unit 7)).toList :=
  toList_ofSortedList_eq_btree 2 (unit 7)

example : (ofSortedList 2 (unit 7)).toList = (Std.TreeMap.ofList (unit 7) compare).toList :=
  toList_ofSortedList_eq_treeMap 2 isSortedAssoc_unit_seven

end CslibFrontierTests.BPlusTreeBulk
