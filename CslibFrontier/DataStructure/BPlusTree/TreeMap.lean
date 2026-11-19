/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.OfSortedList
public import CslibFrontier.Foundations.Data.TreeMap.SortedAssoc

/-!
# Bulk loading of B+-trees, `Std.TreeMap` and classic B-trees

The output of bulk loading a B+-tree agrees with two other ordered maps built from the same
list. On a sorted list `l`, the entries of Lean core's `Std.TreeMap.ofList l compare`, ordered by
the `compare` of the linear order, are `l` itself (`Std.TreeMap.toList_ofList_of_isSortedAssoc`).
On every list, the entries of the classic B-tree `Cslib.DataStructure.BTree.ofSortedList t l` are
`l`. So are those of the B+-tree, by `toList_ofSortedList`.

## Main results

* `toList_ofSortedList_eq_treeMap`: bulk loading a sorted list gives the entries of the tree map
  built from it, for every minimum degree.
* `toList_ofSortedList_eq_btree`: bulk loading gives the entries of the classic B-tree loaded
  from the same list, for every list and every minimum degree.
-/

public section

variable {α β : Type}

namespace Cslib.DataStructure.BPlusTree

/-- Bulk loading a sorted list gives the entries of Lean core's tree map built from it: an output
equality, for every minimum degree. -/
theorem toList_ofSortedList_eq_treeMap [LinearOrder α] (t : ℕ) {l : List (α × β)}
    (h : l.IsSortedAssoc) : (ofSortedList t l).toList = (Std.TreeMap.ofList l compare).toList :=
  (toList_ofSortedList t l).trans (Std.TreeMap.toList_ofList_of_isSortedAssoc h).symm

/-- Bulk loading gives the entries of the classic B-tree loaded from the same list: an output
equality, for every list and every minimum degree. -/
theorem toList_ofSortedList_eq_btree (t : ℕ) (l : List (α × β)) :
    (ofSortedList t l).toList = (BTree.ofSortedList t l).toList :=
  (toList_ofSortedList t l).trans (BTree.toList_ofSortedList t l).symm

end Cslib.DataStructure.BPlusTree
