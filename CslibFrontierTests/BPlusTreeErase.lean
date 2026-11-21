/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.Erase.MinMax

/-!
# B+-tree erasure examples

Checked examples for erasure from `Cslib.DataStructure.BPlusTree`: an erased key that stays as a
separator, the empty tree, absent keys, minimum degrees below `2`, a leaf merge, a merge that
splits again, an interior merge, a root collapse, and the removal of the least and greatest
entries.
-/

public section

namespace CslibFrontierTests.BPlusTreeErase

open Cslib Cslib.DataStructure Cslib.DataStructure.BPlusTree

/-- A tree of height `3` at `t = 2`: four leaves under two interior nodes. The key `4` is
absent. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

/-- A tree whose separator `2` is not a key. -/
def gap : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(3, "c")])]

/-- Two leaves at minimum occupancy for `t = 2`. -/
def pair : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])]

/-- The roadmap's tree: the separator `2` is the first key of the second leaf. -/
def sep : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(2, "b"), (3, "c")])]

/-- A leaf at minimum occupancy beside a full leaf, at `t = 3`. -/
def lop : BPlusTree ℕ String :=
  .node (.leaf [(1, "a"), (2, "b")])
    [(3, .leaf [(3, "c"), (4, "d"), (5, "e"), (6, "f"), (7, "g")])]

private theorem isWF_twoLevels : IsWF 2 twoLevels := by decide

/-! ### An erased key that stays as a separator -/

/-- The roadmap's example: erasing `2` leaves `2` as a separator, and the tree is well-formed. -/
example : (erase 2 2 sep).toList = [(1, "a"), (3, "c")] ∧ IsWF 2 (erase 2 2 sep) := by decide

example : ∃ l r, erase 2 2 sep = .node l [(2, r)] := ⟨_, _, rfl⟩

example : lookup 2 (erase 2 2 sep) = none := by
  rw [lookup_eq (t := 2) (by decide)]
  decide

/-! ### The empty tree, absent keys and small minimum degrees -/

/-- Erasure from the empty tree is the empty tree. -/
example : (erase 2 1 (.leaf [] : BPlusTree ℕ String)).leaves = [[]] := by decide

/-- Erasing an absent key changes nothing. -/
example : (erase 2 4 twoLevels).leaves = twoLevels.leaves ∧ IsWF 2 (erase 2 4 twoLevels) := by
  decide

/-- Below minimum degree `2` erasure still evaluates and removes the entry. -/
example : (erase 0 1 pair).toList = [(2, "b")] := by decide

/-- A key equal to a separator that is not a key is absent. -/
example : (erase 2 2 gap).leaves = gap.leaves := by decide

/-! ### Repairs -/

/-- The first leaf empties and merges with its right sibling; the root collapses. -/
example : (erase 2 1 pair).leaves = [[(2, "b")]] ∧ (erase 2 1 pair).height = 1 := by decide

/-- The last leaf empties and is repaired against its left sibling. -/
example : (erase 2 2 pair).leaves = [[(1, "a")]] := by decide

example : IsWF 3 lop := by decide

/-- A merge that splits again at `t = 3`: `1 + 5` entries become `3` and `3`, under the new
separator `5`. -/
example :
    (erase 3 1 lop).leaves = [[(2, "b"), (3, "c"), (4, "d")], [(5, "e"), (6, "f"), (7, "g")]] ∧
      IsWF 3 (erase 3 1 lop) := by
  decide

example : ∃ l r, erase 3 1 lop = .node l [(5, r)] := ⟨_, _, rfl⟩

/-- A leaf merge, then an interior merge that pulls the separator `3` down, then a root
collapse. -/
example :
    (erase 2 1 twoLevels).leaves = [[(2, "b")], [(3, "c")], [(5, "e"), (6, "f")]] ∧
      (erase 2 1 twoLevels).height = 2 ∧ IsWF 2 (erase 2 1 twoLevels) := by
  decide

/-! ### The least and greatest entries -/

example : eraseMin? 2 (.leaf [] : BPlusTree ℕ String) = none := by decide

example : eraseMax? 2 (.leaf [] : BPlusTree ℕ String) = none := by
  simp [eraseMax?_eq_map_max?]

example : (eraseMin? 2 gap).map (fun p => (p.1, p.2.toList)) = some ((1, "a"), [(3, "c")]) := by
  decide

example : (eraseMax? 2 gap).map (fun p => (p.1, p.2.toList)) = some ((3, "c"), [(1, "a")]) := by
  have h : max? gap = some (3, "c") := by simp [gap]
  rw [eraseMax?_eq_map_max?, h]
  decide

end CslibFrontierTests.BPlusTreeErase
