/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.Insert

/-!
# B+-tree insertion examples

Checked examples for insertion into `Cslib.DataStructure.BPlusTree`: the empty tree, minimum
degrees below `2`, a split of a root leaf, a replaced value, a key below the first separator, a
key equal to a separator that is not a key, and a leaf split that makes the root split.
-/

public section

namespace CslibFrontierTests.BPlusTreeInsert

open Cslib Cslib.DataStructure Cslib.DataStructure.BPlusTree

/-- A tree of height `3` at `t = 2`: four leaves under two interior nodes. The key `4` is
absent. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

/-- A tree whose separator `2` is not a key. -/
def gap : BPlusTree ℕ String := .node (.leaf [(1, "a")]) [(2, .leaf [(3, "c")])]

theorem isWF_twoLevels : IsWF 2 twoLevels := by decide

/-- A root with three separators over four full leaves, at `t = 2`. -/
def wide : BPlusTree ℕ String :=
  .node (.leaf [(1, "a"), (2, "b"), (3, "c")])
    [(4, .leaf [(4, "d"), (5, "e"), (6, "f")]), (7, .leaf [(7, "g"), (8, "h"), (9, "i")]),
      (10, .leaf [(10, "j"), (11, "k"), (12, "l")])]

example : IsWF 2 wide := by decide

/-! ### The empty tree and small minimum degrees -/

/-- Insertion into the empty tree gives a one-entry leaf. -/
example :
    (insert 2 1 "a" (.leaf [])).leaves = [[(1, "a")]] ∧ (insert 2 1 "a" (.leaf [])).height = 1 := by
  decide

/-- Below minimum degree `2` insertion still evaluates and keeps the entries. -/
example :
    (insert 0 1 "a" (.leaf [])).toList = [(1, "a")] ∧
      (insert 1 2 "b" (.leaf [(1, "a")])).toList = [(1, "a"), (2, "b")] ∧
      (insert 1 2 "b" gap).toList = [(1, "a"), (2, "b"), (3, "c")] := by
  decide

/-! ### Leaves and the separator search -/

/-- A root leaf of four entries splits: the left leaf keeps `t = 2` entries and the first key of
the right leaf is copied up. -/
example :
    (insert 2 4 "d" (.leaf [(1, "a"), (2, "b"), (3, "c")])).leaves =
        [[(1, "a"), (2, "b")], [(3, "c"), (4, "d")]] ∧
      (insert 2 4 "d" (.leaf [(1, "a"), (2, "b"), (3, "c")])).height = 2 := by
  decide

example : ∃ l r, insert 2 4 "d" (.leaf [(1, "a"), (2, "b"), (3, "c")]) = .node l [(3, r)] :=
  ⟨_, _, rfl⟩

/-- An equal key has its value replaced. -/
example : (insert 2 3 "z" gap).leaves = [[(1, "a")], [(3, "z")]] := by decide

/-- A key below the first separator goes into the first child. -/
example : (insert 2 0 "z" gap).leaves = [[(0, "z"), (1, "a")], [(3, "c")]] := by decide

/-- A key equal to a separator that is not a key goes into the child the separator
introduces. -/
example : (insert 2 2 "b" gap).leaves = [[(1, "a")], [(2, "b"), (3, "c")]] := by decide

/-! ### Interior nodes -/

/-- The last leaf splits, the root gets a fourth separator and splits: the separator `10` moves
up. -/
example :
    (insert 2 13 "m" wide).leaves =
        [[(1, "a"), (2, "b"), (3, "c")], [(4, "d"), (5, "e"), (6, "f")],
          [(7, "g"), (8, "h"), (9, "i")], [(10, "j"), (11, "k")], [(12, "l"), (13, "m")]] ∧
      (insert 2 13 "m" wide).height = 3 := by
  decide

example : ∃ l r, insert 2 13 "m" wide = .node l [(10, r)] := ⟨_, _, rfl⟩

example : IsWF 2 (insert 2 13 "m" wide) := by decide

example : IsWF 2 (insert 2 4 "d" twoLevels) := by decide

example : (insert 2 4 "d" twoLevels).toList = SortedAssoc.insert 4 "d" twoLevels.toList := by
  decide

/-! ### Theorem instances -/

example : (insert 2 4 "d" twoLevels).toList = SortedAssoc.insert 4 "d" twoLevels.toList :=
  toList_insert isWF_twoLevels 4 "d"

example : IsWF 2 (insert 2 4 "d" twoLevels) := isWF_twoLevels.insert 4 "d"

example :
    (insert 2 4 "d" twoLevels).height =
      match insertOrSplit 2 4 "d" twoLevels with
      | .tree _ => twoLevels.height
      | .split .. => twoLevels.height + 1 :=
  height_insert isWF_twoLevels 4 "d"

example : (insert 2 4 "d" twoLevels).height ≤ twoLevels.height + 1 :=
  height_insert_le isWF_twoLevels 4 "d"

example : twoLevels.height ≤ (insert 2 4 "d" twoLevels).height :=
  height_le_height_insert isWF_twoLevels 4 "d"

example :
    (insert 2 4 "d" twoLevels).size =
      if (lookup 4 twoLevels).isSome then twoLevels.size else twoLevels.size + 1 :=
  size_insert isWF_twoLevels 4 "d"

end CslibFrontierTests.BPlusTreeInsert
