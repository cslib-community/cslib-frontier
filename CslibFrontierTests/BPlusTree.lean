/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BPlusTree.Height

/-!
# B+-tree well-formedness and height examples

Checked examples for `Cslib.DataStructure.BPlusTree`: the separator convention, concrete trees at
`t = 2` and `t = 3` that `decide` accepts or rejects for occupancy, equal leaf depth, key order
and the separator convention, the leaves of a tree, and instances of the height bounds.
-/

public section

namespace CslibFrontierTests.BPlusTree

open Cslib.DataStructure Cslib.DataStructure.BPlusTree

/-! ### The separator convention -/

/-- A separator equal to the least key of the child it introduces is intended. Under the rejected
alternative, with separators bounding their child strictly from below, this tree would be
malformed. -/
example :
    IsWF 2 (BPlusTree.node (α := ℕ) (β := String) (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])]) := by
  decide

/-- A separator above a key in the child it introduces violates the convention. -/
example :
    ¬ Separated
      (BPlusTree.node (α := ℕ) (β := String) (.leaf [(1, "a")]) [(3, .leaf [(2, "b")])]) := by
  decide

/-- A separator need not occur as a key in any leaf. -/
example :
    IsWF 2 (BPlusTree.node (α := ℕ) (β := String) (.leaf [(1, "a")]) [(2, .leaf [(3, "c")])]) := by
  decide

/-- A separator must be above every key of the children before it, not only of the child just
before it: here `5` is in the first child and the second separator is `4`. The entries are still
in key order child by child only if the convention holds, so sortedness fails too. -/
example :
    ¬ Separated (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(5, ())])
      [(6, .leaf [(6, ())]), (4, .leaf [(7, ())])]) := by
  decide

/-- The separator convention is not implied by sorted entries: these entries are in key order,
but the separator `1` is not above the key `1` of the first child. -/
example :
    (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ())]) [(1, .leaf [(2, ())])]).toList
        = [(1, ()), (2, ())] ∧
      ¬ IsWF 2 (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ())]) [(1, .leaf [(2, ())])]) := by
  decide

/-! ### Well-formedness -/

/-- The empty tree is the empty leaf, and it is well-formed. -/
example : IsWF 2 (BPlusTree.leaf [] : BPlusTree ℕ Unit) := by decide

/-- The minimum degree is at least `2`, so even the empty tree is not well-formed at `t = 1`. -/
example : ¬ IsWF 1 (BPlusTree.leaf [] : BPlusTree ℕ Unit) := by decide

/-- A root leaf may hold up to `2 * t - 1` entries and no more. -/
example :
    IsWF 2 (BPlusTree.leaf [(1, ()), (2, ()), (3, ())] : BPlusTree ℕ Unit) ∧
      ¬ IsWF 2 (BPlusTree.leaf [(1, ()), (2, ()), (3, ()), (4, ())] : BPlusTree ℕ Unit) := by
  decide

/-- Occupancy depends on `t`: one-entry leaves are full enough at `t = 2` and too sparse at
`t = 3`, where a non-root leaf needs at least two entries. -/
example :
    IsWF 2 (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ())]) [(2, .leaf [(2, ())])]) ∧
      ¬ IsWF 3
        (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ())]) [(2, .leaf [(2, ())])]) := by
  decide

/-- Two leaves of two entries under one separator are well-formed at `t = 3`. -/
example :
    IsWF 3 (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ()), (2, ())])
      [(3, .leaf [(3, ()), (4, ())])]) := by
  decide

/-- An interior root needs at least one separator. -/
example : ¬ IsWF 2 (BPlusTree.node (α := ℕ) (β := Unit) (.leaf [(1, ())]) []) := by decide

/-- A node whose children differ in height is not well-formed for any `t`. -/
example (t : ℕ) :
    ¬ IsWF t (BPlusTree.node (α := ℕ) (β := Unit)
      (.node (.leaf [(1, ())]) [(2, .leaf [(2, ())])]) [(3, .leaf [(3, ())])]) :=
  fun h => absurd h.balanced (by decide)

/-- Entries out of key order within a leaf are not well-formed. -/
example : ¬ IsWF 2 (BPlusTree.leaf [(2, ()), (1, ())] : BPlusTree ℕ Unit) := by decide

/-! ### Leaves, size and height -/

/-- A tree of height `3` at `t = 2`: four leaves under two interior nodes. -/
def twoLevels : BPlusTree ℕ String :=
  .node (.node (.leaf [(1, "a")]) [(2, .leaf [(2, "b")])])
    [(3, .node (.leaf [(3, "c")]) [(5, .leaf [(5, "e"), (6, "f")])])]

example : IsWF 2 twoLevels := by decide

/-- `leaves` lists the leaves from left to right, and `toList` is their concatenation. -/
example :
    twoLevels.leaves = [[(1, "a")], [(2, "b")], [(3, "c")], [(5, "e"), (6, "f")]] ∧
      twoLevels.toList = [(1, "a"), (2, "b"), (3, "c"), (5, "e"), (6, "f")] := by
  decide

/-- A leaf has height `1`, and the empty tree has size `0`. -/
example :
    (BPlusTree.leaf [] : BPlusTree ℕ Unit).height = 1 ∧
      (BPlusTree.leaf [] : BPlusTree ℕ Unit).size = 0 := by
  decide

/-- The height bound at `twoLevels`: height `3`, size `5`, and `Nat.log 2 5 + 1 = 3`. -/
example : twoLevels.height = 3 ∧ twoLevels.size = 5 ∧ Nat.log 2 twoLevels.size + 1 = 3 := by
  decide

/-- The bounds applied to a well-formed tree. -/
example :
    twoLevels.height ≤ Nat.log 2 twoLevels.size + 1 ∧
      2 ^ (twoLevels.height - 1) ≤ twoLevels.size :=
  have h : IsWF 2 twoLevels := by decide
  ⟨h.height_le_log, h.pow_le_size (by decide)⟩

/-- Mapping over values keeps the keys and the shape. -/
example :
    (twoLevels.map String.length).toList = [(1, 1), (2, 1), (3, 1), (5, 1), (6, 1)] ∧
      (twoLevels.map String.length).height = 3 := by
  decide

end CslibFrontierTests.BPlusTree
