/-
Copyright (c) 2026 Paulo Matos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Matos
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Rope.Basic
-- `import all` so that `decide +kernel` can evaluate `Rope.ofList` on concrete inputs through
-- `List.toChunks`, whose body Batteries does not expose.
import all Batteries.Data.List.Basic

/-!
# Rope well-formedness and model examples

Checked examples for `Cslib.DataStructure.Rope` at chunk bounds `B = 1` and `B = 2`. Each part
of `IsWF` is shown failing on a tree that satisfies the other two parts: a stale length cache, a
stale height cache, an oversized leaf, an empty leaf, an empty internal child and a height
imbalance. The boundary conventions of the later edit operations are checked on core lists.
-/

public section

namespace CslibFrontierTests.Rope

open Cslib.DataStructure Cslib.DataStructure.Rope

/-- `[1, 2]` and `[3]` under one node. -/
abbrev twoLeaves : Rope ℕ := .node 3 1 (.leaf [1, 2]) (.leaf [3])

/-- Three singleton leaves, balanced. -/
abbrev threeSingletons : Rope ℕ := .node 3 2 (.node 2 1 (.leaf [1]) (.leaf [2])) (.leaf [3])

/-! ### Well-formed trees -/

example : IsWF 2 (empty : Rope ℕ) := by decide
example : IsWF 1 (leaf [7]) := by decide
example : IsWF 2 twoLeaves := by decide
example : IsWF 1 threeSingletons := by decide

/-- A leaf of two elements is too large at `B = 1`. -/
example : ¬ IsWF 1 twoLeaves := by decide

/-! ### Each part of well-formedness fails on its own -/

/-- A stale length cache: the caches are wrong but the chunks and balance are fine. -/
example : ¬ CacheCorrect (Rope.node 4 1 (.leaf [1, 2]) (.leaf [3])) ∧
    Chunked 2 (Rope.node 4 1 (.leaf [1, 2]) (.leaf [3])) ∧
    Balanced (Rope.node 4 1 (.leaf [1, 2]) (.leaf [3])) := by decide

/-- A stale height cache. -/
example : ¬ CacheCorrect (Rope.node 3 2 (.leaf [1, 2]) (.leaf [3])) ∧
    Chunked 2 (Rope.node 3 2 (.leaf [1, 2]) (.leaf [3])) ∧
    Balanced (Rope.node 3 2 (.leaf [1, 2]) (.leaf [3])) := by decide

/-- An oversized leaf. -/
example : ¬ Chunked 2 (Rope.leaf [1, 2, 3]) ∧ CacheCorrect (Rope.leaf [1, 2, 3]) := by decide

/-- An empty leaf: the empty rope must be `empty`, never `leaf []`. -/
example : ¬ Chunked 2 (Rope.leaf ([] : List ℕ)) := by decide

/-- An internal node with an empty child. -/
example : ¬ Chunked 2 (Rope.node 1 1 .empty (.leaf [1])) ∧
    CacheCorrect (Rope.node 1 1 .empty (.leaf [1])) ∧
    Balanced (Rope.node 1 1 .empty (.leaf [1])) := by decide

/-- A height imbalance with correct caches and chunks. -/
example : ¬ Balanced (Rope.node 4 3 threeSingletons (.leaf [4])) ∧
    CacheCorrect (Rope.node 4 3 threeSingletons (.leaf [4])) ∧
    Chunked 1 (Rope.node 4 3 threeSingletons (.leaf [4])) := by decide

/-! ### The list model -/

example : threeSingletons.toList = [1, 2, 3] := by decide
example : threeSingletons.length = threeSingletons.toList.length := by decide
example : threeSingletons.get? 1 = some 2 := by decide
example : threeSingletons.get? 3 = none := by decide
/-- Lookups on either side of the boundary between the chunks `[1, 2]` and `[3]`. -/
example : twoLeaves.get? 1 = some 2 ∧ twoLeaves.get? 2 = some 3 := by decide
example : (twoLeaves.map (· * 10)).toList = [10, 20, 30] := by decide
example : twoLeaves.foldl (fun acc x => acc * 10 + x) 0 = 123 := by decide
example : twoLeaves.foldr (fun x acc => acc * 10 + x) 0 = 321 := by decide
example : 3 ∈ twoLeaves := by decide
example : 4 ∉ twoLeaves := by decide

/-- Bulk construction on a concrete input is well-formed and represents it. -/
example : IsWF 2 (ofList 2 [1, 2, 3, 4, 5]) ∧ (ofList 2 [1, 2, 3, 4, 5]).toList = [1, 2, 3, 4, 5] :=
  by decide +kernel

/-- Bulk construction at `B = 0` makes singleton chunks, as `max 1 B` says. -/
example : IsWF 1 (ofList 0 [1, 2, 3]) ∧ (ofList 0 [1, 2, 3]).get? 2 = some 3 := by decide +kernel

/-! ### Boundary conventions of the edit operations, on core lists -/

example : [1, 2, 3].splitAt 5 = ([1, 2, 3], []) := rfl
example : [1, 2, 3].insertIdx 3 0 = [1, 2, 3, 0] := rfl
example : [1, 2, 3].insertIdx 4 0 = [1, 2, 3] := rfl
example : [1, 2, 3].set 3 0 = [1, 2, 3] := rfl
example : [1, 2, 3, 4].extract 1 3 = [2, 3] := rfl
example : [1, 2, 3, 4].extract 3 1 = [] := rfl
example : [1, 2, 3, 4].take 1 ++ [1, 2, 3, 4].drop 3 = [1, 4] := rfl
/-- Reversed erase endpoints would duplicate elements, so erase guards on `i ≤ j`. -/
example : [1, 2, 3, 4].take 3 ++ [1, 2, 3, 4].drop 1 = [1, 2, 3, 2, 3, 4] := rfl

end CslibFrontierTests.Rope
