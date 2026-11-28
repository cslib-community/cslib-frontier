/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.DataStructure.BTree.NodeAccess.Query
import CslibFrontier.DataStructure.BTree.NodeAccess.Range

/-!
# External-Memory B-Tree Node-Access Tests and Non-Vacuity Witnesses

Kernel-checked examples and theorems exercising `Cslib.DataStructure.BTree.NodeAccess`:
1. Concrete integer-handle (`H := ℕ`) unaugmented and order-statistic page stores denoting a
   well-formed height-2 B-tree of minimum degree `t = 2` with 7 entries.
2. Exact `eval` and `countQueries` checks for `minR`, `maxR`, `lookupR`, `containsR`, `predR`,
   `succR`, `rankR`, and `rangeR`, including `0` reads on `none` (empty leaf), `1` read on a root
   hit (`fuel = 10 > height`), `2` reads on `rankR` skipping child pages, and pruned child pages in
   `rangeR`.
3. Termination and `≤ fuel` query-count check against a cyclic adversarial store (`h ↦ some h`).
4. Non-vacuity theorem instantiating `countQueries_lookupR_le_log`, `countQueries_rankR_le_log`,
   and `countQueries_rangeR_le_log` on `sampleTree`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BTreeNodeAccess

open PFunctor.FreeM Cslib.DataStructure Cslib.DataStructure.BTree
open Cslib.DataStructure.BTree.NodeAccess

/-- Well-formed height-2 B-tree of minimum degree `t = 2` holding 7 entries. -/
def sampleTree : BTree ℕ String :=
  .node
    (.node .leaf [(1, "a", .leaf), (3, "b", .leaf)])
    [ (5, "c", .node .leaf [(7, "d", .leaf), (9, "e", .leaf)]),
      (11, "f", .node .leaf [(13, "g", .leaf)]) ]

theorem isWF_sampleTree : IsWF 2 sampleTree := by decide

/-- Concrete integer-handle store (`H := ℕ`) with root at handle `0` and children at `1, 2, 3`. -/
def intStore : Store ℕ String ℕ
  | 0 => ⟨some 1, [⟨5, "c", some 2⟩, ⟨11, "f", some 3⟩]⟩
  | 1 => ⟨none, [⟨1, "a", none⟩, ⟨3, "b", none⟩]⟩
  | 2 => ⟨none, [⟨7, "d", none⟩, ⟨9, "e", none⟩]⟩
  | 3 => ⟨none, [⟨13, "g", none⟩]⟩
  | _ => ⟨none, []⟩

/-- Concrete integer-handle order-statistic store (`H := ℕ`) augmenting child slots with sizes. -/
def intRankedStore : RankedStore ℕ String ℕ
  | 0 => ⟨⟨some 1, 2⟩, [⟨5, "c", ⟨some 2, 2⟩⟩, ⟨11, "f", ⟨some 3, 1⟩⟩]⟩
  | 1 => ⟨⟨none, 0⟩, [⟨1, "a", ⟨none, 0⟩⟩, ⟨3, "b", ⟨none, 0⟩⟩]⟩
  | 2 => ⟨⟨none, 0⟩, [⟨7, "d", ⟨none, 0⟩⟩, ⟨9, "e", ⟨none, 0⟩⟩]⟩
  | 3 => ⟨⟨none, 0⟩, [⟨13, "g", ⟨none, 0⟩⟩]⟩
  | _ => ⟨⟨none, 0⟩, []⟩

theorem denotesRanked_intRankedStore : DenotesRanked intRankedStore (some 0) sampleTree := by
  simp only [sampleTree, denotesRanked_some_node_iff, intRankedStore, BTree.size, BTree.toList,
    BTree.toListRest, List.nil_append, List.cons_append, List.length_cons, List.length_nil,
    denotesRankedRest_cons_cons_iff, denotesRankedRest_nil_nil, denotesRanked_none_leaf, and_self]

theorem denotes_intStore : Denotes intStore (some 0) sampleTree := by
  have heq : intStore = intRankedStore.toStore := by
    funext h
    match h with
    | 0 | 1 | 2 | 3 | _ + 4 => rfl
  rw [heq]
  exact denotesRanked_intRankedStore.toDenotes

-- Empty-leaf reference (`none`) issues `0` page reads across all 8 operations, even with
-- `fuel = 5`:
example :
    countQueries intStore (minR 5 none) = 0 ∧
      countQueries intStore (maxR 5 none) = 0 ∧
      countQueries intStore (lookupR 5 7 none) = 0 ∧
      countQueries intStore (containsR 5 7 none) = 0 ∧
      countQueries intStore (predR 5 7 none) = 0 ∧
      countQueries intStore (succR 5 7 none) = 0 ∧
      countQueries intRankedStore (rankR 5 7 none) = 0 ∧
      countQueries intStore (rangeR 5 1 10 none) = 0 := by
  decide

-- Exact evaluation and page-read counts on `intStore` / `intRankedStore` with excess `fuel = 10`:
example :
    eval intStore (lookupR 10 5 (some 0)) = some "c" ∧
      countQueries intStore (lookupR 10 5 (some 0)) = 1 ∧
      eval intStore (lookupR 10 9 (some 0)) = some "e" ∧
      countQueries intStore (lookupR 10 9 (some 0)) = 2 ∧
      eval intStore (containsR 10 8 (some 0)) = false ∧
      countQueries intStore (containsR 10 8 (some 0)) = 2 ∧
      eval intStore (minR 10 (some 0)) = some (1, "a") ∧
      countQueries intStore (minR 10 (some 0)) = 2 ∧
      eval intStore (maxR 10 (some 0)) = some (13, "g") ∧
      countQueries intStore (maxR 10 (some 0)) = 2 ∧
      eval intStore (predR 10 7 (some 0)) = some (5, "c") ∧
      countQueries intStore (predR 10 7 (some 0)) = 2 ∧
      eval intStore (succR 10 9 (some 0)) = some (11, "f") ∧
      countQueries intStore (succR 10 9 (some 0)) = 2 ∧
      eval intRankedStore (rankR 10 10 (some 0)) = 5 ∧
      countQueries intRankedStore (rankR 10 10 (some 0)) = 2 ∧
      eval intStore (rangeR 10 3 9 (some 0)) = [(3, "b"), (5, "c"), (7, "d"), (9, "e")] ∧
      countQueries intStore (rangeR 10 3 9 (some 0)) = 3 := by
  decide

/-- Cyclic adversarial store where handle `0` points back to `0` on every child slot. -/
def cyclicStore : Store ℕ String ℕ :=
  fun h => ⟨some h, [⟨10, "x", some h⟩]⟩

example :
    eval cyclicStore (lookupR 4 99 (some 0)) = none ∧
      countQueries cyclicStore (lookupR 4 99 (some 0)) = 4 := by
  decide

-- Non-vacuity witness instantiating the logarithmic theorems on `sampleTree`:
example :
    eval intStore (lookupR 2 11 (some 0)) = BTree.lookup 11 sampleTree ∧
      countQueries intStore (lookupR 2 11 (some 0)) ≤
        Nat.log 2 ((sampleTree.size + 1) / 2) + 1 ∧
      eval intRankedStore (rankR 2 11 (some 0)) = BTree.rank 11 sampleTree ∧
      countQueries intRankedStore (rankR 2 11 (some 0)) ≤
        Nat.log 2 ((sampleTree.size + 1) / 2) + 1 ∧
      eval intStore (rangeR 2 3 11 (some 0)) = BTree.range 3 11 sampleTree ∧
      countQueries intStore (rangeR 2 3 11 (some 0)) ≤
        2 * (Nat.log 2 ((sampleTree.size + 1) / 2) + 1) +
          (BTree.range 3 11 sampleTree).length := by
  have hf : sampleTree.height ≤ 2 := by decide
  exact ⟨eval_lookupR denotes_intStore hf 11,
    countQueries_lookupR_le_log isWF_sampleTree denotes_intStore hf 11,
    eval_rankR denotesRanked_intRankedStore hf 11,
    countQueries_rankR_le_log isWF_sampleTree denotesRanked_intRankedStore hf 11,
    eval_rangeR denotes_intStore hf 3 11,
    countQueries_rangeR_le_log isWF_sampleTree denotes_intStore hf 3 11⟩

end CslibFrontierTests.BTreeNodeAccess
