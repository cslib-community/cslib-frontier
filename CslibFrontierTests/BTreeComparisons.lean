/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.BTree.Comparisons.Erase
public import CslibFrontier.DataStructure.BTree.Comparisons.Insert
public import CslibFrontier.DataStructure.BTree.Comparisons.Range

/-!
# B-tree comparison cost examples
-/

public section

namespace CslibFrontierTests.BTreeComparisons

open Cslib (FreeM)
open Cslib.DataStructure
open Cslib.DataStructure.BTree
open Cslib.Query (LEQuery UpperBound)

private def exampleTree : BTree ℕ String :=
  BTree.node (BTree.node BTree.leaf [(1, "a", BTree.leaf), (2, "b", BTree.leaf)])
    [(3, "c", BTree.node BTree.leaf [(4, "d", BTree.leaf), (5, "e", BTree.leaf)]),
     (6, "f", BTree.node BTree.leaf [(7, "g", BTree.leaf), (8, "h", BTree.leaf)])]

example :
    (lookupQ 4 (BTree.node (BTree.node BTree.leaf [(1, 1, BTree.leaf)])
      [(2, 2, BTree.node BTree.leaf [(3, 3, BTree.leaf)])] : BTree ℕ ℕ)).countQueries
        orderOracle = 2 := by
  simp [lookupQ_def, lookupM]

example : (rangeQ 2 7 exampleTree).countQueries orderOracle = 16 := by
  simp [exampleTree, rangeQ_def, rangeM_node, rangeM_leaf, rangeRestM_cons, rangeRestM_nil]

example : (rangeQ 9 10 exampleTree).countQueries orderOracle = 8 := by
  simp [exampleTree, rangeQ_def, rangeM_node, rangeM_leaf, rangeRestM_cons, rangeRestM_nil]

example : (insertQ (t := 2) 4 "new" exampleTree).countQueries orderOracle = 5 := by
  simp [exampleTree, insertQ_def, insertM, insertOrSplitM, insertRestM]

def falseOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun _ _ => false

example :
    (lookupQ 4 (BTree.node (BTree.node BTree.leaf [(1, 1, BTree.leaf)])
      [(2, 2, BTree.node BTree.leaf [(3, 3, BTree.leaf)])] : BTree ℕ ℕ)).countQueries
        falseOracle = 2 := by
  simp [lookupQ_def, lookupM, falseOracle]

example : (insertQ (t := 2) 4 "new" exampleTree).eval orderOracle =
    insert (t := 2) 4 "new" exampleTree := by
  exact eval_insertQ

def exampleTreeFull : BTree ℕ String :=
  BTree.node (BTree.node BTree.leaf [(1, "a", BTree.leaf), (2, "b", BTree.leaf)])
    [(3, "c", BTree.node BTree.leaf [(4, "d", BTree.leaf), (5, "e", BTree.leaf)]),
     (6, "f", BTree.node BTree.leaf [(7, "g", BTree.leaf),
       (8, "h", BTree.leaf), (9, "i", BTree.leaf)])]

example : (insertQ (t := 2) 10 "j" exampleTreeFull).countQueries orderOracle = 5 := by
  simp [exampleTreeFull, insertQ_def, insertM, insertOrSplitM, insertRestM]

example : (insertQ (t := 2) 10 "j" exampleTreeFull).countQueries falseOracle = 5 := by
  simp [exampleTreeFull, falseOracle, insertQ_def, insertM, insertOrSplitM, insertRestM]

/-! ### Erasure -/

private def trueOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun _ _ => true

/-- Under the order's oracle the counted erasure returns the tree without the key. -/
example :
    ((eraseQ 2 4 exampleTree).eval orderOracle).toList =
      [(1, "a"), (2, "b"), (3, "c"), (5, "e"), (6, "f"), (7, "g"), (8, "h")] := by
  rw [eval_eraseQ]
  decide

/-- Under the order's oracle the counted extremal removals return the least and greatest
entries. -/
example :
    ((eraseMinQ 2 exampleTree).eval orderOracle).map (·.1) = some (1, "a") ∧
      ((eraseMaxQ 2 exampleTree).eval orderOracle).map (·.1) = some (8, "h") := by
  rw [eval_eraseMinQ, eval_eraseMaxQ, eraseMin?_eq, eraseMax?_eq]
  decide

/-- Three comparisons at the root (`4 ≤ 3` fails, `4 ≤ 6` holds, `6 ≤ 4` fails) and two in the
child holding the key. -/
example : (eraseQ 2 4 exampleTree).countQueries orderOracle = 5 := by
  simp [exampleTree, eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons,
    popMinM_node, rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- An interior key costs the two comparisons that find it: fetching its successor asks
nothing. -/
example : (eraseQ 2 3 exampleTree).countQueries orderOracle = 2 := by
  simp [exampleTree, eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons,
    popMinM_node, rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- When every answer is `false`, erasure scans both root keys and both keys of the last child. -/
example : (eraseQ 2 4 exampleTree).countQueries falseOracle = 4 := by
  simp [exampleTree, falseOracle, eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons,
    popMinM_node, rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- When every answer is `true`, erasure takes the first root key for the key sought. -/
example : (eraseQ 2 4 exampleTree).countQueries trueOracle = 2 := by
  simp [exampleTree, trueOracle, eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons,
    popMinM_node, rebalanceRightM_def, rebalanceLastM_def, underflows]

example : (eraseQ 2 4 (.leaf : BTree ℕ String)).countQueries falseOracle = 0 := by simp

/-- An absent key: two comparisons at the root and two in the first child, where the search ends
in an empty subtree. -/
example : (eraseQ 2 0 exampleTree).countQueries orderOracle = 4 := by
  simp [exampleTree, eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons, popMinM_node,
    rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- A repair and a root collapse ask nothing: erasing `1` leaves its child empty, the child merges
with its sibling and the root collapses, for the two comparisons at each of the two nodes
scanned. -/
example :
    (eraseQ 2 1 (BTree.node (.node .leaf [(1, (), .leaf)])
      [(2, (), .node .leaf [(3, (), .leaf)])] : BTree ℕ Unit)).countQueries orderOracle = 4 := by
  simp [eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons, popMinM_node,
    rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- The bound is attained: erasing the last key of a full node at `t = 2` makes
`2 * t * height = 4` comparisons. -/
example :
    (eraseQ 2 3 (BTree.node .leaf [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)] :
      BTree ℕ Unit)).countQueries orderOracle = 4 := by
  simp [eraseQ_def, eraseM_def, eraseSubtreeM_node, eraseRestM_cons, rebalanceRightM_def,
    rebalanceLastM_def, underflows]

/-- The bound `2 * t * height` at `t = 2` and height `2`, under every oracle. -/
example (oracle : {ι : Type} → LEQuery ℕ ι → ι) :
    (eraseQ 2 4 exampleTree).countQueries oracle ≤ 8 :=
  countQueries_eraseQ_le oracle (tr := exampleTree) (by decide)

/-- The least key is `1`: two comparisons at the root and two in the first child. -/
example : (eraseMinQ 2 exampleTree).countQueries orderOracle = 4 := by
  simp [exampleTree, eraseMinQ_def, eraseMinM_def, minM, eraseM_def, eraseSubtreeM_node,
    eraseRestM_cons, popMinM_node, rebalanceRightM_def, rebalanceLastM_def, underflows]

/-- The greatest key is `8`: two comparisons at the root and three in the last child. -/
example : (eraseMaxQ 2 exampleTree).countQueries orderOracle = 5 := by
  simp [exampleTree, eraseMaxQ_def, eraseMaxM_def, maxM_node_cons_cons, maxM_node_singleton,
    maxM_leaf, eraseM_def, eraseSubtreeM_node, eraseRestM_cons, popMinM_node, rebalanceRightM_def,
    rebalanceLastM_def, underflows]

/-- Finding the least entry asks nothing, so an oracle that is not an order sees only the scan of
the erasure. -/
example : (eraseMinQ 2 exampleTree).countQueries falseOracle = 4 := by
  simp [exampleTree, falseOracle, eraseMinQ_def, eraseMinM_def, minM, eraseM_def,
    eraseSubtreeM_node, eraseRestM_cons, popMinM_node, rebalanceRightM_def,
    rebalanceLastM_def, underflows]

/-! The node-visit bounds of erasure times the per-node comparison bound, `2 * t * (2 * height)`
for `erase` and `2 * t * (3 * height)` for the extremal removals, follow from the bounds proved
here. -/

example {α β : Type} [LinearOrder α] {t : ℕ} :
    UpperBound (fun p : WFInput α β t => eraseQ t p.val.2 p.val.1)
      (fun p => p.val.1.height) (fun h => 2 * t * (2 * h)) :=
  fun oracle n x hx =>
    (eraseQ_upperBound oracle n x hx).trans (Nat.mul_le_mul_left _ (by omega))

example {α β : Type} [LinearOrder α] {t : ℕ} :
    UpperBound (fun p : {tr : BTree α β // IsWF t tr} => eraseMinQ t p.val)
      (fun p => p.val.height) (fun h => 2 * t * (3 * h)) :=
  fun oracle n x hx =>
    (eraseMinQ_upperBound oracle n x hx).trans (Nat.mul_le_mul_left _ (by omega))

example {α β : Type} [LinearOrder α] {t : ℕ} :
    UpperBound (fun p : {tr : BTree α β // IsWF t tr} => eraseMaxQ t p.val)
      (fun p => p.val.height) (fun h => 2 * t * (3 * h)) :=
  fun oracle n x hx =>
    (eraseMaxQ_upperBound oracle n x hx).trans (Nat.mul_le_mul_left _ (by omega))

end CslibFrontierTests.BTreeComparisons
