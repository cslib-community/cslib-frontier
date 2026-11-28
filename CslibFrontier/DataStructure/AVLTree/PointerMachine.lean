/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.Basic
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Search

/-!
# Logarithmic pointer-machine search in AVL trees

`search_correct` applies the concrete linked-tree search program to the existing AVL
representation and height theorem. Its bound counts pointer-machine instructions, including
comparisons, null tests, jumps and halt. The initial linked representation is supplied;
this theorem does not construct it or implement AVL insertion and rebalancing.
-/

public section

namespace Cslib.DataStructure.AVLTree

open Cslib.PointerMachine
open SearchTree.PointerMachine

/-- A represented valid AVL tree admits a concrete pointer-machine search in at most
`12 * log₂(card + 1) + 3` instructions. Nonnull output is exactly key membership;
`SearchResult` additionally gives the matching record and the complete register/heap frame. -/
theorem search_correct {M : Model} [LinearOrder M.Value] {extra regs : ℕ}
    (lt : M.Test) (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (t : AVLTree M.Value) (valid : t.Valid)
    (tree : BinaryTree (Label M extra)) (shape : keys tree = t.toBinaryTree)
    (x : State M (layout extra regs)) (parent : Pointer)
    (rep : Represents x.heap parent tree) (cursor : x.ptr 0 = root tree) (pc : x.pc = 0) :
    ∃ y time, Executes (search lt) x y time ∧
      time ≤ 12 * Nat.log 2 (t.elements.card + 1) + 3 ∧
      SearchResult x y tree ∧ ((y.ptr 0).isSome = true ↔ x.data 0 ∈ t.elements) := by
  obtain ⟨y, time, exec, bound, result⟩ :=
    SearchTree.PointerMachine.search_correct lt compare x tree parent rep cursor pc
  have visits := t.searchVisits_le_cachedHeight valid.heightConsistent (x.data 0)
  have height := valid.cachedHeight_le_two_mul_log
  have bv : SearchTree.searchVisits (x.data 0) (keys tree) ≤ t.cachedHeight := by
    rw [shape]
    exact visits
  refine ⟨y, time, exec, by omega, result, ?_⟩
  rw [result.found, shape, ← contains_eq_searchTree]
  exact contains_eq_true valid.ordered (x.data 0)

end Cslib.DataStructure.AVLTree
