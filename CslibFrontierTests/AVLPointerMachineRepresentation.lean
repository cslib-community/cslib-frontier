/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Context
import Mathlib.Tactic.FinCases

/-! The concrete height program realizes the existing AVL constructor while retaining its child. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure SearchTree.PointerMachine AVLTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Bool
  Test := Empty
  evalOp op a b := if op then max a b + 1 else 0
  evalTest t := nomatch t

private def node (address key height : ℕ) : Label model 1 :=
  ⟨address, fun f => if f = 0 then key else height⟩

private def child : BinaryTree (Label model 1) := .node (node 1 3 1) .nil .nil

private def tree (oldHeight : ℕ) : BinaryTree (Label model 1) :=
  .node (node 0 7 oldHeight) child .nil

private def initial (oldHeight : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 then some 0 else none
  data _ := 42
  heap := [record (some 1) none none (node 0 7 oldHeight),
    record none none (some 0) (node 1 3 1)]

private theorem distinct (oldHeight : ℕ) : AddressesDistinct (tree oldHeight) := by
  have loc (p : PosNum) (u : Label model 1) (h : (tree oldHeight).get p = some u) :
      (p = .one ∧ u = node 0 7 oldHeight) ∨ (p = .bit0 .one ∧ u = node 1 3 1) := by
    cases p with
    | one => simpa [tree, BinaryTree.get, eq_comm] using h
    | bit1 p => cases p <;> simp [tree, BinaryTree.get] at h
    | bit0 p =>
      cases p with
      | one => simpa [tree, child, BinaryTree.get, eq_comm] using h
      | bit0 p => cases p <;> simp [tree, child, BinaryTree.get] at h
      | bit1 p => cases p <;> simp [tree, child, BinaryTree.get] at h
  intro p q u v hp hq eq
  rcases loc p u hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases loc q v hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [node]

example (oldHeight : ℕ) :
    ∃ y, Executes (recomputeHeight false true 1) (initial oldHeight) y 9 ∧
      Represents y.heap none (.node (node 0 7 2) child .nil) ∧
      Matches id 1 (.node (node 0 7 2) child .nil)
        (AVLTree.mkNode 7 (.node 3 1 .nil .nil) .nil) ∧
      y.data 0 = 42 ∧ y.ptr 0 = some 0 := by
  obtain ⟨y, exec, _, rep, matched, _, data, ptr⟩ := recomputeHeight_mkNode false true id
    (fun _ _ => rfl) (fun _ _ => rfl) 1 (by decide) (initial oldHeight)
    (node 0 7 oldHeight) child .nil (.node 3 1 .nil .nil) .nil none
    (by simp [Represents, initial, node, root, child]) (distinct oldHeight)
    (by simp [Matches, child, node]) trivial
    (by simp [AVLTree.HeightConsistent, AVLTree.cachedHeight]) trivial rfl rfl
  have updated : { node 0 7 oldHeight with
      data := Function.update (node 0 7 oldHeight).data 1 2 } = node 0 7 2 := by
    change Label.mk 0 _ = Label.mk 0 _
    congr 1
    funext f
    fin_cases f <;> rfl
  refine ⟨y, exec, ?_, ?_, data 0 (by decide) (by decide), ptr 0 (by decide)⟩
  · change Represents y.heap none (.node
      { node 0 7 oldHeight with data := Function.update (node 0 7 oldHeight).data 1 2 } child .nil)
      at rep
    simpa only [updated] using rep
  · change Matches id 1 (.node
      { node 0 7 oldHeight with data := Function.update (node 0 7 oldHeight).data 1 2 } child .nil)
      (AVLTree.mkNode 7 (.node 3 1 .nil .nil) .nil) at matched
    simpa only [updated] using matched

-- Equal key trees do not suffice: the complete match detects incorrect cached heights.
example : ¬ Matches id 1 (tree 99) (AVLTree.mkNode 7 (.node 3 1 .nil .nil) .nil) := by
  simp [Matches, tree, node, AVLTree.mkNode, AVLTree.cachedHeight]

-- A valid whole-tree match supplies the original AVL value at a proper linked focus.
example : ∃ t : AVLTree ℕ, Matches id 1 child t ∧ t.Valid := by
  have matched : Matches id 1 (plug [.left (node 0 7 2) .nil] child)
      (.node 7 2 (.node 3 1 .nil .nil) .nil) := by
    simp [plug, Matches, child, node]
  exact matched.exists_valid_focus (by
    simp [AVLTree.Valid, AVLTree.Ordered, SearchTree.Ordered, AVLTree.toBinaryTree,
      SearchTree.elements, AVLTree.HeightConsistent, AVLTree.Balanced, AVLTree.cachedHeight])

-- Consistent heights determine the cached decoration; the source shape is sufficient.
example (t : AVLTree ℕ) (valid : t.HeightConsistent)
    (shape : t.toBinaryTree = BinaryTree.node 7 (.node 3 .nil .nil) .nil) :
    t = .node 7 2 (.node 3 1 .nil .nil) .nil :=
  valid.eq_of_toBinaryTree_eq (by simp [AVLTree.HeightConsistent, AVLTree.cachedHeight]) shape
