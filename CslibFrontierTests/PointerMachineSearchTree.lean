/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine
import CslibFrontier.DataStructure.SearchTree.PointerMachine.Update
import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context

/-! A linked three-node tree with an unrelated record, metadata and client registers.
Both outcomes and empty-tree termination are tested, together with the logarithmic theorem. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Unit
  evalOp o := nomatch o
  evalTest _ a b := decide (a < b)

private def label (address key : ℕ) : Label model 1 :=
  ⟨address, fun i => if i = 0 then key else 99⟩

private def tree : BinaryTree (Label model 1) :=
  .node (label 0 2) (.node (label 1 1) .nil .nil) (.node (label 2 3) .nil .nil)

private def initial (query : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else some 3
  data i := if i = 0 then query else 42
  heap := [record (some 1) (some 2) none (label 0 2),
    record none none (some 0) (label 1 1), record none none (some 0) (label 2 3),
    record none none none (label 3 100)]

private def run (s : State model (layout 1 1)) : State model (layout 1 1) :=
  (fun x => (step (search ()) x).getD x)^[30] s

example : ((run (initial 1)).ptr 0 == some 1) = true := by decide
example : ((run (initial 2)).ptr 0 == some 0) = true := by decide
example : ((run (initial 3)).ptr 0 == some 2) = true := by decide
example : ((run (initial 0)).ptr 0 == none) = true := by decide
example : ((run (initial 4)).ptr 0 == none) = true := by decide
example : ((run (initial 1)).data 2 == 42) = true := by decide
example : ((run (initial 1)).ptr 6 == some 3) = true := by decide
example : (((run (initial 1)).heap[1]?.map (fun n => n.data 1)) == some 99) = true := by decide
example : ((run (initial 4)).pc == 10) = true := by decide
example : ((run ((initial 2).setPtr 0 none)).pc == 10) = true := by decide

private def avl : AVLTree ℕ :=
  .node 2 2 (.node 1 1 .nil .nil) (.node 3 1 .nil .nil)

example (query : ℕ) :
    ∃ y time, Executes (search ()) (initial query) y time ∧ time ≤ 27 ∧
      SearchResult (initial query) y tree ∧
      ((y.ptr 0).isSome = true ↔ query ∈ ({1, 2, 3} : Finset ℕ)) := by
  obtain ⟨y, time, exec, bound, result, member⟩ := AVLTree.search_correct
    (M := model) () (fun _ _ => rfl) avl (by
      simp [avl, AVLTree.Valid, AVLTree.Ordered, SearchTree.Ordered, AVLTree.toBinaryTree,
        SearchTree.elements, AVLTree.HeightConsistent, AVLTree.Balanced])
    tree rfl (initial query) none
    (by simp [Represents, initial, tree, root, label]) rfl rfl
  refine ⟨y, time, exec, ?_, result, ?_⟩
  · norm_num [avl, AVLTree.elements, SearchTree.elements, AVLTree.toBinaryTree, Nat.log] at bound
    exact bound
  · simpa [initial, avl, AVLTree.elements, SearchTree.elements, AVLTree.toBinaryTree,
      Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using member

-- A falsely labelled root does not satisfy the representation invariant.
example : ¬ Represents (initial 1).heap none (.node (label 0 8) .nil .nil) := by
  intro h
  have data := congrArg (fun n => n.map (fun r => r.data 0)) h.1
  norm_num [initial, record, label] at data

-- An arbitrary payload is stored at the cursor without changing any key or client register.
example (value : ℕ) :
    ∃ y, Executes [.storeData 1 0 2, .halt]
        ((initial 2).setData 2 value) y 2 ∧
      Represents y.heap none (updateData tree 0 1 value) ∧
      y.ptr = (initial 2).ptr ∧
      y.data = ((initial 2).setData 2 value).data ∧
      y.heap.length = 4 ∧
      (∀ b, b ≠ 0 → y.heap[b]? = (initial 2).heap[b]?) := by
  exact storeData_correct ((initial 2).setData 2 value) tree none
    (by simp [State.setData, Represents, initial, tree, root, label]) 0 0 rfl 1 2 rfl

example (value : ℕ) : keys (updateData tree 0 1 value) = keys tree :=
  keys_updateData tree 0 1 value (by decide)

-- Writing the key itself is deliberately not covered by the key-preservation theorem.
example : keys (updateData tree 0 0 8) =
    .node 8 (.node 1 .nil .nil) (.node 3 .nil .nil) := by decide

-- The ghost ancestor context reconstructs the original whole tree.
private def ancestors : List (Frame model 1) :=
  [.left (label 0 2) (.node (label 2 3) .nil .nil)]

example (query : ℕ) :
    Represents (initial query).heap (contextParent ancestors) (.node (label 1 1) .nil .nil) ∧
      ContextRep (initial query).heap (some 1) ancestors := by
  apply (represents_plug_iff (initial query).heap ancestors
    (.node (label 1 1) .nil .nil)).mp
  simp [ancestors, plug, Represents, initial, root, label]

example (query : ℕ) :
    ∃ t, Executes [.loadPtr 0 2 0, .halt] ((initial query).setPtr 0 (some 1)) t 2 ∧
      t.heap = (initial query).heap ∧ t.data = (initial query).data ∧ t.ptr 0 = some 0 ∧
      (∀ i, i ≠ 0 → t.ptr i = ((initial query).setPtr 0 (some 1)).ptr i) := by
  apply ascend_correct ((initial query).setPtr 0 (some 1)) ancestors
    (label 1 1) .nil .nil
  · simp [State.setPtr, Represents, ancestors, contextParent, initial, label, root]
  · simp [State.setPtr, label]
  · rfl
