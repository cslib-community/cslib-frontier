/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Height

/-! Height recomputation repairs a stale cache and handles empty children. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure.SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Bool
  Test := Empty
  evalOp op a b := if op then max a b + 1 else 0
  evalTest t := nomatch t

private def node (address key height : ℕ) : Label model 1 :=
  ⟨address, fun f => if f = 0 then key else height⟩

private def tree (oldHeight : ℕ) : BinaryTree (Label model 1) :=
  .node (node 0 7 oldHeight) (.node (node 1 3 1) .nil .nil) .nil

private def initial (oldHeight : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 then some 0 else none
  data _ := 42
  heap := [record (some 1) none none (node 0 7 oldHeight),
    record none none (some 0) (node 1 3 1)]

example (oldHeight : ℕ) :
    ∃ y, Executes (recomputeHeight false true 1) (initial oldHeight) y 9 ∧
      Represents y.heap none (updateData (tree oldHeight) 0 1 2) ∧
      y.data 0 = 42 ∧ y.ptr 0 = some 0 := by
  obtain ⟨y, exec, _, rep, data, ptr⟩ := recomputeHeight_correct false true id
    (fun _ _ => rfl) (fun _ _ => rfl) 1 (initial oldHeight) (node 0 7 oldHeight)
    (.node (node 1 3 1) .nil .nil) .nil none
    (by simp [Represents, initial, node, root])
    rfl rfl rfl rfl
  exact ⟨y, exec, rep, data 0 (by decide) (by decide), ptr 0 (by decide)⟩

private def run (x : State model (layout 1 1)) : State model (layout 1 1) :=
  (fun s => (step (recomputeHeight false true 1) s).getD s)^[9] x

example : ((run (initial 99)).heap[0]?.map (fun r => r.data 1)) = some 2 := by decide
example : ((run (initial 99)).heap[0]?.map (fun r => r.data 0)) = some 7 := by decide
example : (run (initial 99)).data 0 = 42 := by decide

-- A leaf's two null-child loads preserve initialized zero, despite nonzero old temporaries.
example :
    ((run { initial 99 with heap := [record none none none (node 0 7 99)] }).heap[0]?.map
      (fun r => r.data 1)) = some 1 := by decide

-- A stale child cache fails the input contract; only the current root cache may be stale.
example : heightValue (M := model) 0 1 (.node (node 1 3 5) .nil .nil) ≠
    (BinaryTree.node (node 1 3 5) .nil .nil).height := by decide
