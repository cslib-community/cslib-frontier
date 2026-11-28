/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Allocation

/-! Allocation initializes a key and payload, retains an existing tree, and charges all stores. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure.SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Empty
  evalOp o := nomatch o
  evalTest t := nomatch t

private def oldLabel : Label model 1 := ⟨0, fun _ => 77⟩

private def oldTree : BinaryTree (Label model 1) := .node oldLabel .nil .nil

private def initial (key value : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 2 then some 0 else none
  data i := if i = 0 then key else value
  heap := [record none none none oldLabel]

private def source (f : Fin 2) : Fin 3 := if f = 0 then 0 else 2

example (key value : ℕ) : (initial key value).Valid := by
  simp [State.Valid, initial, record, oldLabel]

example (key value : ℕ) :
    ∃ y, Executes (allocate source) (initial key value) y 5 ∧
      Represents y.heap none oldTree ∧
      Represents y.heap (some 0)
        (.node ⟨1, fun f => if f = 0 then key else value⟩ .nil .nil) ∧
      y.heap.length = 2 ∧ y.ptr 0 = some 1 ∧ y.data = (initial key value).data := by
  obtain ⟨y, exec, heap, ptr, data, leaf⟩ := allocate_correct source (initial key value) rfl
  have old : Represents (initial key value).heap none oldTree := by
    simp [Represents, initial, oldTree, root, oldLabel]
  refine ⟨y, exec, ?_, ?_, ?_, ?_, data⟩
  · rw [heap]
    exact old.append _
  · simpa [initial, source] using leaf
  · simp [heap, initial]
  · simp [ptr, initial]

private def run (key value : ℕ) : State model (layout 1 1) :=
  (fun x => (step (allocate source) x).getD x)^[5] (initial key value)

example : (run 12 34).ptr 0 = some 1 := by decide
example : ((run 12 34).heap[1]?.map (fun r => r.data 0)) = some 12 := by decide
example : ((run 12 34).heap[1]?.map (fun r => r.data 1)) = some 34 := by decide
example : ((run 12 34).heap[1]?.map (fun r => r.ptr 2)) = some (some 0) := by decide
example : (run 12 34).pc = 4 := by decide

-- Empty-heap initialization, including the layout without metadata fields.
example :
    ∃ y, Executes (allocate (fun _ : Fin 1 => (0 : Fin 2)))
        ((State.empty : State model (layout 0 0)).setData 0 9) y 4 ∧
      Represents y.heap none (.node ⟨0, fun _ => 9⟩ .nil .nil) ∧ y.heap.length = 1 := by
  obtain ⟨y, exec, heap, _, _, leaf⟩ :=
    allocate_correct (fun _ : Fin 1 => (0 : Fin 2))
      ((State.empty : State model (layout 0 0)).setData 0 9) rfl
  refine ⟨y, exec, ?_, ?_⟩
  · simpa [State.empty, State.setData] using leaf
  · simp [heap, State.empty, State.setData]
