/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.InsertLeaf

/-! Leaf creation exercises empty-root and both child attachments, payloads, and heap frames. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure.SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Empty
  evalOp o := nomatch o
  evalTest t := nomatch t

private def source (f : Fin 2) : Fin 3 := if f = 0 then 0 else 2

private def initial (key value : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 1 ∨ i = 2 then some 0 else some 1
  data i := if i = 0 then key else value
  heap := [record none none none ⟨0, fun _ => 77⟩,
    record none none none ⟨1, fun _ => 88⟩]

-- A caller obtains a represented fresh leaf, preserves an unrelated record, and charges
-- every allocation, field store, branch and composition jump for arbitrary scalar inputs.
example (key value : ℕ) (side : Fin 2) :
    ∃ y, Executes (insertLeaf source side) (initial key value) y 10 ∧
      Represents y.heap (some 0)
        (.node ⟨2, fun f => if f = 0 then key else value⟩ .nil .nil) ∧
      y.heap[1]? = (initial key value).heap[1]? ∧
      y.ptr 0 = some 2 ∧ y.ptr 1 = some 0 := by
  have vacant : ∃ par, (initial key value).heap[0]? = some par ∧
      par.ptr side.castSucc = none := by
    refine ⟨_, rfl, ?_⟩
    simp [record]
  obtain ⟨y, exec, heap, leaf, _, cursor, rootReg, _, _, _, _⟩ :=
    insertLeaf_correct source side (initial key value) rfl vacant
  refine ⟨y, exec, ?_, ?_, cursor, ?_⟩
  · simpa [initial, source] using leaf
  · simp [heap, initial]
  · simpa [initial] using rootReg

private def run (side : Fin 2) : State model (layout 1 1) :=
  (fun x => (step (insertLeaf source side) x).getD x)^[10] (initial 12 34)

example : ((run 0).heap[0]?.map (fun r => (r.ptr 0, r.ptr 1))) =
    some (some 2, none) := by decide +kernel
example : ((run 1).heap[0]?.map (fun r => (r.ptr 0, r.ptr 1))) =
    some (none, some 2) := by decide +kernel
example : ((run 1).heap[2]?.map (fun r => (r.ptr 2, r.data 0, r.data 1))) =
    some (some 0, 12, 34) := by decide +kernel
example : (run 0).pc = 11 ∧ (run 0).heap.length = 3 ∧ (run 0).ptr 6 = some 1 := by
  decide +kernel

-- Empty-root initialization works without metadata fields and for either side.
example (side : Fin 2) :
    ∃ y, Executes (insertLeaf (fun _ : Fin 1 => (0 : Fin 2)) side)
        ((State.empty : State model (layout 0 0)).setData 0 9) y 9 ∧
      Represents y.heap none (.node ⟨0, fun _ => 9⟩ .nil .nil) ∧
      y.heap.length = 1 ∧ y.ptr 1 = some 0 := by
  obtain ⟨y, exec, _, leaf, len, _, rootReg, _, _, _, _⟩ :=
    insertLeaf_correct (fun _ : Fin 1 => (0 : Fin 2)) side
      ((State.empty : State model (layout 0 0)).setData 0 9) rfl rfl
  refine ⟨y, exec, ?_, ?_, ?_⟩
  · simpa [State.empty, State.setData] using leaf
  · simpa [State.empty, State.setData] using len
  · simpa [State.empty, State.setData] using rootReg

-- An occupied child does not satisfy the vacancy premise.
example : ¬ ∃ par, (run 0).heap[0]? = some par ∧ par.ptr 0 = none := by
  decide +kernel
