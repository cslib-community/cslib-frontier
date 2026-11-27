/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Seek

/-! Search retains the parent at vacant links and certifies the complete comparison path. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure.SearchTree.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Unit
  evalOp o := nomatch o
  evalTest _ a b := decide (a < b)

private def label (address key : ℕ) : Label model 1 :=
  ⟨address, fun i => if i = 0 then key else 77⟩

private def tree : BinaryTree (Label model 1) :=
  .node (label 0 20) (.node (label 1 10) .nil .nil) (.node (label 2 30) .nil .nil)

private def initial (query : ℕ) : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else some 2
  data i := if i = 0 then query else 77
  heap := [record (some 1) (some 2) none (label 0 20),
    record none none (some 0) (label 1 10), record none none (some 0) (label 2 30)]

-- The theorem supplies linked focus and context, all path comparisons, and agreement with
-- functional contains for every query, while the original whole tree is unchanged.
example (query : ℕ) :
    ∃ y time cs focus, Executes (seek ()) (initial query) y time ∧
      time ≤ 7 * Cslib.DataStructure.SearchTree.searchVisits query (keys tree) + 4 ∧
      SeekResult (initial query) y tree focus cs := by
  apply seek_correct () (fun _ _ => rfl) (initial query) tree
  · simp [Represents, initial, tree, root, label]
  · rfl
  · rfl

private def run (query steps : ℕ) : State model (layout 1 1) :=
  (fun x => (step (seek ()) x).getD x)^[steps] (initial query)

-- A right-then-left miss remembers the last nonnull parent.
example : (run 25 17).ptr 0 = none ∧ (run 25 17).ptr 2 = some 2 ∧
    (run 25 17).pc = 13 := by decide +kernel
-- Found children retain their parent; finding the original root has a null parent.
example : (run 10 13).ptr 0 = some 1 ∧ (run 10 13).ptr 2 = some 0 := by decide +kernel
example : (run 20 7).ptr 0 = some 0 ∧ (run 20 7).ptr 2 = none := by decide +kernel
example : (run 25 17).heap = (initial 25).heap ∧ (run 25 17).data 0 = 25 ∧
    (run 25 17).data 2 = 77 ∧ (run 25 17).ptr 1 = some 0 ∧
    (run 25 17).ptr 6 = some 2 := by
  exact ⟨rfl, by decide +kernel⟩

private def missContext : List (Frame model 1) :=
  [.left (label 2 30) .nil, .right (.node (label 1 10) .nil .nil) (label 0 20)]

example : plug missContext .nil = tree := rfl
example : SearchPath (M := model) 25 missContext := by
  simp [SearchPath, missContext, label]
example : ¬ SearchPath (M := model) 35 missContext := by
  simp [SearchPath, missContext, label]
example : ContextRep (run 25 17).heap none missContext := by
  change ContextRep (initial 25).heap none missContext
  simp [ContextRep, initial, missContext, root, label, contextParent, Represents]

-- Empty input terminates in four instructions, retaining an empty context and null parent.
example :
    ∃ y time cs focus, Executes (seek ()) (State.empty : State model (layout 0 0)) y time ∧
      time ≤ 4 ∧ SeekResult State.empty y .nil focus cs := by
  simpa [keys, BinaryTree.map, Cslib.DataStructure.SearchTree.searchVisits] using
    seek_correct () (fun _ _ => rfl)
    (State.empty : State model (layout 0 0)) .nil trivial rfl rfl
