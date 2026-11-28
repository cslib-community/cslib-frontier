/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Search

/-! The structured search, assembled and run on a linked three-node tree with an unrelated
record. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine

private abbrev treeModel : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Unit
  evalOp o := nomatch o
  evalTest _ a b := decide (a < b)

private def label (address key : ℕ) : Label treeModel 1 :=
  ⟨address, fun i => if i = 0 then key else 99⟩

private def tree : BinaryTree (Label treeModel 1) :=
  .node (label 0 2) (.node (label 1 1) .nil .nil) (.node (label 2 3) .nil .nil)

private def initial (query : ℕ) : State treeModel (layout 1 1) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else some 3
  data i := if i = 0 then query else 42
  heap := [record (some 1) (some 2) none (label 0 2),
    record none none (some 0) (label 1 1), record none none (some 0) (label 2 3),
    record none none none (label 3 100)]

example : (Structured.search (M := treeModel) (extra := 1) (regs := 1) ()).program =
    [.null 5, .ifPtrEq 0 5 11, .loadData 1 0 0, .ifTest () 0 1 9, .ifTest () 1 0 7,
     .movePtr 5 0, .goto 8, .loadPtr 0 1 0, .goto 10, .loadPtr 0 0 0, .goto 1, .halt] := rfl

private def run (x : State treeModel (layout 1 1)) : State treeModel (layout 1 1) :=
  (fun x => (step (Structured.search ()).program x).getD x)^[30] x

example : ((run (initial 1)).ptr 0 == some 1) = true := by decide
example : ((run (initial 2)).ptr 0 == some 0) = true := by decide
example : ((run (initial 3)).ptr 0 == some 2) = true := by decide
example : ((run (initial 0)).ptr 0 == none) = true := by decide
example : ((run (initial 4)).ptr 0 == none) = true := by decide
example : ((run (initial 1)).data 2 == 42) = true := by decide
example : ((run (initial 1)).ptr 6 == some 3) = true := by decide
example : ((run (initial 4)).pc == 11) = true := by decide

example (query : ℕ) :
    ∃ y time, Executes (Structured.search ()).program (initial query) y time ∧ time ≤ 18 ∧
      SearchResult (initial query) y tree := by
  obtain ⟨y, time, exec, bound, result⟩ := Structured.search_executes (M := treeModel) ()
    (fun _ _ => rfl) (initial query) tree none
    (by simp [Represents, initial, tree, root, label]) rfl rfl
  refine ⟨y, time, exec, bound.trans ?_, result⟩
  have := SearchTree.searchVisits_le_height ((initial query).data 0) (keys tree)
  have height : (keys tree).height = 2 := by decide
  omega
