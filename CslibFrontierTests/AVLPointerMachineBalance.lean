/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Balance
import Mathlib.Tactic.FinCases

/-! All five balance paths: height repair, both single rotations, and both double rotations.
Every input has a stale root cache, a payload field, client registers, and an external record. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine
open AVLTree.PointerMachine (Matches)

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Bool
  Test := Bool
  evalOp op a b := if op then max a b + 1 else 0
  evalTest test a b := if test then decide (a ≤ b) else decide (b + 1 < a)

private def label (address key height : ℕ) : Label model 2 :=
  ⟨address, fun f => if f = 0 then key else if f = 1 then height else 1000 + address⟩

private def left (c : Fin 5) : BinaryTree (Label model 2) :=
  if c = 0 then .node (label 1 1 1) .nil .nil
  else if c = 1 then .node (label 1 2 2) (.node (label 2 1 1) .nil .nil) .nil
  else if c = 3 then .node (label 1 1 2) .nil (.node (label 2 2 1) .nil .nil)
  else .nil

private def right (c : Fin 5) : BinaryTree (Label model 2) :=
  if c = 0 then .node (label 2 3 1) .nil .nil
  else if c = 2 then .node (label 1 2 2) .nil (.node (label 2 3 1) .nil .nil)
  else if c = 4 then .node (label 1 3 2) (.node (label 2 2 1) .nil .nil) .nil
  else .nil

private def avl : BinaryTree (Label model 2) → AVLTree ℕ
  | .nil => .nil
  | .node x l r => .node (x.data 0) (x.data 1) (avl l) (avl r)

private def rootLabel (c : Fin 5) :=
  label 0 (if c = 0 then 2 else if c = 1 ∨ c = 3 then 3 else 1) 99

private def initial (c : Fin 5) : State model (layout 2 2) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else none
  data _ := 77
  heap := [
    record (root (left c)) (root (right c)) none (rootLabel c),
    record (if c = 1 ∨ c = 4 then some 2 else none)
      (if c = 2 ∨ c = 3 then some 2 else none) (some 0)
      (label 1 (if c = 0 ∨ c = 3 then 1 else if c = 4 then 3 else 2) (if c = 0 then 1 else 2)),
    record none none (if c = 0 then some 0 else some 1)
      (label 2 (if c = 0 ∨ c = 2 then 3 else if c = 1 then 1 else 2) 1),
    record none none none (label 3 55 55)]

private def sampleCode : List (Instr model (layout 2 2)) :=
  AVLTree.PointerMachine.balance false true false true 1

private def after (c : Fin 5) : State model (layout 2 2) :=
  (fun x => (step sampleCode x).getD x)^[121] (initial c)

-- The same valid primitive contracts and representation hypotheses satisfy the general theorem
-- in all five branches; this also checks that payload and client-frame conclusions are usable.
example (c : Fin 5) : ∃ t, ∃ (tree : BinaryTree (Label model 2)), ∃ time,
    Executes sampleCode (initial c) t time ∧ time ≤ 121 ∧
    Matches id 1 tree (AVLTree.balance ((rootLabel c).data 0) (avl (left c)) (avl (right c))) ∧
    t.ptr 6 = some 0 ∧ t.data 3 = 77 ∧
    (t.heap[2]?).map (fun n => n.data 2) = some 1002 := by
  have ml : Matches id 1 (left c) (avl (left c)) := by
    fin_cases c <;> simp [left, avl, Matches, label]
  have mr : Matches id 1 (right c) (avl (right c)) := by
    fin_cases c <;> simp [right, avl, Matches, label]
  obtain ⟨t, tree, time, exec, bound, _, matched, _, _, _, _, _, saved, _, data, _, payload⟩ :=
    AVLTree.PointerMachine.balance_correct false true false true id
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      1 (by decide +kernel) (initial c) (rootLabel c) (left c) (right c)
      (avl (left c)) (avl (right c)) none
      (by fin_cases c <;> simp [Represents, initial, left, right, rootLabel, root, record, label])
      (by fin_cases c <;> simp [left, right, rootLabel, AddressesDistinct.node_iff,
        addresses, BinaryTree.map, SearchTree.elements, label])
      ml mr (by fin_cases c <;> simp [left, avl, label, AVLTree.HeightConsistent])
      (by fin_cases c <;> simp [right, avl, label, AVLTree.HeightConsistent]) rfl rfl
  exact ⟨t, tree, time, exec, bound, matched, saved,
    data 3 (by decide +kernel) (by decide +kernel), payload 2 2 (by decide +kernel)⟩

example (c : Fin 5) :
    (after c).ptr 0 = some (if c = 0 then 0 else if c = 1 ∨ c = 2 then 1 else 2) := by
  fin_cases c <;> decide +kernel
example (c : Fin 5) : (after c).ptr 1 = some 0 ∧ (after c).ptr 6 = some 0 ∧
    (after c).data 0 = 77 ∧ (after c).data 3 = 77 := by
  fin_cases c <;> decide +kernel
example (c : Fin 5) : ((after c).heap[3]?).map (fun n => n.data 0) = some 55 ∧
    ((after c).heap[2]?).map (fun n => n.data 2) = some 1002 := by
  fin_cases c <;> decide +kernel
example (c : Fin 5) : ((after c).deref 0).map (fun n => (n.data 0, n.data 1)) = some (2, 2) := by
  fin_cases c <;> decide +kernel
