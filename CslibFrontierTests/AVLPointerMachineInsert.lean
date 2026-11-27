/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Insert
import Mathlib.Tactic.FinCases

/-! Full insertion handles duplicates, empty roots, and single/double ancestor rotations,
with explicit payload sources and the existing functional AVL result. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine
open AVLTree.PointerMachine (Matches InsertResult)

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Bool
  Test := Fin 3
  evalOp op a b := if op then max a b + 1 else 0
  evalTest test a b := if test = 0 then decide (a < b)
    else if test = 1 then decide (b + 1 < a) else decide (a ≤ b)

private def label (address key height : ℕ) : Label model 2 :=
  ⟨address, fun f => if f = 0 then key else if f = 1 then height else 100 + address⟩

private def tree : BinaryTree (Label model 2) :=
  .node (label 0 20 2) (.node (label 1 10 1) .nil .nil) .nil

private def original : AVLTree ℕ := .node 20 2 (.node 10 1 .nil .nil) .nil

private def initial (query : ℕ) : State model (layout 2 2) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else none
  data i := if i = 0 then query else 999
  heap := [record (some 1) none none (label 0 20 2),
    record none none (some 0) (label 1 10 1),
    record none none none (label 2 80 1)]

private def source (_ : Fin 3) : Fin 4 := 3

private def sampleCode : List (Instr model (layout 2 2)) :=
  AVLTree.PointerMachine.insert (M := model) false true 0 1 2 1 source

-- An arbitrary query has an actual finite-program execution with the complete insertion
-- outcome. It preserves non-height scalar fields of all old records, including the unrelated
-- third record; it does not assert a full frame for that record's pointer and height fields.
example (query : ℕ) : ∃ t result time,
    Executes sampleCode (initial query) t time ∧ time ≤ 315 ∧
    InsertResult id 1 source (initial query) t tree result original := by
  have valid : original.Valid := by
    simp [original, AVLTree.Valid, AVLTree.Ordered, AVLTree.HeightConsistent,
      AVLTree.Balanced, AVLTree.toBinaryTree, SearchTree.Ordered, SearchTree.elements]
  obtain ⟨t, result, time, exec, bound, _, outcome⟩ :=
    AVLTree.PointerMachine.insert_correct (M := model) false true 0 1 2 id
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) 1 (by decide +kernel) source
      (by intro f _ _; simp [source]) (initial query) tree original
      (by simp [Represents, initial, tree, root, label])
      (by simp [tree, AddressesDistinct.node_iff, addresses, BinaryTree.map,
        SearchTree.elements, label])
      (by simp [Matches, tree, original, label]) valid rfl rfl rfl
  exact ⟨t, result, time, exec, bound, outcome⟩

private def after (query : ℕ) : State model (layout 2 2) :=
  (fun x => (step sampleCode x).getD x)^[315] (initial query)

-- Single rotation promotes the old left child; double rotation promotes the fresh node.
example : (after 5).ptr 1 = some 1 ∧ (after 5).heap.length = 4 := by decide +kernel
example : (after 15).ptr 1 = some 3 ∧ (after 15).heap.length = 4 := by decide +kernel
example : ((after 15).heap[3]?).map (fun n => (n.data 0, n.data 1, n.data 2)) =
    some (15, 2, 999) := by decide +kernel
example : ((after 15).heap[2]?).map (fun n => (n.data 0, n.data 2)) =
    some (80, 102) := by decide +kernel
example : (after 20).heap.length = 3 ∧ (after 20).ptr 1 = some 0 ∧
    (after 20).data 0 = 20 ∧ (after 20).data 3 = 999 := by decide +kernel

-- A source layout without optional payload fields is also admissible.
example : ∃ t, ∃ (result : BinaryTree (Label model 1)), ∃ time,
    Executes (AVLTree.PointerMachine.insert (M := model) false true 0 1 2 1
      (fun _ : Fin 2 => (0 : Fin 3)))
      (State.empty : State model (layout 1 1)) t time ∧ time ≤ 32 ∧
    Matches (M := model) id 1 result (.node 0 1 .nil .nil) ∧ t.heap.length ≤ 1 := by
  obtain ⟨t, result, time, exec, bound, _, outcome⟩ :=
    AVLTree.PointerMachine.insert_correct (M := model) false true 0 1 2 id
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) 1 (by decide +kernel)
      (fun _ : Fin 2 => (0 : Fin 3))
      (by intro f h1 h0; fin_cases f <;> contradiction)
      (State.empty : State model (layout 1 1)) .nil .nil trivial
      AddressesDistinct.nil trivial AVLTree.valid_nil rfl rfl rfl
  exact ⟨t, result, time, exec, bound, outcome.matched, outcome.space.2⟩
