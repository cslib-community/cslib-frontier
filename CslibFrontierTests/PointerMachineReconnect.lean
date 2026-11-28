/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.ReconnectContext
import Mathlib.Tactic.FinCases

/-! Reconnect either child slot or the overall root, preserving unrelated records and data. -/

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

private def label (a : ℕ) : Label model 0 := ⟨a, fun _ => a⟩

private def parentRecord (left : Bool) : Record model (layout 0 0) :=
  record (if left then some 1 else some 3) (if left then some 3 else some 1)
    none (label 2)

private def initial (left : Bool) : State model (layout 0 0) where
  pc := 0
  ptr i := if i = 0 then some 0 else if i = 1 then some 2 else if i = 6 then some 1 else none
  data _ := 42
  heap := [record none (some 1) (some 2) (label 0),
    record none none (some 0) (label 1), parentRecord left, record none none (some 2) (label 3)]

private def run (s : State model (layout 0 0)) : State model (layout 0 0) :=
  (fun t => (step reconnect t).getD t)^[7] s

example : ((run (initial true)).heap[2]?.map (fun r => r.ptr 0)) = some (some 0) := by decide
example : ((run (initial false)).heap[2]?.map (fun r => r.ptr 1)) = some (some 0) := by decide
example : ((run (initial true)).heap[3]?.map (fun r => r.data 0)) = some 3 := by decide
example : (run (initial false)).ptr 1 = some 2 := by decide
example : (run (initial true)).ptr 6 = some 1 := by decide
example : (run (initial true)).data 0 = 42 := by decide

example (left : Bool) :
    ∃ t, ∃ field : Fin 3, Executes reconnect (initial left) t 7 ∧
      (field = 0 ∨ field = 1) ∧ (parentRecord left).ptr field = (initial left).ptr 6 ∧
      t.heap = (initial left).heap.modify 2
        (fun r => { r with ptr := Function.update r.ptr field (some 0) }) ∧
      t.data = (initial left).data ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 5 → t.ptr i = (initial left).ptr i) := by
  apply reconnect_child (initial left) (record none (some 1) (some 2) (label 0))
    (parentRecord left) 2 rfl
  · rfl
  · rfl
  · rfl
  · cases left <;> simp [parentRecord, record, initial]

private def atRoot : State model (layout 0 0) :=
  { (initial true).setPtr 1 (some 1) with heap :=
      [record none (some 1) none (label 0), record none none (some 0) (label 1)] }

example : (run atRoot).ptr 1 = some 0 := by decide

example : ∃ t, Executes reconnect atRoot t 5 ∧ t.heap = atRoot.heap ∧
    t.data = atRoot.data ∧ t.ptr 1 = atRoot.ptr 0 ∧
    (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 5 → t.ptr i = atRoot.ptr i) :=
  reconnect_root atRoot (record none (some 1) none (label 0)) rfl rfl rfl

example (left : Bool) : (initial left).Valid := by
  constructor
  · intro r a h
    dsimp [initial] at h ⊢
    split_ifs at h <;> simp_all <;> omega
  · intro n hn f a h
    simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    all_goals
      fin_cases f <;> cases left <;> simp_all [initial, record, parentRecord, label] <;> omega

example : atRoot.Valid := by
  simp only [State.Valid, atRoot, initial, record, label, State.setPtr]
  constructor
  · intro r a h
    simp only [Function.update_apply] at h
    split_ifs at h <;> simp_all <;> omega
  · simp

-- The local rotation contract reconstructs the complete tree on either side of a parent.
private def oldFocus : BinaryTree (Label model 0) :=
  .node (label 1) (.node (label 0) .nil .nil) .nil

private def newFocus : BinaryTree (Label model 0) :=
  .node (label 0) .nil (.node (label 1) .nil .nil)

private def ancestors (left : Bool) : List (Frame model 0) :=
  [if left then .left (label 2) (.node (label 3) .nil .nil)
    else .right (.node (label 3) .nil .nil) (label 2)]

private def beforeHeap (left : Bool) : List (Record model (layout 0 0)) :=
  [record none none (some 1) (label 0), record (some 0) none (some 2) (label 1),
    parentRecord left, record none none (some 2) (label 3)]

example (left : Bool) : ∃ t time, Executes reconnect (initial left) t time ∧ time ≤ 7 ∧
    ReconnectResult (initial left) (ancestors left) newFocus t := by
  apply reconnect_context (beforeHeap left) (initial left) (ancestors left) oldFocus newFocus
  · cases left <;> simp [beforeHeap, ancestors, plug, oldFocus, Represents, root,
      parentRecord, record, label]
  · cases left <;> simp [ancestors, plug, oldFocus, AddressesDistinct.node_iff,
      addresses, BinaryTree.map, Cslib.DataStructure.SearchTree.elements, label]
  · cases left <;> simp [initial, ancestors, contextParent, newFocus, Represents, root, label]
  · simp [newFocus, AddressesDistinct.node_iff, addresses, BinaryTree.map,
      Cslib.DataStructure.SearchTree.elements, label]
  · decide
  · intro a ha
    simp only [oldFocus, addresses, BinaryTree.map, Cslib.DataStructure.SearchTree.elements,
      label, Finset.mem_insert, Finset.mem_union, Finset.notMem_empty, or_false,
      not_or] at ha
    rcases a with _ | _ | a <;> simp_all [initial, beforeHeap]
  · intro h; cases h
  · intro h; cases h
  · rfl
  · rfl
  · rfl
  · cases left <;> rfl
