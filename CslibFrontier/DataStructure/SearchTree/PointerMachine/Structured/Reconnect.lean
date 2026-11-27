/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers

/-!
# Reconnecting and ascending as structured pointer-machine programs

`Structured.reconnect` is the program of `Reconnect` written as a structured program: cursor
zero holds the promoted node of a rotation and register six the former root; the program
installs the cursor in root register one at the overall root, and otherwise replaces the
parent's link to the former root. `Structured.ascend` follows the parent link of the cursor.

## Main definitions

* `reconnect`, `ascend`: the programs.

## Main results

* `reconnect_root`, `reconnect_child`: reconnecting takes four instructions at the root and at
  most eight below a parent, and changes one link.
* `ascend_correct`: ascending is one load.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

open Register in
/-- Reconnect the rotated subtree at cursor zero, replacing the former root in register six.
Scratch registers two, three and five may change. -/
@[expose] def reconnect : Code M (layout extra regs) := pm[
  par ← cur[parent];
  nul ← null;
  if par = nul then [ top ← cur ] else [
    link ← par[left];
    if link = old then [ par[left] ← cur ] else [ par[right] ← cur ] ] ]

/-- Reconnecting the overall root takes four instructions, leaves the heap and scalar registers
unchanged, and installs the cursor in root register one. -/
theorem reconnect_root (s : State M (layout extra regs))
    (node : Record M (layout extra regs))
    (read : s.deref 0 = some node) (parent : node.ptr 2 = none) :
    ∃ t, ExecWithin reconnect s t 4 ∧ t.heap = s.heap ∧ t.data = s.data ∧
      t.ptr 1 = s.ptr 0 ∧
      (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 5 → t.ptr i = s.ptr i) := by
  apply WP.exists_execWithin
  pm_exec [reconnect, read, parent]
  exact ⟨by omega, trivial, trivial, by simp, fun i h1 h2 h5 => by simp [h1, h2, h5]⟩

/-- Reconnecting below a parent takes at most eight instructions. Exactly one parent child link
changes from the saved former root to the cursor; all other records and fields are preserved.
The caller supplies the parent's old child link, not the resulting heap. -/
theorem reconnect_child (s : State M (layout extra regs))
    (node par : Record M (layout extra regs)) (a : ℕ)
    (read : s.deref 0 = some node) (parent : node.ptr 2 = some a)
    (lookup : s.heap[a]? = some par)
    (attached : par.ptr 0 = s.ptr 6 ∨ par.ptr 1 = s.ptr 6) :
    ∃ t, ∃ field : Fin 3, ExecWithin reconnect s t 8 ∧
      (field = 0 ∨ field = 1) ∧ par.ptr field = s.ptr 6 ∧
      t.heap = s.heap.modify a (fun r => { r with ptr := Function.update r.ptr field (s.ptr 0) }) ∧
      t.data = s.data ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 5 → t.ptr i = s.ptr i) := by
  simp only [exists_and_left]
  apply WP.exists_execWithin
  by_cases h : par.ptr 0 = s.ptr 6
  · pm_exec [reconnect, read, parent, lookup, h]
    exact ⟨by omega, 0, .inl rfl, h, by simp [State.modify], by simp,
      fun i h2 h3 h5 => by simp [h2, h3, h5]⟩
  · pm_exec [reconnect, read, parent, lookup, h]
    exact ⟨by omega, 1, .inr rfl, attached.resolve_left h, by simp [State.modify], by simp,
      fun i h2 h3 h5 => by simp [h2, h3, h5]⟩

open Register in
/-- Move the cursor to its parent. -/
@[expose] def ascend : Code M (layout extra regs) := pm[ cur ← cur[parent] ]

/-- Following a represented nonempty focus's parent takes one load. The heap, scalars and every
other pointer register survive; at the root the resulting cursor is null. -/
theorem ascend_correct (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (label : Label M extra) (l r : BinaryTree (Label M extra))
    (rep : Represents s.heap (contextParent cs) (.node label l r))
    (cursor : s.ptr 0 = some label.address) :
    ∃ t, ExecWithin ascend s t 1 ∧
      t.heap = s.heap ∧ t.data = s.data ∧ t.ptr 0 = contextParent cs ∧
      (∀ i, i ≠ 0 → t.ptr i = s.ptr i) := by
  have read : s.deref 0 = some (record (root l) (root r) (contextParent cs) label) := by
    simp [State.deref, cursor, rep.1]
  apply WP.exists_execWithin
  pm_exec [ascend, read, record]
  exact ⟨by omega, trivial, trivial, by simp, fun i hi => by simp [hi]⟩

/-! Frames of `reconnect` and `ascend`, for the programs that call them. -/

@[simp] theorem reconnect_keepsSize : (reconnect : Code M (layout extra regs)).KeepsSize := by
  pm_frame

@[simp] theorem reconnect_dataDests : (reconnect : Code M (layout extra regs)).dataDests = [] :=
  rfl

@[simp] theorem reconnect_fieldDests : (reconnect : Code M (layout extra regs)).fieldDests = [] :=
  rfl

@[simp] theorem ascend_keepsSize : (ascend : Code M (layout extra regs)).KeepsSize := by
  pm_frame

@[simp] theorem ascend_dataDests : (ascend : Code M (layout extra regs)).dataDests = [] := rfl

@[simp] theorem ascend_fieldDests : (ascend : Code M (layout extra regs)).fieldDests = [] := rfl

end Cslib.DataStructure.SearchTree.PointerMachine.Structured
