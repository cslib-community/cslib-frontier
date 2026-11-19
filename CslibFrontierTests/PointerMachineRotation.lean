/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.SearchTree.PointerMachine.Rotation

/-! Both rotation directions with empty and nonempty middle subtrees, payload preservation,
and an unrelated external parent record. -/

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

private def label (address key : ℕ) : Label model 1 :=
  ⟨address, fun i => if i = 0 then key else 99⟩

private def middle : BinaryTree (Label model 1) := .node (label 2 2) .nil .nil

private def initial : State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 then some 0 else some 3
  data _ := 42
  heap := [record (some 1) none (some 3) (label 0 3),
    record none (some 2) (some 0) (label 1 1),
    record none none (some 1) (label 2 2),
    record (some 0) none none (label 3 100)]

private def run (s : State model (layout 1 1)) : State model (layout 1 1) :=
  (fun x => (step rotateRight x).getD x)^[9] s

example : (run initial).ptr 0 = some 1 := by decide
example : (run initial).pc = 9 := by decide
example : ((run initial).heap[0]?.map (fun r => r.ptr 0)) = some (some 2) := by decide
example : ((run initial).heap[0]?.map (fun r => r.ptr 2)) = some (some 1) := by decide
example : ((run initial).heap[1]?.map (fun r => r.ptr 1)) = some (some 0) := by decide
example : ((run initial).heap[1]?.map (fun r => r.ptr 2)) = some (some 3) := by decide
example : ((run initial).heap[2]?.map (fun r => r.ptr 2)) = some (some 0) := by decide
example : ((run initial).heap[2]?.map (fun r => r.data 1)) = some 99 := by decide
-- Reconnecting the external parent's child is intentionally a separate operation.
example : ((run initial).heap[3]?.map (fun r => r.ptr 0)) = some (some 0) := by decide

private theorem distinct :
    AddressesDistinct
      (.node (label 0 3) (.node (label 1 1) .nil middle) .nil) := by
  have classify (p : PosNum) (u : Label model 1)
      (h : (BinaryTree.node (label 0 3) (.node (label 1 1) .nil middle) .nil).get p =
        some u) :
      (p = .one ∧ u.address = 0) ∨ (p = .bit0 .one ∧ u.address = 1) ∨
        (p = .bit0 (.bit1 .one) ∧ u.address = 2) := by
    cases p with
    | one => cases Option.some.inj h; exact .inl ⟨rfl, rfl⟩
    | bit1 p => cases p <;> cases h
    | bit0 p =>
      cases p with
      | one => cases Option.some.inj h; exact .inr (.inl ⟨rfl, rfl⟩)
      | bit0 p => cases p <;> cases h
      | bit1 p =>
        cases p with
        | one => cases Option.some.inj h; exact .inr (.inr ⟨rfl, rfl⟩)
        | bit0 p => cases p <;> cases h
        | bit1 p => cases p <;> cases h
  intro p q u v hp hq eq
  rcases classify p u hp with ⟨rfl, hu⟩ | ⟨rfl, hu⟩ | ⟨rfl, hu⟩ <;>
    rcases classify q v hq with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;>
    simp_all

private theorem rotated :
    ∃ t, Executes rotateRight initial t 10 ∧
      Represents t.heap (some 3)
        (.node (label 1 1) .nil (.node (label 0 3) middle .nil)) ∧
      t.ptr 0 = some 1 ∧ t.data = initial.data ∧ t.heap.length = initial.heap.length ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → t.ptr i = initial.ptr i) ∧
      (∀ z, z ≠ 1 → z ≠ 0 → root middle ≠ some z →
        t.heap[z]? = initial.heap[z]?) := by
  apply rotateRight_represents initial (label 1 1) (label 0 3) .nil middle .nil (some 3)
  · simp [Represents, initial, middle, root, label]
  · exact distinct
  · rfl
  · rfl

private def emptyMiddle : State model (layout 1 1) :=
  { initial with heap := initial.heap.set 1 (record none none (some 0) (label 1 1)) }

example : (run emptyMiddle).ptr 0 = some 1 := by decide
example : ((run emptyMiddle).heap[0]?.map (fun r => r.ptr 0)) = some none := by decide
example : ((run emptyMiddle).heap[2]?.map (fun r => r.ptr 2)) = some (some 1) := by decide

-- Two positions cannot own the same heap record in the rotation invariant.
example : ¬ AddressesDistinct
    (.node (label 0 3) (.node (label 0 1) .nil .nil) .nil) := by
  intro h
  have bad := h .one (.bit0 .one) (label 0 3) (label 0 1) rfl rfl rfl
  cases bad


-- The inverse rotation is a concrete program and restores the represented original subtree.
example :
    ∃ s t, Executes rotateRight initial s 10 ∧
      Executes rotateLeft { s with pc := 0 } t 10 ∧
      Represents t.heap (some 3)
        (.node (label 0 3) (.node (label 1 1) .nil middle) .nil) ∧
      t.ptr 0 = some 0 ∧ t.ptr 1 = initial.ptr 1 ∧ t.ptr 6 = initial.ptr 6 ∧
      t.heap[3]? = initial.heap[3]? := by
  obtain ⟨s, first, rep, cursor, _, _, frame, heapFrame⟩ := rotated
  obtain ⟨t, second, rep', cursor', _, _, frame', heapFrame'⟩ :=
    rotateLeft_represents { s with pc := 0 } (label 0 3) (label 1 1)
      .nil middle .nil (some 3) rep distinct.rotateRight cursor rfl
  exact ⟨s, t, first, second, rep', cursor',
    (frame' 1 (by decide) (by decide) (by decide) (by decide)).trans
      (frame 1 (by decide) (by decide) (by decide) (by decide)),
    (frame' 6 (by decide) (by decide) (by decide) (by decide)).trans
      (frame 6 (by decide) (by decide) (by decide) (by decide)),
    (heapFrame' 3 (by decide) (by decide) (by decide)).trans
      (heapFrame 3 (by decide) (by decide) (by decide))⟩

example : AddressesDistinct
    (.node (label 0 3) (.node (label 1 1) .nil middle) .nil) :=
  distinct.rotateRight.rotateLeft

private def runLeft (s : State model (layout 1 1)) : State model (layout 1 1) :=
  (fun x => (step rotateLeft x).getD x)^[9] s

example : (runLeft { run initial with pc := 0 }).ptr 0 = some 0 := by decide
example : ((runLeft { run initial with pc := 0 }).heap[2]?.map (fun r => r.ptr 2)) =
    some (some 1) := by decide
example : (runLeft { run emptyMiddle with pc := 0 }).ptr 0 = some 0 := by decide
