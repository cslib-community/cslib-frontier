/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Rotation

/-! Concrete composed rotations repair deliberately stale pivot heights and preserve
keys, the root register, a client query and an unrelated record. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine
open AVLTree.PointerMachine (Matches)

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Bool
  Test := Empty
  evalOp op a b := if op then max a b + 1 else 0
  evalTest t := nomatch t

private def label (address key height : ℕ) : Label model 1 :=
  ⟨address, fun f => if f = 0 then key else height⟩

private def initial (right middle : Bool) (oldHeight newHeight : ℕ) :
    State model (layout 1 1) where
  pc := 0
  ptr i := if i = 0 ∨ i = 1 then some 0 else none
  data _ := 77
  heap := [
    record (if right then some 1 else none) (if right then none else some 1) none
      (label 0 (if right then 10 else 5) oldHeight),
    record (if right then none else if middle then some 2 else none)
      (if right && middle then some 2 else none) (some 0)
      (label 1 (if right then 5 else 10) newHeight),
    record none none (some 1) (label 2 7 1),
    record none none none (label 3 55 55)]

private def run (right middle : Bool) : State model (layout 1 1) :=
  let code : List (Instr model (layout 1 1)) :=
    if right then AVLTree.PointerMachine.rotateRight false true 1
    else AVLTree.PointerMachine.rotateLeft false true 1
  (fun x => (step code x).getD x)^[39] (initial right middle 99 98)

example : (run true true).pc = 38 ∧ (run false true).pc = 38 := by decide +kernel
example : (run true true).ptr 0 = some 1 ∧ (run false true).ptr 0 = some 1 := by decide +kernel
example : (run true true).ptr 6 = some 0 ∧ (run false true).ptr 6 = some 0 := by decide +kernel
example : (run true true).ptr 1 = some 0 ∧ (run false true).ptr 1 = some 0 := by decide +kernel
example : (run true true).data 0 = 77 ∧ (run false true).data 0 = 77 := by decide +kernel
example : ((run true true).heap[0]?.map (fun r => r.data 1)) = some 2 ∧
    ((run true true).heap[1]?.map (fun r => r.data 1)) = some 3 := by decide +kernel
example : ((run false true).heap[0]?.map (fun r => r.data 1)) = some 2 ∧
    ((run false true).heap[1]?.map (fun r => r.data 1)) = some 3 := by decide +kernel
example : ((run true false).heap[0]?.map (fun r => r.data 1)) = some 1 ∧
    ((run true false).heap[1]?.map (fun r => r.data 1)) = some 2 := by decide +kernel
example : ((run false false).heap[0]?.map (fun r => r.data 1)) = some 1 ∧
    ((run false false).heap[1]?.map (fun r => r.data 1)) = some 2 := by decide +kernel
example : ((run true true).heap[3]?.map (fun r => r.data 0)) = some 55 ∧
    ((run false true).heap[3]?.map (fun r => r.data 0)) = some 55 := by decide +kernel

private theorem distinct (h₀ h₁ : ℕ) :
    AddressesDistinct (.node (label 0 10 h₀) (.node (label 1 5 h₁) .nil .nil) .nil) := by
  have classify (p : PosNum) (u : Label model 1)
      (h : (BinaryTree.node (label 0 10 h₀) (.node (label 1 5 h₁) .nil .nil) .nil).get p =
        some u) :
      (p = .one ∧ u.address = 0) ∨ (p = .bit0 .one ∧ u.address = 1) := by
    cases p with
    | one => cases Option.some.inj h; exact .inl ⟨rfl, rfl⟩
    | bit1 p => cases p <;> cases h
    | bit0 p =>
      cases p with
      | one => cases Option.some.inj h; exact .inr ⟨rfl, rfl⟩
      | bit0 p => cases p <;> cases h
      | bit1 p => cases p <;> cases h
  intro p q u v hp hq eq
  rcases classify p u hp with ⟨rfl, hu⟩ | ⟨rfl, hu⟩ <;>
    rcases classify q v hq with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;> simp_all

-- The general theorem accepts arbitrary stale pivot caches and establishes a full AVL match.
example (h₀ h₁ : ℕ) :
    ∃ t tree, Executes (AVLTree.PointerMachine.rotateRight false true 1)
        (initial true false h₀ h₁) t 39 ∧ Represents t.heap none tree ∧
      Matches id 1 tree (.node 5 2 .nil (.node 10 1 .nil .nil)) ∧
      t.ptr 0 = root tree ∧ t.ptr 6 = some 0 := by
  obtain ⟨t, exec, rep, matched, _, _, cursor, _, _, _, saved, _⟩ :=
    AVLTree.PointerMachine.rotateRight_correct (M := model) false true id
      (fun _ _ => rfl) (fun _ _ => rfl) 1 (by decide +kernel) (initial true false h₀ h₁)
      (label 1 5 h₁) (label 0 10 h₀) .nil .nil .nil .nil .nil .nil none
      (by simp [Represents, initial, record, label, root])
      (distinct h₀ h₁) trivial trivial trivial trivial trivial trivial rfl rfl
  exact ⟨t, _, exec, rep, matched, cursor, saved⟩
