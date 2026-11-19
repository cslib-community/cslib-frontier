/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-!
# Reconnecting a rotated subtree

Cursor zero holds the promoted node and register six holds the former root.
The program reads the promoted node's parent link. At the overall root it updates root
register one; otherwise it replaces the parent's link to the former root.
This is a local attachment contract; whole-tree composition additionally needs the
rotation's representation and separation invariants.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Reconnect the rotated subtree at cursor zero, replacing the former root in register six.
Scratch registers two, three and five may change. -/
@[expose] def reconnect : List (Instr M (layout extra regs)) :=
  [.loadPtr 2 2 0, .null 5, .ifPtrEq 2 5 9, .loadPtr 3 0 2, .ifPtrEq 3 6 7,
   .storePtr 1 2 0, .halt, .storePtr 0 2 0, .halt, .movePtr 1 0, .halt]

private def tick (i : Instr M (layout extra regs)) (s : State M (layout extra regs)) :=
  { i.effect s with pc := s.pc + 1 }

/-- Reconnecting the overall root takes five instructions, leaves the heap and scalar
registers unchanged, and installs the cursor in root register one. -/
theorem reconnect_root (s : State M (layout extra regs))
    (node : Record M (layout extra regs)) (pc : s.pc = 0)
    (read : s.deref 0 = some node) (parent : node.ptr 2 = none) :
    ∃ t, Executes reconnect s t 5 ∧ t.heap = s.heap ∧ t.data = s.data ∧
      t.ptr 1 = s.ptr 0 ∧
      (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 5 → t.ptr i = s.ptr i) := by
  let s1 := tick (.loadPtr 2 2 0) s
  let s2 := tick (.null 5) s1
  let s3 := { s2 with pc := 9 }
  let t := tick (.movePtr 1 0) s3
  have exec : Executes reconnect s t 5 := by
    refine ⟨4, .head s s1 _ _ ?_ (.head s1 s2 _ _ ?_
      (.head s2 s3 _ _ ?_ (.single ?_))), ?_, rfl⟩
    all_goals simp [step, reconnect, tick, s1, s2, s3, t, pc, Instr.effect,
      Instr.next, read, parent, State.setPtr]
  refine ⟨t, exec, ?_, ?_, ?_, ?_⟩
  · simp [t, s3, s2, s1, tick, Instr.effect, read, parent, State.setPtr]
  · simp [t, s3, s2, s1, tick, Instr.effect, read, parent, State.setPtr]
  · simp [t, s3, s2, s1, tick, Instr.effect, read, parent, State.setPtr]
  · intro i h1 h2 h5
    simp [t, s3, s2, s1, tick, Instr.effect, read, parent, State.setPtr, h1, h2, h5]

/-- Reconnecting below a parent takes seven instructions. Exactly one parent child link
changes from the saved former root to the cursor; all other records and fields are preserved.
The caller supplies the parent's old child link, not the resulting heap. -/
theorem reconnect_child (s : State M (layout extra regs))
    (node par : Record M (layout extra regs)) (a : ℕ) (pc : s.pc = 0)
    (read : s.deref 0 = some node) (parent : node.ptr 2 = some a)
    (lookup : s.heap[a]? = some par)
    (attached : par.ptr 0 = s.ptr 6 ∨ par.ptr 1 = s.ptr 6) :
    ∃ t, ∃ field : Fin 3, Executes reconnect s t 7 ∧
      (field = 0 ∨ field = 1) ∧ par.ptr field = s.ptr 6 ∧
      t.heap = s.heap.modify a (fun r => { r with ptr := Function.update r.ptr field (s.ptr 0) }) ∧
      t.data = s.data ∧
      (∀ i, i ≠ 2 → i ≠ 3 → i ≠ 5 → t.ptr i = s.ptr i) := by
  change (s.ptr 0).bind (s.heap[·]?) = some node at read
  let field : Fin 3 := if par.ptr 0 = s.ptr 6 then 0 else 1
  let s1 := tick (.loadPtr 2 2 0) s
  let s2 := tick (.null 5) s1
  let s3 := { s2 with pc := 3 }
  let s4 := tick (.loadPtr 3 0 2) s3
  let s5 := { s4 with pc := if par.ptr 0 = s.ptr 6 then 7 else 5 }
  let t := tick (.storePtr field 2 0) s5
  have exec : Executes reconnect s t 7 := by
    refine ⟨6, .head s s1 _ _ ?_ (.head s1 s2 _ _ ?_
      (.head s2 s3 _ _ ?_ (.head s3 s4 _ _ ?_
        (.head s4 s5 _ _ ?_ (.single ?_))))), ?_, rfl⟩
    all_goals by_cases h : par.ptr 0 = s.ptr 6 <;>
      simp [step, reconnect, tick, s1, s2, s3, s4, s5, t, field, pc,
        Instr.effect, Instr.next, read, parent, State.setPtr, State.deref,
        lookup, State.modify, h]
  refine ⟨t, field, exec, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : par.ptr 0 = s.ptr 6 <;> simp [field, h]
  · dsimp [field]; split_ifs with h
    · exact h
    · exact attached.resolve_left h
  · simp [t, s5, s4, s3, s2, s1, tick, Instr.effect, State.setPtr,
      State.deref, State.modify, read, parent, lookup]
  · simp [t, s5, s4, s3, s2, s1, tick, Instr.effect, State.setPtr,
      State.deref, State.modify, read, parent, lookup]
  · intro i h2 h3 h5
    simp [t, s5, s4, s3, s2, s1, tick, Instr.effect, State.setPtr,
      State.deref, State.modify, read, parent, lookup, h2, h3, h5]

end Cslib.DataStructure.SearchTree.PointerMachine
