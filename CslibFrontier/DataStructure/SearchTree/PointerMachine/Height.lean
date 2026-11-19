/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Update

/-!
# Recomputing a linked tree's cached height

The nine-instruction program reads the two child caches, treats null children as height zero,
computes their maximum plus one, and writes the root cache. The scalar model supplies zero and
maximum-plus-one operations with explicit correctness contracts. This is the local height-update
step of AVL balancing, not an insertion or balancing algorithm.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Cached scalar height at a subtree root, with the supplied zero for an empty tree. -/
@[expose] def heightValue (zero : M.Value) (field : Fin (extra + 1)) :
    BinaryTree (Label M extra) → M.Value
  | .nil => zero
  | .node label _ _ => label.data field

/-- Six instructions read child caches into data registers one and two.
Pointer register two is scratch; a null child keeps the supplied scalar zero. -/
@[expose] def readHeightsPrefix (zero : M.Op) (field : Fin (extra + 1)) (base : Fin 7) :
    List (Instr M (layout extra (regs + 1))) :=
  [.op zero 1 1 1, .op zero 2 2 2, .loadPtr 2 0 base, .loadData 1 field 2,
   .loadPtr 2 1 base, .loadData 2 field 2]

/-- The cache-read prefix executes before any suffix, preserving the heap and client registers. -/
theorem readHeightsPrefix_runs (zero : M.Op) (z : M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = z)
    (field : Fin (extra + 1)) (base : Fin 7) (scratch : base ≠ 2)
    (suffix : List (Instr M (layout extra (regs + 1))))
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (cursor : s.ptr base = some label.address) (pc : s.pc = 0) :
    ∃ t, Runs (readHeightsPrefix zero field base ++ suffix) s t 6 ∧ t.pc = 6 ∧
      t.heap = s.heap ∧
      t.data 1 = heightValue z field l ∧ t.data 2 = heightValue z field r ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 2 → t.ptr i = s.ptr i) := by
  have ne : (1 : Fin (regs + 1 + 2)) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change 1 = 2 % (regs + 1 + 2) at hv
    rw [Nat.mod_eq_of_lt (show 2 < regs + 1 + 2 by omega)] at hv
    omega
  let s1 : State M (layout extra (regs + 1)) := { s.setData 1 z with pc := 1 }
  let s2 : State M (layout extra (regs + 1)) := { s1.setData 2 z with pc := 2 }
  let s3 : State M (layout extra (regs + 1)) := { s2.setPtr 2 (root l) with pc := 3 }
  let s4 : State M (layout extra (regs + 1)) :=
    { s3.setData 1 (heightValue z field l) with pc := 4 }
  let s5 : State M (layout extra (regs + 1)) := { s4.setPtr 2 (root r) with pc := 5 }
  let t : State M (layout extra (regs + 1)) :=
    { s5.setData 2 (heightValue z field r) with pc := 6 }
  have run : Runs (readHeightsPrefix zero field base ++ suffix) s t 6 := by
    refine .head s s1 _ _ ?_ (.head s1 s2 _ _ ?_ (.head s2 s3 _ _ ?_
      (.head s3 s4 _ _ ?_ (.head s4 s5 _ _ ?_ (.single ?_)))))
    · simp [step, readHeightsPrefix, pc, Instr.effect, Instr.next, s1, zero_spec]
    · simp [step, readHeightsPrefix, Instr.effect, Instr.next, s2, s1, zero_spec]
    · simp [step, readHeightsPrefix, Instr.effect, Instr.next, s3, s2, s1,
        State.setData, State.deref, cursor, rep.1, record]
    · rcases rep with ⟨_, hl, _⟩
      cases l with
      | nil => simp [step, readHeightsPrefix, Instr.effect, Instr.next, s4, s3, s2, s1,
          State.setPtr, State.setData, State.deref, root, heightValue, ne]
      | node a l r =>
        simp [step, readHeightsPrefix, Instr.effect, Instr.next, s4, s3, s2, s1,
          State.setPtr, State.setData, State.deref, root, hl.1, record, heightValue]
    · simp [step, readHeightsPrefix, Instr.effect, Instr.next, s5, s4, s3, s2, s1,
        State.setData, State.setPtr, State.deref, cursor, rep.1, record, scratch]
    · rcases rep with ⟨_, _, hr⟩
      cases r with
      | nil => simp [step, readHeightsPrefix, Instr.effect, Instr.next, t, s5, s4, s3, s2, s1,
          State.setPtr, State.setData, State.deref, root, heightValue, Ne.symm ne]
      | node a l r =>
        simp [step, readHeightsPrefix, Instr.effect, Instr.next, t, s5, s4, s3, s2, s1,
          State.setPtr, State.setData, State.deref, root, hr.1, record, heightValue]
  refine ⟨t, run, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [t, s5, s4, s3, s2, s1, State.setData, State.setPtr, ne]
  · simp [t, State.setData]
  · intro i h1 h2
    simp [t, s5, s4, s3, s2, s1, State.setData, State.setPtr, h1, h2]
  · intro i h2
    simp [t, s5, s4, s3, s2, s1, State.setData, State.setPtr, h2]


/-- Recompute the cursor's height. Data registers one/two and pointer register two are scratch.
Null-child loads preserve the initialized scalar zero. -/
@[expose] def recomputeHeight (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    List (Instr M (layout extra (regs + 1))) :=
  readHeightsPrefix zero field 0 ++ [.op maxSucc 1 1 2, .storeData field 0 1, .halt]

/-- Correct child caches give a correct root cache in nine instructions, including halt.
Only the root's selected scalar field, data temporaries one/two and pointer temporary two change.
The statement uses structural height; it does not assume that the root cache was already correct. -/
theorem recomputeHeight_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (x : State M (layout extra (regs + 1)))
    (label : Label M extra) (l r : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent (.node label l r))
    (left : heightValue (encode 0) field l = encode l.height)
    (right : heightValue (encode 0) field r = encode r.height)
    (cursor : x.ptr 0 = some label.address) (pc : x.pc = 0) :
    ∃ y, Executes (recomputeHeight zero maxSucc field) x y 9 ∧
      y.heap = x.heap.modify label.address
        (fun n =>
          { n with data := Function.update n.data field (encode (max l.height r.height + 1)) }) ∧
      Represents y.heap parent
        (updateData (.node label l r) label.address field
          (encode (BinaryTree.node label l r).height)) ∧
      (∀ i, i ≠ 1 → i ≠ 2 → y.data i = x.data i) ∧
      (∀ i, i ≠ 2 → y.ptr i = x.ptr i) := by
  obtain ⟨t, run, tpc, heap, dl, dr, data, ptr⟩ := readHeightsPrefix_runs zero (encode 0)
    zero_spec field 0 (by decide) [.op maxSucc 1 1 2, .storeData field 0 1, .halt]
    x label l r parent rep cursor pc
  have tc : t.ptr 0 = some label.address := (ptr 0 (by change (0 : Fin 7) ≠ 2; decide)).trans cursor
  let value := encode (max l.height r.height + 1)
  let s7 : State M (layout extra (regs + 1)) := { t.setData 1 value with pc := 7 }
  let y : State M (layout extra (regs + 1)) :=
    { s7 with pc := 8
              heap := x.heap.modify label.address
                (fun n => { n with data := Function.update n.data field value }) }
  have tail : Runs (recomputeHeight zero maxSucc field) t y 2 := by
    refine .head t s7 _ _ ?_ (.single ?_)
    · simp [step, recomputeHeight, readHeightsPrefix, tpc, Instr.effect, Instr.next,
        s7, dl, dr, left, right, max_spec, value]
    · simp [step, recomputeHeight, readHeightsPrefix, Instr.effect, Instr.next, y, s7,
        State.setData, State.modify, tc, heap]
  refine ⟨y, ⟨8, run.trans tail, rfl, rfl⟩, rfl, rep.updateData _ _ _, ?_, ?_⟩
  · intro i h1 h2
    simpa [y, s7, State.setData, h1] using data i h1 h2
  · intro i h2
    exact ptr i h2

end Cslib.DataStructure.SearchTree.PointerMachine
