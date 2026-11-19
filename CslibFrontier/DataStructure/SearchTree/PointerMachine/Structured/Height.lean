/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Height
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers

/-!
# Cached heights as structured pointer-machine programs

`Structured.readHeights` and `Structured.recomputeHeight` are the programs of `Height` written
as structured programs: read the two child caches, treating null children as height zero, and
write their maximum plus one to the root cache.

## Main definitions

* `readHeights`: read the child caches into data registers one and two.
* `recomputeHeight`: recompute the cache of the cursor.

## Main results

* `readHeights_exec`: six instructions, preserving the heap and client registers.
* `recomputeHeight_correct`: correct child caches give a correct root cache in eight
  instructions.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine
open Cslib.Program (ExecWithin.seq)

variable {M : Model} {extra regs : ℕ}

open Register in
/-- Read the child caches of `base` into data registers one and two. Pointer register two is
scratch, so `base` must not be register two: the first load would overwrite it.
A null child keeps the supplied scalar zero. -/
@[expose] def readHeights (zero : M.Op) (field : Fin (extra + 1)) (base : Fin 7) :
    Code M (layout extra (regs + 1)) := pm[
  lh := zero lh lh;
  rh := zero rh rh;
  kid ← base[left];
  lh := kid[field];
  kid ← base[right];
  rh := kid[field] ]

/-- Loading the cache of a represented subtree through its root gives its cached height, and
keeps the register when the subtree is empty. -/
private theorem loadData_cache {x : State M (layout extra regs)} {t : BinaryTree (Label M extra)}
    {p : Pointer} (rep : Represents x.heap p t) {base : Fin 7} (hb : x.ptr base = root t)
    (s : Fin (regs + 2)) (field : Fin (extra + 1)) :
    (Op.loadData s field base).effect x = x.setData s (heightValue (x.data s) field t) := by
  cases t with
  | nil => simp [Op.effect, Op.instr, Instr.effect, State.deref, hb, root, heightValue,
      State.setData]
  | node a l r => simp [Op.effect, Op.instr, Instr.effect, State.deref, hb, root, rep.1,
      heightValue, record]

private theorem one_ne_two : (1 : Fin (regs + 1 + 2)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = 2 % (regs + 1 + 2) at hv
  rw [Nat.mod_eq_of_lt (show 2 < regs + 1 + 2 by omega)] at hv
  omega

/-- Reading the child caches takes six instructions and preserves the heap and client
registers. -/
theorem readHeights_exec (zero : M.Op) (z : M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = z)
    (field : Fin (extra + 1)) (base : Fin 7) (scratch : base ≠ 2)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (cursor : s.ptr base = some label.address) :
    ∃ t, ExecWithin (readHeights zero field base) s t 6 ∧ t.heap = s.heap ∧
      t.data 1 = heightValue z field l ∧ t.data 2 = heightValue z field r ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 2 → t.ptr i = s.ptr i) := by
  have ne := one_ne_two (regs := regs)
  obtain ⟨node, hl, hr⟩ := rep
  have deref : s.deref base = some (record (root l) (root r) parent label) := by
    simp [State.deref, cursor, node]
  have derefBase (x : State M (layout extra (regs + 1))) (p : Pointer) :
      (x.setPtr 2 p).deref base = x.deref base := State.deref_setPtr_of_ne x scratch p
  let s₂ := (s.setData 1 z).setData 2 z
  let s₃ := s₂.setPtr 2 (root l)
  let s₄ := s₃.setData 1 (heightValue z field l)
  let s₅ := s₄.setPtr 2 (root r)
  let t := s₅.setData 2 (heightValue z field r)
  have e₁ : (Op.op zero 1 1 1).effect s = s.setData 1 z := by
    simp [Op.effect, Op.instr, Instr.effect, zero_spec]
  have e₂ : (Op.op zero 2 2 2).effect (s.setData 1 z) = s₂ := by
    simp [Op.effect, Op.instr, Instr.effect, zero_spec, s₂]
  have e₃ : (Op.loadPtr 2 0 base).effect s₂ = s₃ := by
    simp [Op.effect, Op.instr, Instr.effect, deref, record, s₃, s₂]
  have e₄ : (Op.loadData 1 field 2).effect s₃ = s₄ :=
    (loadData_cache (x := s₃) (t := l) hl (base := 2) (by simp [s₃]) 1 field).trans
      (by simp [s₄, s₃, s₂, ne])
  have e₅ : (Op.loadPtr 2 1 base).effect s₄ = s₅ := by
    simp [Op.effect, Op.instr, Instr.effect, deref, record, s₅, s₄, s₃, s₂, derefBase]
  have e₆ : (Op.loadData 2 field 2).effect s₅ = t :=
    (loadData_cache (x := s₅) (t := r) hr (base := 2) (by simp [s₅]) 2 field).trans
      (by simp [t, s₅, s₄, s₃, s₂, Ne.symm ne])
  have run : ExecWithin (readHeights zero field base) s t 6 :=
    (ExecWithin.seq (ExecWithin.op_eq e₁) (ExecWithin.seq (ExecWithin.op_eq e₂)
      (ExecWithin.seq (ExecWithin.op_eq e₃) (ExecWithin.seq (ExecWithin.op_eq e₄)
        (ExecWithin.seq (ExecWithin.op_eq e₅) (ExecWithin.op_eq e₆)))))).mono (by omega)
  refine ⟨t, run, rfl, ?_, ?_, ?_, ?_⟩
  · simp [t, s₅, s₄, s₃, s₂, ne]
  · simp [t]
  · intro i h1 h2
    simp [t, s₅, s₄, s₃, s₂, h1, h2]
  · intro i h2
    simp [t, s₅, s₄, s₃, s₂, h2]

open Register in
/-- Recompute the cached height of the cursor. Data registers one and two and pointer register
two are scratch. -/
@[expose] def recomputeHeight (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    Code M (layout extra (regs + 1)) := pm[
  ⟪readHeights zero field cur⟫;
  lh := maxSucc lh rh;
  cur[field] := lh ]

/-- Correct child caches give a correct root cache in eight instructions. Only the root's
selected scalar field, data temporaries one and two and pointer temporary two change. The
statement uses structural height; it does not assume that the root cache was already correct. -/
theorem recomputeHeight_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (x : State M (layout extra (regs + 1)))
    (label : Label M extra) (l r : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent (.node label l r))
    (left : heightValue (encode 0) field l = encode l.height)
    (right : heightValue (encode 0) field r = encode r.height)
    (cursor : x.ptr 0 = some label.address) :
    ∃ y, ExecWithin (recomputeHeight zero maxSucc field) x y 8 ∧
      y.heap = x.heap.modify label.address
        (fun n =>
          { n with data := Function.update n.data field (encode (max l.height r.height + 1)) }) ∧
      Represents y.heap parent
        (updateData (.node label l r) label.address field
          (encode (BinaryTree.node label l r).height)) ∧
      (∀ i, i ≠ 1 → i ≠ 2 → y.data i = x.data i) ∧
      (∀ i, i ≠ 2 → y.ptr i = x.ptr i) := by
  obtain ⟨t, run, heap, dl, dr, data, ptr⟩ := readHeights_exec zero (encode 0) zero_spec field 0
    (by decide) x label l r parent rep cursor
  have tc : t.ptr 0 = some label.address := (ptr 0 (by change (0 : Fin 7) ≠ 2; decide)).trans cursor
  have result : ((Op.storeData field 0 1).effect ((Op.op maxSucc 1 1 2).effect t)).heap =
      x.heap.modify label.address (fun n =>
        { n with data := Function.update n.data field (encode (max l.height r.height + 1)) }) := by
    simp [Op.effect, Op.instr, Instr.effect, State.setData, State.modify, tc, heap, dl, dr, left,
      right, max_spec]
  refine ⟨_, ExecWithin.seq run (ExecWithin.seq ExecWithin.op ExecWithin.op), result, ?_, ?_, ?_⟩
  · rw [result]
    exact rep.updateData _ _ _
  · intro i h1 h2
    simpa [Op.effect, Op.instr, Instr.effect, State.setData, State.modify, tc, h1] using
      data i h1 h2
  · intro i h2
    simpa [Op.effect, Op.instr, Instr.effect, State.setData, State.modify, tc] using ptr i h2

end Cslib.DataStructure.SearchTree.PointerMachine.Structured
