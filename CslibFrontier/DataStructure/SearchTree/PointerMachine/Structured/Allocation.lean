/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers
import Mathlib.Tactic.FinCases

/-!
# Allocating and attaching tree nodes as structured pointer-machine programs

`Structured.allocate` and `Structured.insertLeaf` are the programs of `Allocation` and
`InsertLeaf` written as structured programs. `allocate` creates a leaf with its parent from
pointer register two and its scalar fields from supplied data registers. `insertLeaf` also fills
a vacant child link of that parent, or initializes root register one when the parent is null.

## Main definitions

* `allocate`, `attachLeaf`, `insertLeaf`: the programs.

## Main results

* `allocate_correct`: allocation takes `extra + 3` instructions, appends one record and
  preserves every register except cursor zero.
* `insertLeaf_correct`: allocating and attaching a leaf takes at most `extra + 7` instructions.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine
open Cslib.Program (ExecWithin.skip ExecWithin.seq ExecWithin.branch_pos ExecWithin.branch_neg)

variable {M : Model} {extra regs : ℕ}

/-- Copy each scalar field of the cursor from the specified data register. -/
@[expose] def storeFields (source : Fin (extra + 1) → Fin (regs + 2))
    (fields : List (Fin (extra + 1))) : Code M (layout extra regs) :=
  Program.Code.seqList (fields.map fun f => .op (.storeData f 0 (source f)))

open Register in
/-- Allocate a leaf in cursor register zero, initialize its parent from pointer register two,
and copy each scalar field from the specified data register. -/
@[expose] def allocate (source : Fin (extra + 1) → Fin (regs + 2)) :
    Code M (layout extra regs) := pm[
  cur ← new;
  cur[parent] ← par;
  ⟪storeFields source (List.finRange (extra + 1))⟫ ]

/-- Storing the fields `fields` of the cursor record takes one instruction each, and changes
only those fields. -/
private theorem storeFields_exec (source : Fin (extra + 1) → Fin (regs + 2))
    (fields : List (Fin (extra + 1))) (x : State M (layout extra regs)) (a : ℕ)
    (cursor : x.ptr 0 = some a) :
    ∃ y, ExecWithin (storeFields source fields) x y fields.length ∧ y.ptr = x.ptr ∧
      y.data = x.data ∧
      y.heap = x.heap.modify a fun n =>
        { n with data := fun f => if f ∈ fields then x.data (source f) else n.data f } := by
  induction fields generalizing x with
  | nil => exact ⟨x, ExecWithin.skip, rfl, rfl, (List.modify_id a x.heap).symm⟩
  | cons f fields ih =>
    obtain ⟨y, run, ptr, data, heap⟩ := ih ((Op.storeData f 0 (source f)).effect x)
      (by simpa [Op.effect, Op.instr, Instr.effect] using cursor)
    refine ⟨y, (ExecWithin.seq ExecWithin.op run).mono (by simp [Nat.add_comm]),
      by simpa [Op.effect, Op.instr, Instr.effect] using ptr,
      by simpa [Op.effect, Op.instr, Instr.effect] using data, ?_⟩
    rw [heap]
    simp only [Op.effect, Op.instr, Instr.effect, State.modify, cursor, List.modify_modify_eq]
    congr 1
    funext n
    simp only [Function.comp_apply, Record.mk.injEq, true_and]
    funext g
    by_cases hg : g = f <;> simp [hg]

/-- Allocation initializes all fields in `extra + 3` instructions. It appends exactly one
record and preserves every register except cursor zero. The new node is a represented leaf,
with the specified parent and complete scalar payload. -/
theorem allocate_correct (source : Fin (extra + 1) → Fin (regs + 2))
    (x : State M (layout extra regs)) :
    let label : Label M extra := ⟨x.heap.length, fun f => x.data (source f)⟩
    ∃ y, ExecWithin (allocate source) x y (extra + 3) ∧
      y.heap = x.heap ++ [record none none (x.ptr 2) label] ∧
      y.ptr = Function.update x.ptr 0 (some x.heap.length) ∧ y.data = x.data ∧
      Represents y.heap (x.ptr 2) (.node label .nil .nil) := by
  intro label
  let s := (Op.storePtr 2 0 2).effect ((Op.create (M := M) (L := layout extra regs) 0).effect x)
  obtain ⟨y, run, ptr, data, heap⟩ := storeFields_exec source (List.finRange (extra + 1)) s
    x.heap.length (by simp [s, Op.effect, Op.instr, Instr.effect])
  have result : y.heap = x.heap ++ [record none none (x.ptr 2) label] := by
    rw [heap]
    simp only [s, Op.effect, Op.instr, Instr.effect, State.modify, State.setPtr,
      Function.update_self, List.modify_modify_eq, List.mem_finRange, ↓reduceIte]
    rw [List.modify_eq_set_getElem?]
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, List.set_append_right _ _ (Nat.le_refl _), List.set_cons_zero,
      Option.map_eq_map, Option.map_some, Option.getD_some, Function.comp_apply]
    congr 2
    simp only [record, Record.blank, Record.mk.injEq]
    exact ⟨by funext f; fin_cases f <;> simp, rfl⟩
  refine ⟨y, (ExecWithin.seq ExecWithin.op (ExecWithin.seq ExecWithin.op run)).mono
    (by simp only [List.length_finRange]; omega), result,
    by simpa [s, Op.effect, Op.instr, Instr.effect, State.setPtr] using ptr,
    by simpa [s, Op.effect, Op.instr, Instr.effect, State.setPtr] using data, ?_⟩
  simp [result, Represents, root, label]

open Register in
/-- Attach the cursor at pointer field `field` of parent register two, or set root register one
if the parent is null. Register five is scratch. -/
@[expose] def attachAt (field : Fin 3) : Code M (layout extra regs) := pm[
  nul ← null;
  if par = nul then [ top ← cur ] else [ par[field] ← cur ] ]

/-- Attach the cursor to the selected child of parent register two, or set root register one if
the parent is null. Register five is scratch. -/
@[expose] def attachLeaf (side : Fin 2) : Code M (layout extra regs) := attachAt side.castSucc

/-- Allocate a leaf with the supplied scalar fields and attach it at the selected vacant link.
The null-parent case initializes root register one. -/
@[expose] def insertLeaf (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2) :
    Code M (layout extra regs) := pm[
  ⟪allocate source⟫;
  ⟪attachLeaf side⟫ ]

private theorem attach_correct (side : Fin 2) (x : State M (layout extra regs)) :
    ∃ y, ExecWithin (attachLeaf side) x y 4 ∧
      y.heap = (x.modify 2 (fun n =>
        { n with ptr := Function.update n.ptr side.castSucc (x.ptr 0) })).heap ∧
      y.ptr = Function.update (Function.update x.ptr 5 none) 1
        (if x.ptr 2 = none then x.ptr 0 else x.ptr 1) ∧ y.data = x.data := by
  cases hp : x.ptr 2 with
  | none =>
    refine ⟨_, (ExecWithin.seq ExecWithin.op (ExecWithin.branch_pos ?_ ExecWithin.op)).mono
      (by omega), ?_, ?_, ?_⟩
    all_goals simp [Test.Holds, Op.effect, Op.instr, Instr.effect, State.modify, hp]
  | some p =>
    refine ⟨_, (ExecWithin.seq ExecWithin.op (ExecWithin.branch_neg ?_ ExecWithin.op)).mono
      (by omega), ?_, ?_, ?_⟩
    all_goals simp [Test.Holds, Op.effect, Op.instr, Instr.effect, State.modify, hp]

/-- Filling a vacant child slot (or empty root) costs at most `extra + 7` instructions. The new
leaf has the complete supplied payload and parent link. The heap formula preserves every old
record except the selected parent's child link; all scalar registers and pointer registers other
than cursor, root and null scratch are unchanged. No ordering or balance is asserted. -/
theorem insertLeaf_correct (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2)
    (x : State M (layout extra regs))
    (vacant : match x.ptr 2 with
      | none => x.ptr 1 = none
      | some a => ∃ par, x.heap[a]? = some par ∧ par.ptr side.castSucc = none) :
    let label : Label M extra := ⟨x.heap.length, fun f => x.data (source f)⟩
    let heap := x.heap ++ [record none none (x.ptr 2) label]
    ∃ y, ExecWithin (insertLeaf source side) x y (extra + 7) ∧
      y.heap = (match x.ptr 2 with
        | none => heap
        | some a => heap.modify a
            (fun n =>
              { n with ptr := Function.update n.ptr side.castSucc (some x.heap.length) })) ∧
      Represents y.heap (x.ptr 2) (.node label .nil .nil) ∧
      y.heap.length = x.heap.length + 1 ∧
      y.ptr 0 = some x.heap.length ∧
      y.ptr 1 = (if x.ptr 2 = none then some x.heap.length else x.ptr 1) ∧
      y.data = x.data ∧ y.ptr 5 = none ∧
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 5 → y.ptr i = x.ptr i) ∧
      (∀ a par, x.ptr 2 = some a → x.heap[a]? = some par →
        y.heap[a]? = some
          { par with ptr := Function.update par.ptr side.castSucc (some x.heap.length) }) := by
  intro label heap0
  obtain ⟨a, alloc, ah, ap, ad, _⟩ := allocate_correct source x
  obtain ⟨y, attach, bh, bp, bd⟩ := attach_correct side a
  have heap : y.heap = match x.ptr 2 with
      | none => heap0
      | some p => heap0.modify p fun n =>
          { n with ptr := Function.update n.ptr side.castSucc (some x.heap.length) } := by
    cases hp : x.ptr 2 <;> simpa [heap0, label, State.modify, ap, ah, hp] using bh
  refine ⟨y, (ExecWithin.seq alloc attach).mono (by omega), heap, ?_, ?_,
    by simp [bp, ap], by simp [bp, ap], bd.trans ad, by simp [bp],
    fun i h0 h1 h5 => by simp [bp, ap, h0, h1, h5], ?_⟩
  · rw [heap]
    cases hp : x.ptr 2 with
    | none => simp [Represents, root, heap0, label, hp]
    | some p =>
      obtain ⟨par, get, _⟩ := hp ▸ vacant
      refine ⟨?_, trivial, trivial⟩
      rw [List.getElem?_modify_ne _ _ (ne_of_lt (List.getElem?_eq_some_iff.mp get).1)]
      simp [root, heap0, label, hp]
  · cases hp : x.ptr 2 <;> simp [heap, hp, heap0]
  · intro p par hp get
    simp [heap, heap0, hp, List.getElem?_append_left (List.getElem?_eq_some_iff.mp get).1, get]

/-! Frames of the allocation programs. The text of `storeFields` depends on the number of
fields, so its frames are proved by induction and those of the programs that call it follow by
`simp`. -/

@[simp] theorem storeFields_dataDests (source : Fin (extra + 1) → Fin (regs + 2))
    (fields : List (Fin (extra + 1))) :
    (storeFields (M := M) source fields).dataDests = [] := by
  induction fields <;> simp_all [storeFields, Program.Code.seqList, Op.dataDest]

@[simp] theorem storeFields_ptrDests (source : Fin (extra + 1) → Fin (regs + 2))
    (fields : List (Fin (extra + 1))) :
    (storeFields (M := M) source fields).ptrDests = [] := by
  induction fields <;> simp_all [storeFields, Program.Code.seqList, Op.ptrDest]

/-- Allocating and attaching a leaf assigns no data register. -/
@[simp] theorem insertLeaf_dataDests (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2) :
    (insertLeaf (M := M) source side).dataDests = [] := by
  simp [insertLeaf, allocate, attachLeaf, attachAt, Op.dataDest]

/-- Allocating and attaching a leaf assigns only pointer registers zero, one and five. -/
theorem insertLeaf_ptrDests (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2) :
    (insertLeaf (M := M) source side).ptrDests ⊆ [0, 1, 5] := by
  simp [insertLeaf, allocate, attachLeaf, attachAt, Op.ptrDest]

end Cslib.DataStructure.SearchTree.PointerMachine.Structured
