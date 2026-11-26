/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
import Mathlib.Tactic.FinCases

/-!
# Allocating linked tree nodes

`allocate` creates a leaf with its parent from pointer register two and its scalar fields
from supplied data registers. Its execution theorem charges allocation and every field store,
preserves the entire old heap and all registers except cursor zero, and identifies the new leaf.
Attaching the leaf to its parent and rebalancing are separate operations.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Allocate a leaf in cursor register zero, initialize its parent from pointer register two,
and copy each scalar field from the specified data register. -/
@[expose] def allocate (source : Fin (extra + 1) → Fin (regs + 2)) :
    List (Instr M (layout extra regs)) :=
  [.create 0, .storePtr 2 0 2] ++
    List.ofFn (fun f => .storeData f 0 (source f)) ++ [.halt]

private def partialRecord (x : State M (layout extra regs))
    (source : Fin (extra + 1) → Fin (regs + 2)) (k : ℕ) : Record M (layout extra regs) :=
  ⟨fun f => if f = 2 then x.ptr 2 else none,
   fun f => if f.val < k then x.data (source f) else M.undefined⟩

private def partialState (x : State M (layout extra regs))
    (source : Fin (extra + 1) → Fin (regs + 2)) (k : ℕ) : State M (layout extra regs) :=
  { x.setPtr 0 (some x.heap.length) with
    pc := k + 2
    heap := x.heap ++ [partialRecord x source k] }

private theorem fill_step (x : State M (layout extra regs))
    (source : Fin (extra + 1) → Fin (regs + 2)) (k : ℕ) (hk : k < extra + 1) :
    step (allocate source) (partialState x source k) =
      some (partialState x source (k + 1)) := by
  have upd : Function.update (partialRecord x source k).data ⟨k, hk⟩
      (x.data (source ⟨k, hk⟩)) = (partialRecord x source (k + 1)).data := by
    funext f
    rcases eq_or_ne f ⟨k, hk⟩ with rfl | h
    · simp [partialRecord]
    · rw [Function.update_of_ne h]
      have : f.val ≠ k := Fin.val_ne_of_ne h
      change (if f.val < k then _ else _) = if f.val < k + 1 then _ else _
      split_ifs <;> first | rfl | omega
  have fetch : (allocate (M := M) source)[k + 2]? =
      some (.storeData ⟨k, hk⟩ 0 (source ⟨k, hk⟩)) := by
    simp only [allocate, List.cons_append, List.nil_append,
      List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by simpa using hk)]
    simp only [List.getElem?_ofFn, hk, ↓reduceDIte]
  simp only [step, partialState, fetch, Instr.effect, Instr.next, State.setPtr, State.modify,
    Function.update_self, List.modify_eq_set_getElem?, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.map_eq_map, Option.map_some, Option.getD_some,
    List.set_append_right _ _ (Nat.le_refl _), List.set_cons_zero, upd]
  rfl

private theorem fill_run (x : State M (layout extra regs))
    (source : Fin (extra + 1) → Fin (regs + 2)) (k : ℕ) (hk : k ≤ extra + 1) :
    Runs (allocate source) (partialState x source 0) (partialState x source k) k := by
  induction k with
  | zero => exact .refl _
  | succ k ih => exact (ih (by omega)).tail _ _ _ _ (fill_step x source k (by omega))

/-- Allocation initializes all fields in exactly `extra + 4` instructions, including halt.
It appends exactly one record and preserves every register except cursor zero.
The new node is a represented leaf, with the specified parent and complete scalar payload. -/
theorem allocate_correct (source : Fin (extra + 1) → Fin (regs + 2))
    (x : State M (layout extra regs)) (pc : x.pc = 0) :
    let label : Label M extra := ⟨x.heap.length, fun f => x.data (source f)⟩
    ∃ y, Executes (allocate source) x y (extra + 4) ∧
      y.heap = x.heap ++ [record none none (x.ptr 2) label] ∧
      y.ptr = Function.update x.ptr 0 (some x.heap.length) ∧ y.data = x.data ∧
      Represents y.heap (x.ptr 2) (.node label .nil .nil) := by
  let created : State M (layout extra regs) := { (Instr.create 0).effect x with pc := 1 }
  have hupd : Function.update (fun _ : Fin 3 => (none : Pointer)) 2 (x.ptr 2) =
      fun f => if f = 2 then x.ptr 2 else none :=
    funext fun _ => by simp [Function.update_apply]
  have start : Runs (allocate source) x (partialState x source 0) 2 :=
    .head x created _ _ (by simp [step, allocate, pc, created, Instr.next])
      (.single (by simp [step, allocate, created, Instr.effect, Instr.next, partialState,
        partialRecord, State.setPtr, State.modify, Record.blank, List.modify_eq_set_getElem?,
        hupd]))
  have finish : partialRecord x source (extra + 1) =
      record none none (x.ptr 2) ⟨x.heap.length, fun f => x.data (source f)⟩ :=
    congrArg₂ _ (funext fun f => by fin_cases f <;> rfl)
      (funext fun f => by simp [f.isLt])
  have hrun : Runs (allocate source) x (partialState x source (extra + 1)) (extra + 3) := by
    convert start.trans (fill_run x source (extra + 1) le_rfl) using 1
    omega
  refine ⟨partialState x source (extra + 1), ⟨extra + 3, hrun, ?_, by omega⟩,
    by simp only [partialState, finish], rfl, rfl,
    by simp [Represents, partialState, finish, root]⟩
  simp only [partialState, allocate, List.cons_append, List.nil_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

end Cslib.DataStructure.SearchTree.PointerMachine
