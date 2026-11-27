/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Representation

/-! # Concrete word-RAM operation routines

Memory operations call the verified linked AVL dictionary. Scalar operations use the source
arithmetic basis directly. Register zero carries an address as scalar data, never as a heap
pointer. Each routine halts locally, so the compiler can relocate it to a continuation.
-/

public section
namespace Cslib.WordRAM.PointerMachine
open Cslib.DataStructure
open Cslib.PointerMachine (sequence)
variable {w r : ℕ}

/-- A halting pointer-machine routine for each standard word-RAM data operation. -/
@[expose] def operation (o : Op .standard r) :
    List (Cslib.PointerMachine.Instr (model w) (layout r)) :=
  match o with
  | .load d a => sequence [.moveData 0 (register a), .halt]
      (sequence (AVLTree.PointerMachine.Dictionary.read (.constant 0) .lt)
        [.moveData (register d) 3, .halt])
  | .store a src => sequence [.moveData 0 (register a), .moveData 3 (register src), .halt]
      (AVLTree.PointerMachine.Dictionary.write (.constant 0) .maxSucc .lt .heavy .le)
  | _ => [(scalar o).getD .halt, .halt]

private theorem operation_scalar (o : Op .standard r)
    (i : Cslib.PointerMachine.Instr (model w) (layout r)) (h : scalar o = some i) :
    operation o = [i, .halt] := by
  cases o <;> simp_all [operation, scalar]

private theorem scalar_run (o : Op .standard r)
    (i : Cslib.PointerMachine.Instr (model w) (layout r))
    (lowered : scalar o = some i) (s : Cslib.PointerMachine.State (model w) (layout r))
    (pc : s.pc = 0) :
    Cslib.PointerMachine.Executes (operation o) s { i.effect s with pc := 1 } 2 := by
  rw [operation_scalar o i lowered]
  refine ⟨1, .single ?_, rfl, rfl⟩
  cases o with
  | load d a => cases lowered
  | store a src => cases lowered
  | const d n | copy d n =>
    cases Option.some.inj lowered
    simp [Cslib.PointerMachine.step, pc, Cslib.PointerMachine.Instr.next]
  | alu f d args =>
    cases f <;> cases Option.some.inj lowered <;>
      simp [Cslib.PointerMachine.step, pc, Cslib.PointerMachine.Instr.next]

private theorem scalar_rep (o : Op .standard r)
    (i : Cslib.PointerMachine.Instr (model w) (layout r)) (x y : Data r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x s tree avl) (lowered : scalar o = some i)
    (evaluated : o.eval w x = some y) :
    Represents y { i.effect s with pc := 1 } tree avl := by
  have h := scalar_correct o i x y s rep.registers lowered evaluated
  have mem : y.mem = x.mem := by
    cases o with
    | const d n => obtain ⟨_, rfl⟩ := Data.put_eq_some.mp evaluated; rfl
    | copy d src => cases Option.some.inj evaluated; rfl
    | alu f d args =>
      obtain ⟨v, _, _, rfl⟩ := Op.eval_alu_eq_some.mp evaluated
      rfl
    | load d a => cases lowered
    | store a src => cases lowered
  exact ⟨h.1, h.2.2.1 ▸ rep.heap, rep.matched, rep.valid, rep.distinct,
    mem ▸ rep.memory, congrFun h.2.2.2 1 |>.trans rep.root⟩

private theorem move_run (s : Cslib.PointerMachine.State (model w) (layout r))
    (d a : Fin (layout r).dataRegs) (pc : s.pc = 0) :
    Cslib.PointerMachine.Executes [.moveData d a, .halt] s
      { s.setData d (s.data a) with pc := 1 } 2 := by
  refine ⟨1, .single ?_, rfl, rfl⟩
  simp [Cslib.PointerMachine.step, pc, Cslib.PointerMachine.Instr.effect,
    Cslib.PointerMachine.Instr.next]

private theorem load_rep (d a : Fin r) (x : Data r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x s tree avl) (pc : s.pc = 0) :
    ∃ t time, Cslib.PointerMachine.Executes (operation (.load d a)) s t time ∧
      time ≤ 6 * avl.cachedHeight + 16 ∧
      Represents (x.set d (x.mem (x.regs a))) t tree avl ∧ t.heap.length ≤ s.heap.length + 1 := by
  let start := { s.setData 0 (s.data (register a)) with pc := 0 }
  obtain ⟨t, time, run, bound, heap, root, result, frame⟩ :=
    AVLTree.PointerMachine.Dictionary.read_correct (M := model w) (.constant 0) .lt id
      (fun _ _ => rfl) (fun _ _ => rfl) start tree avl x.mem rep.heap rep.matched
      rep.valid rep.memory rep.root rfl
  have done := move_run { t with pc := 0 } (register d) 3 rfl
  have all := (move_run s 0 (register a) pc).sequence (run.sequence done)
  refine ⟨_, _, all, by omega, ?_, ?_⟩
  swap
  · simpa only [heap, start, Cslib.PointerMachine.State.setData] using Nat.le_succ s.heap.length
  have value : t.data 3 = x.mem (x.regs a) := by
    simpa [start, Cslib.PointerMachine.State.setData, rep.registers] using result
  refine ⟨?_, heap ▸ rep.heap, rep.matched, rep.valid, rep.distinct, rep.memory,
    root.trans rep.root⟩
  intro j
  by_cases eq : j = d
  · subst j
    simpa [Cslib.PointerMachine.State.setData, Data.set] using value
  · have ne : register j ≠ register d := fun h => eq (register_injective h)
    have hj0 : register j ≠ 0 := register_ne_scratch j 0 (by decide)
    have hj1 : register j ≠ 1 := register_ne_scratch j 1 (by decide)
    have hj3 : register j ≠ 3 := register_ne_scratch j 3 (by decide)
    simp only [Cslib.PointerMachine.State.setData, Function.update_of_ne ne,
      Data.set, Function.update_of_ne eq]
    simpa [start, Cslib.PointerMachine.State.setData, hj0, rep.registers] using frame _ hj1 hj3

private theorem prepare_store (s : Cslib.PointerMachine.State (model w) (layout r))
    (a src : Fin r) (pc : s.pc = 0) :
    Cslib.PointerMachine.Executes
      [.moveData 0 (register a), .moveData 3 (register src), .halt] s
      { (s.setData 0 (s.data (register a))).setData 3 (s.data (register src)) with pc := 2 }
      3 := by
  have ne : register src ≠ 0 := register_ne_scratch src 0 (by decide)
  let t := { s.setData 0 (s.data (register a)) with pc := 1 }
  refine ⟨2, .head s t _ _ ?_ (.single ?_), rfl, rfl⟩
  · simp [Cslib.PointerMachine.step, pc, Cslib.PointerMachine.Instr.effect,
      Cslib.PointerMachine.Instr.next, t]
  · simp [Cslib.PointerMachine.step, Cslib.PointerMachine.Instr.effect,
      Cslib.PointerMachine.Instr.next, Cslib.PointerMachine.State.setData, t, ne]

private theorem store_rep (a src : Fin r) (x : Data r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x s tree avl) (pc : s.pc = 0) :
    ∃ t tree' time, Cslib.PointerMachine.Executes (operation (.store a src)) s t time ∧
      time ≤ 147 * avl.cachedHeight + 56 ∧
      Represents (x.write (x.regs a) (x.regs src)) t tree' (AVLTree.insert (x.regs a) avl) ∧
      t.heap.length ≤ s.heap.length + 1 := by
  let start := { (s.setData 0 (s.data (register a))).setData 3 (s.data (register src))
    with pc := 0 }
  have h03 : (0 : Fin (layout r).dataRegs) ≠ 3 := by
    intro h
    have eq := congrArg Fin.val h
    change 0 % (r + 2 + 2) = 3 % (r + 2 + 2) at eq
    rw [Nat.mod_eq_of_lt (show 3 < r + 2 + 2 by omega)] at eq
    simp at eq
  have query : start.data 0 = x.regs a := by
    simp [start, Cslib.PointerMachine.State.setData, rep.registers, h03]
  have payload : start.data 3 = x.regs src := by
    simp [start, Cslib.PointerMachine.State.setData, rep.registers]
  obtain ⟨t, tree', time, run, bound, result⟩ :=
    AVLTree.PointerMachine.Dictionary.write_correct (M := model w)
      (.constant 0) .maxSucc .lt .heavy .le id
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) start tree avl x.mem rep.heap rep.matched rep.valid rep.distinct
      rep.memory rep.root rfl
  have all := (prepare_store s a src pc).sequence run
  refine ⟨_, tree', _, all, by omega, ?_, result.space.2⟩
  refine ⟨?_, result.rep, ?_, AVLTree.valid_insert rep.valid _, result.distinct, ?_, result.root⟩
  · intro j
    have hj0 : register j ≠ 0 := register_ne_scratch j 0 (by decide)
    have hj1 : register j ≠ 1 := register_ne_scratch j 1 (by decide)
    have hj2 : register j ≠ 2 := register_ne_scratch j 2 (by decide)
    have hj3 : register j ≠ 3 := register_ne_scratch j 3 (by decide)
    simpa [start, Cslib.PointerMachine.State.setData, hj0, hj3, rep.registers, Data.write]
      using result.data _ hj1 hj2
  · simpa only [query] using result.matched
  · simpa only [query, payload, Data.write, id_eq] using result.stored

/-- Every successful source data operation has a concrete halting pointer-machine routine.
A write adds at most one stored address; every routine costs at most a fixed linear function
of the AVL height, hence logarithmic time in the number of stored addresses. -/
theorem operation_correct (o : Op .standard r) (x y : Data r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x s tree avl) (pc : s.pc = 0) (evaluated : o.eval w x = some y) :
    ∃ t tree' avl' time, Cslib.PointerMachine.Executes (operation o) s t time ∧
      Represents y t tree' avl' ∧ avl.elements.card ≤ avl'.elements.card ∧
      avl'.elements.card ≤ avl.elements.card + 1 ∧
      time ≤ 294 * Nat.log 2 (avl.elements.card + 1) + 56 ∧
      t.heap.length ≤ s.heap.length + 1 := by
  have height := rep.valid.cachedHeight_le_two_mul_log
  cases hs : scalar (w := w) o with
  | some i =>
    refine ⟨_, tree, avl, 2, scalar_run o i hs s pc,
      scalar_rep o i x y s tree avl rep hs evaluated, le_rfl, by omega, by omega, ?_⟩
    rw [(scalar_correct o i x y s rep.registers hs evaluated).2.2.1]
    omega
  | none =>
    cases o with
    | load d a =>
      cases Option.some.inj evaluated
      obtain ⟨t, time, run, bound, ht, space⟩ := load_rep d a x s tree avl rep pc
      exact ⟨t, tree, avl, time, run, ht, le_rfl, by omega, by omega, space⟩
    | store a src =>
      cases Option.some.inj evaluated
      obtain ⟨t, tree', time, run, bound, ht, space⟩ := store_rep a src x s tree avl rep pc
      refine ⟨t, tree', _, time, run, ht, ?_, ?_, by omega, space⟩
      · rw [AVLTree.elements_insert]
        exact Finset.card_le_card (Finset.subset_insert _ _)
      · rw [AVLTree.elements_insert]
        exact Finset.card_insert_le _ _
    | const d n => cases hs
    | copy d src => cases hs
    | alu f d args => cases f <;> cases hs

end Cslib.WordRAM.PointerMachine
