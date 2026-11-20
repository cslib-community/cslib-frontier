/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Operations
public import CslibFrontier.Computability.PointerMachine.Program

/-! # Compilation from the standard word-RAM to a pointer machine

Each source instruction occupies a fixed-size block. Memory routines traverse an AVL dictionary;
scalar instructions and control flow take constant time. Padding is unreachable on successful
runs. Source `rand` instructions have no deterministic successor, and compile to a self-loop.
The final output is placed in scalar register three. The scalar model supplies the source word
width, while heap pointers remain opaque throughout execution.
-/

public section
namespace Cslib.WordRAM.PointerMachine
open Cslib.DataStructure
variable {w r : ℕ}

/-- Fixed block size, large enough for either dictionary routine and its register moves. -/
@[expose] def blockSize (w r : ℕ) : ℕ :=
  (AVLTree.PointerMachine.Dictionary.read (M := model w) (regs := r) (.constant 0) .lt).length +
  (AVLTree.PointerMachine.Dictionary.write (M := model w) (regs := r)
    (.constant 0) .maxSucc .lt .heavy .le).length + 12

/-- Lower one instruction, relocating local control flow to its fixed-size block. -/
@[expose] def body (k pc : ℕ) : Instr .standard r →
    List (Cslib.PointerMachine.Instr (model w) (layout r))
  | .op o => (operation o).map (Cslib.PointerMachine.Instr.relocate (k * pc) (k * (pc + 1)))
  | .jump dest => [.goto (k * dest)]
  | .branch (.eq a b) dest =>
      [.ifTest .eq (register a) (register b) (k * dest), .goto (k * (pc + 1))]
  | .branch (.lt a b) dest =>
      [.ifTest .lt (register a) (register b) (k * dest), .goto (k * (pc + 1))]
  | .halt i => [.moveData 3 (register i), .halt]
  | .rand _ _ => [.goto (k * pc)]

/-- Pad the lowered instruction to the fixed block size. -/
@[expose] def block (pc : ℕ) (i : Instr .standard r) :
    List (Cslib.PointerMachine.Instr (model w) (layout r)) :=
  let code := body (blockSize w r) pc i
  code ++ List.replicate (blockSize w r - code.length) (.goto (blockSize w r * pc))

/-- Compile a finite standard word-RAM program to an actual finite pointer-machine program. -/
@[expose] def compile (w : ℕ) (p : Program .standard r) :
    List (Cslib.PointerMachine.Instr (model w) (layout r)) :=
  Cslib.Program.compileBlocks block 0 p

private theorem body_length (pc : ℕ) (i : Instr .standard r) :
    (body (w := w) (blockSize w r) pc i).length ≤ blockSize w r := by
  cases i with
  | op o =>
    cases o with
    | load d a | store d a =>
      simp only [body, List.length_map, operation, Cslib.PointerMachine.sequence,
        List.length_append, List.length_cons, List.length_nil, List.length_map]
      unfold blockSize
      omega
    | const d n | copy d n => simp [body, operation, blockSize]
    | alu f d args => simp [body, operation, blockSize]
  | jump d | halt d | rand d s => simp [body, blockSize]
  | branch c d => cases c <;> simp [body, blockSize]

private theorem block_length (pc : ℕ) (i : Instr .standard r) :
    (block (w := w) pc i).length = blockSize w r := by
  have := body_length (w := w) pc i
  simp only [block, List.length_append, List.length_replicate]
  omega

private theorem fetch {p : Program .standard r} {pc n : ℕ} {i : Instr .standard r}
    {j : Cslib.PointerMachine.Instr (model w) (layout r)} (get : p[pc]? = some i)
    (localGet : (body (blockSize w r) pc i)[n]? = some j) :
    (compile w p)[blockSize w r * pc + n]? = some j := by
  apply Cslib.Program.getElem?_compileBlocks (block := block) (start := 0)
    (fun pc i _ => block_length pc i) get
  simp only [Nat.zero_add, block]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp localGet).1]
  exact localGet

private theorem branch_run (p : Program .standard r) (pc dest : ℕ) (test : Test)
    (a b : Fin r) (s : Cslib.PointerMachine.State (model w) (layout r))
    (entry : s.pc = blockSize w r * pc)
    (first : (compile w p)[blockSize w r * pc]? =
      some (.ifTest test (register a) (register b) (blockSize w r * dest)))
    (second : (compile w p)[blockSize w r * pc + 1]? =
      some (.goto (blockSize w r * (pc + 1)))) :
    ∃ time, Cslib.PointerMachine.Runs (compile w p) s
      { s with pc := if (model w).evalTest test (s.data (register a)) (s.data (register b))
        then blockSize w r * dest else blockSize w r * (pc + 1) } time ∧ time ≤ 2 := by
  cases h : (model w).evalTest test (s.data (register a)) (s.data (register b)) with
  | true =>
    simp only [model] at h
    refine ⟨1, .single ?_, by omega⟩
    simp [Cslib.PointerMachine.step, entry, first, Cslib.PointerMachine.Instr.effect,
      Cslib.PointerMachine.Instr.next, h]
  | false =>
    simp only [model] at h
    let t := { s with pc := blockSize w r * pc + 1 }
    refine ⟨2, .head s t _ _ ?_ (.single ?_), by omega⟩
    · simp [Cslib.PointerMachine.step, entry, first, Cslib.PointerMachine.Instr.effect,
        Cslib.PointerMachine.Instr.next, h, t]
    · simp [Cslib.PointerMachine.step, second, Cslib.PointerMachine.Instr.effect,
        Cslib.PointerMachine.Instr.next, t]

/-- Each successful source step is simulated by actual target instructions. The dictionary
retains all stored addresses, grows by at most one record, and charges logarithmic access time. -/
theorem step_compile (p : Program .standard r) (x y : State r)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x.data s tree avl) (pc : s.pc = blockSize w r * x.pc)
    (next : WordRAM.Next w p x y) :
    ∃ t tree' avl' time, Cslib.PointerMachine.Runs (compile w p) s t time ∧
      Represents y.data t tree' avl' ∧ t.pc = blockSize w r * y.pc ∧
      avl.elements.card ≤ avl'.elements.card ∧ avl'.elements.card ≤ avl.elements.card + 1 ∧
      time ≤ 294 * Nat.log 2 (avl.elements.card + 1) + 56 ∧
      t.heap.length ≤ s.heap.length + 1 := by
  cases get : p[x.pc]? with
  | none => simp [WordRAM.Next, WordRAM.step, get] at next
  | some i =>
    cases i with
    | op o =>
      cases evaluated : o.eval w x.data with
      | none => simp [WordRAM.Next, WordRAM.step, get, evaluated] at next
      | some data =>
        have eq : y = ⟨x.pc + 1, data⟩ := by
          simpa [WordRAM.Next, WordRAM.step, get, evaluated] using next.symm
        subst y
        obtain ⟨t, tree', avl', time, run, rt, mono, card, bound, space⟩ :=
          operation_correct o x.data data { s with pc := 0 } tree avl (rep.with_pc 0) rfl evaluated
        have embedded := run.inCompiledBlock (block := block) (start := 0)
          (next := blockSize w r * (x.pc + 1))
          (suffix := List.replicate (blockSize w r - (operation o).length)
            (.goto (blockSize w r * x.pc)))
          (fun pc i _ => block_length pc i) get
          (by simp only [Nat.zero_add, block, body, List.length_map]; rfl)
        refine ⟨{ t with pc := blockSize w r * (x.pc + 1) }, tree', avl', time,
          ?_, rt.with_pc _, rfl, mono, card, bound, space⟩
        simpa only [compile, Nat.add_zero, ← pc] using embedded
    | jump dest =>
      have eq : y = ⟨dest, x.data⟩ := by
        simpa [WordRAM.Next, WordRAM.step, get] using next.symm
      subst y
      have first := fetch get (show (body (blockSize w r) x.pc (.jump dest))[0]? =
        some (.goto (blockSize w r * dest)) from rfl)
      simp only [Nat.add_zero] at first
      refine ⟨{ s with pc := blockSize w r * dest }, tree, avl, 1,
        .single ?_, rep.with_pc _, rfl, le_rfl, by omega, by omega, by simp⟩
      simp [Cslib.PointerMachine.step, pc, first, Cslib.PointerMachine.Instr.effect,
        Cslib.PointerMachine.Instr.next]
    | branch c dest =>
      have eq : y = ⟨if c.Holds x.data then dest else x.pc + 1, x.data⟩ := by
        simpa [WordRAM.Next, WordRAM.step, get] using next.symm
      subst y
      cases c with
      | eq a b | lt a b =>
        have first := fetch get (show (body (blockSize w r) x.pc _)[0]? = _ from rfl)
        have second := fetch get (show (body (blockSize w r) x.pc _)[1]? =
          some (.goto (blockSize w r * (x.pc + 1))) from rfl)
        obtain ⟨time, run, bound⟩ := branch_run p x.pc dest _ a b s pc
          (by simpa only [Nat.add_zero] using first) second
        refine ⟨_, tree, avl, time, run, rep.with_pc _, ?_, le_rfl, by omega, by omega, by simp⟩
        simp only [model, rep.registers, Cond.Holds, decide_eq_true_eq]
        exact (apply_ite (fun n => blockSize w r * n) _ _ _).symm
    | halt i => simp [WordRAM.Next, WordRAM.step, get] at next
    | rand d a => simp [WordRAM.Next, WordRAM.step, get] at next

/-- A source halt copies its output to scalar register three and halts in two target steps.
The represented register bank and dictionary are preserved. -/
theorem halt_compile (p : Program .standard r) (x : State r) (v : ℕ)
    (s : Cslib.PointerMachine.State (model w) (layout r))
    (tree : BinaryTree (SearchTree.PointerMachine.Label (model w) 2)) (avl : AVLTree ℕ)
    (rep : Represents x.data s tree avl) (pc : s.pc = blockSize w r * x.pc)
    (halt : WordRAM.step w p x = .halt v) :
    ∃ t, Cslib.PointerMachine.Executes (compile w p) s t 2 ∧ t.data 3 = v ∧
      t.heap = s.heap ∧ Represents x.data t tree avl := by
  cases get : p[x.pc]? with
  | none => simp [WordRAM.step, get] at halt
  | some i =>
    cases i with
    | op o => cases evaluated : o.eval w x.data <;> simp [WordRAM.step, get, evaluated] at halt
    | jump d | branch c d | rand d a => simp [WordRAM.step, get] at halt
    | halt i =>
      have value : x.data.regs i = v := by simpa [WordRAM.step, get] using halt
      have first := fetch get (show (body (blockSize w r) x.pc (.halt i))[0]? =
        some (.moveData 3 (register i)) from rfl)
      simp only [Nat.add_zero] at first
      have last := fetch get (show (body (blockSize w r) x.pc (.halt i))[1]? =
        some .halt from rfl)
      let t := { s.setData 3 (s.data (register i)) with pc := blockSize w r * x.pc + 1 }
      refine ⟨t, ⟨1, .single ?_, last, rfl⟩, ?_, rfl, ?_⟩
      · simp [Cslib.PointerMachine.step, pc, first, Cslib.PointerMachine.Instr.effect,
          Cslib.PointerMachine.Instr.next, t]
      · simpa [t, Cslib.PointerMachine.State.setData, rep.registers] using value
      · refine ⟨?_, rep.heap, rep.matched, rep.valid, rep.distinct, rep.memory, rep.root⟩
        intro j
        have ne : register j ≠ 3 := register_ne_scratch j 3 (by decide)
        simp [t, Cslib.PointerMachine.State.setData, ne, rep.registers]

end Cslib.WordRAM.PointerMachine
