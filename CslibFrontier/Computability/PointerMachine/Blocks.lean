/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Frame

/-!
# Composing pointer-machine instruction blocks

Relocation shifts internal branch targets and replaces halt by a jump to a continuation.
`Executes.inBlock` turns a proved halting run into a run of the same instruction count
inside a larger concrete program. The old halt is charged as the continuation jump.
Registers and heap are preserved exactly by this translation; only program counters change.
-/

public section
namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- Shift branch labels by `base` and turn halt into a jump to `next`.
Other instructions are unchanged. -/
@[expose] def Instr.relocate (base next : ℕ) : Instr M L → Instr M L
  | .goto label => .goto (base + label)
  | .ifPtrEq r s label => .ifPtrEq r s (base + label)
  | .ifTest test r s label => .ifTest test r s (base + label)
  | .halt => .goto next
  | i => i

/-- Relocating control flow does not change which scalar fields an instruction can write. -/
@[simp] theorem Instr.writesData_relocate (i : Instr M L) (base next : ℕ)
    (field : Fin L.dataFields) :
    (i.relocate base next).WritesData field ↔ i.WritesData field := by
  cases i <;> rfl

private def shift (base : ℕ) (x : State M L) : State M L :=
  { x with pc := base + x.pc }

private theorem fetch {code : List (Instr M L)} (pre post : List (Instr M L))
    (next : ℕ) {pc : ℕ} {i : Instr M L} (h : code[pc]? = some i) :
    (pre ++ code.map (Instr.relocate pre.length next) ++ post)[pre.length + pc]? =
      some (i.relocate pre.length next) := by
  have bound : pc < code.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa using bound),
    List.getElem?_map, h]
  rfl

private theorem relocated_step {code : List (Instr M L)}
    (pre post : List (Instr M L)) (next : ℕ) {x y : State M L}
    (h : step code x = some y) :
    step (pre ++ code.map (Instr.relocate pre.length next) ++ post)
      (shift pre.length x) = some (shift pre.length y) := by
  cases get : code[x.pc]? with
  | none => simp [step, get] at h
  | some i =>
    have hi := fetch pre post next get
    cases i <;> simp only [step, get] at h
    all_goals first
      | contradiction
      | (cases h
         simp only [step, shift, hi, Instr.relocate]
         simp only [Instr.effect, Instr.next,
           State.setPtr, State.setData, State.modify, State.deref, Option.elim, Nat.add_assoc])
    all_goals split <;> simp_all only

/-- A halting block runs inside any prefix and suffix, with the same instruction count.
Each former halt jumps to the absolute continuation label `next`. The resulting state
is the original result with only its program counter replaced by that label. -/
theorem Executes.inBlock {code : List (Instr M L)} {x y : State M L} {time : ℕ}
    (exec : Executes code x y time) (pre post : List (Instr M L)) (next : ℕ) :
    Runs (pre ++ code.map (Instr.relocate pre.length next) ++ post)
      { x with pc := pre.length + x.pc } { y with pc := next } time := by
  obtain ⟨n, run, halt, rfl⟩ := exec
  have mapped : Runs (pre ++ code.map (Instr.relocate pre.length next) ++ post)
      (shift pre.length x) (shift pre.length y) n :=
    run.map (shift pre.length) (fun _ _ h => relocated_step pre post next h)
  refine mapped.tail _ _ _ _ ?_
  have hi := fetch pre post next halt
  simp only [step, shift, hi, Instr.relocate, Instr.effect, Instr.next]


/-- Choose one halting block by a scalar test. Blocks retain their internal control flow;
their halts jump to the final halt of this program. -/
@[expose] def branch (test : M.Test) (r s : Fin L.dataRegs)
    (yes no : List (Instr M L)) : List (Instr M L) :=
  let join := 1 + no.length + yes.length
  [.ifTest test r s (1 + no.length)] ++
    no.map (Instr.relocate 1 join) ++
    yes.map (Instr.relocate (1 + no.length) join) ++ [.halt]

/-- Executing a conditional block costs the selected block's time plus two instructions:
the initial test and the final halt. The selected block's old halt is a charged jump. -/
theorem Executes.branch (test : M.Test) (r s : Fin L.dataRegs)
    (yes no : List (Instr M L)) {x y : State M L} {time : ℕ} (pc : x.pc = 0)
    (exec : Executes (if M.evalTest test (x.data r) (x.data s) then yes else no) x y time) :
    Executes (PointerMachine.branch test r s yes no) x
      { y with pc := 1 + no.length + yes.length } (time + 2) := by
  let join := 1 + no.length + yes.length
  have halt : (PointerMachine.branch test r s yes no)[join]? = some .halt := by
    change ([.ifTest test r s (1 + no.length)] ++ no.map (Instr.relocate 1 join) ++
      yes.map (Instr.relocate (1 + no.length) join) ++ [.halt])[join]? = _
    rw [List.getElem?_append_right (by simp [join, Nat.add_comm, Nat.add_left_comm])]
    simp [join, Nat.add_comm, Nat.add_left_comm]
  cases h : M.evalTest test (x.data r) (x.data s) with
  | false =>
    simp only [h, Bool.false_eq_true, ↓reduceIte] at exec
    have run := exec.inBlock [.ifTest test r s (1 + no.length)]
      (yes.map (Instr.relocate (1 + no.length) join) ++ [.halt]) join
    have run' : Runs (PointerMachine.branch test r s yes no) { x with pc := 1 }
        { y with pc := join } time := by
      simpa [PointerMachine.branch, join, pc, List.append_assoc, Nat.add_comm] using run
    refine ⟨time + 1, run'.head x _ _ _ ?_, halt, by omega⟩
    simp [step, PointerMachine.branch, pc, Instr.effect, Instr.next, h]
  | true =>
    simp only [h, ↓reduceIte] at exec
    have run := exec.inBlock
      ([.ifTest test r s (1 + no.length)] ++ no.map (Instr.relocate 1 join))
      [.halt] join
    have run' : Runs (PointerMachine.branch test r s yes no) { x with pc := 1 + no.length }
        { y with pc := join } time := by
      simpa [PointerMachine.branch, join, pc, List.append_assoc, Nat.add_comm] using run
    refine ⟨time + 1, run'.head x _ _ _ ?_, halt, by omega⟩
    simp [step, PointerMachine.branch, pc, Instr.effect, Instr.next, h]


/-- Run two halting blocks consecutively. The first halt jumps to the second block,
and the second halt jumps to the single final halt. -/
@[expose] def sequence (first second : List (Instr M L)) : List (Instr M L) :=
  first.map (Instr.relocate 0 first.length) ++
    second.map (Instr.relocate first.length (first.length + second.length)) ++ [.halt]

/-- Sequential block composition preserves the second result and charges the two
block costs plus one final halt. The second block enters at its own label zero;
the first keeps its original entry label. -/
theorem Executes.sequence {first second : List (Instr M L)} {x y z : State M L}
    {time₁ time₂ : ℕ} (h₁ : Executes first x y time₁)
    (h₂ : Executes second { y with pc := 0 } z time₂) :
    Executes (PointerMachine.sequence first second) x
      { z with pc := first.length + second.length } (time₁ + time₂ + 1) := by
  have one := h₁.inBlock []
    (second.map (Instr.relocate first.length (first.length + second.length)) ++ [.halt])
    first.length
  have two := h₂.inBlock (first.map (Instr.relocate 0 first.length)) [.halt]
    (first.length + second.length)
  have one' : Runs (PointerMachine.sequence first second) x
      { y with pc := first.length } time₁ := by
    simpa [PointerMachine.sequence, List.append_assoc] using one
  have two' : Runs (PointerMachine.sequence first second) { y with pc := first.length }
      { z with pc := first.length + second.length } time₂ := by
    simpa [PointerMachine.sequence] using two
  refine ⟨time₁ + time₂, one'.trans two', ?_, rfl⟩
  simp only [PointerMachine.sequence]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- Sequential composition introduces no scalar writes or allocation of its own. -/
@[simp] theorem sequence_no_data_writes (first second : List (Instr M L))
    (field : Fin L.dataFields) :
    (∀ i ∈ sequence first second, ¬ i.WritesData field) ↔
      (∀ i ∈ first, ¬ i.WritesData field) ∧ (∀ i ∈ second, ¬ i.WritesData field) := by
  simp only [sequence, List.forall_mem_append, List.forall_mem_map, Instr.writesData_relocate]
  simp [Instr.WritesData]

/-- Branch selection introduces no scalar writes or allocation of its own. -/
@[simp] theorem branch_no_data_writes (test : M.Test) (r s : Fin L.dataRegs)
    (yes no : List (Instr M L)) (field : Fin L.dataFields) :
    (∀ i ∈ branch test r s yes no, ¬ i.WritesData field) ↔
      (∀ i ∈ yes, ¬ i.WritesData field) ∧ (∀ i ∈ no, ¬ i.WritesData field) := by
  simp only [branch, List.forall_mem_append, List.forall_mem_map, Instr.writesData_relocate]
  simp [Instr.WritesData, and_comm]

end Cslib.PointerMachine
