/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import CslibFrontier.Computability.Program.Assemble
public import CslibFrontier.Computability.WordRAM.Structured
public import CslibFrontier.Computability.WordRAM.Time

/-!
# Compiling structured word-RAM programs

A structured program (`Cslib.WordRAM.Code`) assembles into a flat program
(`Cslib.WordRAM.Code.assemble`) whose conditionals and loops become branches and jumps to
absolute instruction indices:

* `branch c pos neg` at `pc` becomes a branch on `c` to `pos`, then `neg`, then a jump past `pos`;
* `loop c body` at `pc` becomes a branch on `c` to `body`, a jump past the loop, `body`, and a
  jump back to the branch.

`Code.toGeneric` translates the syntax to `Cslib.Program.Code`. Ordinary operations and random
draws are primitive operations of the generic instruction set, with `rand` faulting in its
deterministic interpretation. The translation emits the same flat instructions at every label.

Every structured execution is a run of the assembled program with exactly the same number of
instructions (`Cslib.WordRAM.Exec.runs`). A complete program ends with a `halt`
(`Cslib.WordRAM.Code.program`), so a structured proof that a program answers a question
(`Cslib.WordRAM.Code.Answers`) gives a flat program that answers it with one more instruction
(`Cslib.WordRAM.Code.Answers.program`), and a uniform decision procedure
(`Cslib.WordRAM.Code.decidesInTime_program`, `Cslib.WordRAM.UniformDecidableInTime.of_code`).

## Main definitions

* `Cslib.WordRAM.Code.assemble`, `Cslib.WordRAM.Code.program`: assembly at a given position, and
  the complete program halting with a given register.
* `Cslib.WordRAM.Program.Contains`: a program contains another at a given position.
* `Cslib.WordRAM.Code.Answers`: a structured program answers a question in a register.

## Main results

* `Cslib.WordRAM.Exec.runs`: structured executions are runs of the assembled program with the
  same instruction count.
* `Cslib.WordRAM.Exec.executes`: a structured execution followed by `halt` is a halting run.
* `Cslib.WordRAM.Code.decidesInTime_program`, `Cslib.WordRAM.UniformDecidableInTime.of_code`:
  structured decision procedures are uniform deciders. Width-indexed code with a uniform size bound
  gives `Cslib.WordRAM.DecidableInTime.of_code`.
* `Cslib.WordRAM.Code.not_readsWidth_program`: a compiled program reads the word size only if the
  structured program does.
* `Cslib.WordRAM.Code.isRandFree_assemble`, `Cslib.WordRAM.Code.isRandFree_program`: assembly and
  program compilation preserve `IsRandFree`.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the assembly
  and its exact-cost correctness are adapted from its accompanying Lean formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-! ## Assembly -/

/-- Assemble a structured program to be placed at instruction index `pc`. -/
def Code.assemble : Code B r → ℕ → Program B r
  | .op o, _ => [.op o]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch c pos neg, pc =>
    .branch c (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      .jump (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop c body, pc =>
    .branch c (pc + 2) :: .jump (pc + body.size + 3) :: body.assemble (pc + 2) ++ [.jump pc]
  | .rand dst src, _ => [.rand dst src]

/-- Assembling a structured program `c` at any base index produces `c.size` instructions. -/
@[simp]
theorem Code.length_assemble (c : Code B r) (pc : ℕ) : (c.assemble pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [Code.assemble, List.length_append, List.length_cons, ihp, ihn, Code.size]
    omega
  | _ => simp_all [Code.assemble]

/-- The complete program: the assembled structured program followed by `halt out`. -/
def Code.program (c : Code B r) (out : Fin r) : Program B r := c.assemble 0 ++ [.halt out]

/-- Primitive WordRAM instructions in the shared syntax, including random draws. -/
abbrev GenericOp (B : Basis) (r : ℕ) := Op B r ⊕ (Fin r × Fin r)

/-- The generic deterministic instruction set at a fixed word width. A random draw faults
in deterministic execution. -/
abbrev instructionSet (w : ℕ) (B : Basis) (r : ℕ) : Cslib.Program.InstructionSet where
  Data := Data r
  Op := GenericOp B r
  Test := Cond r
  eval
    | .inl op, x => op.eval w x
    | .inr _, _ => none
  Holds := Cond.Holds

/-- WordRAM instructions and deterministic step laws for generic assembly. -/
abbrev flatMachine (w : ℕ) (B : Basis) (r : ℕ) :
    Cslib.Program.FlatMachine (instructionSet w B r) where
  Instr := Instr B r
  op
    | .inl op => .op op
    | .inr (dst, src) => .rand dst src
  goto := .jump
  jumpIf := .branch
  Step p s t := Next w p ⟨s.1, s.2⟩ ⟨t.1, t.2⟩
  step_op := by
    intro p pc op x y hp h
    cases op with
    | inl op => exact step_op (s := ⟨pc, x⟩) hp h
    | inr regs => cases h
  step_goto hp := step_jump hp
  step_jumpIf_pos := by
    intro p pc target cond x hp h
    change cond.Holds x at h
    simpa only [Next, h, ↓reduceIte] using step_branch (w := w) (s := ⟨pc, x⟩) hp
  step_jumpIf_neg := by
    intro p pc target cond x hp h
    change ¬cond.Holds x at h
    simpa only [Next, h, ↓reduceIte] using step_branch (w := w) (s := ⟨pc, x⟩) hp

/-- Translate structured WordRAM syntax, including random draws, for generic assembly. -/
def Code.toGeneric : Code B r → Cslib.Program.Code (GenericOp B r) (Cond r)
  | .op o => .op (.inl o)
  | .rand dst src => .op (.inr (dst, src))
  | .seq c₁ c₂ => .seq c₁.toGeneric c₂.toGeneric
  | .branch test pos neg => .branch test pos.toGeneric neg.toGeneric
  | .loop test body => .loop test body.toGeneric

/-- The generic translation preserves compiled code length. -/
@[simp] theorem Code.size_toGeneric (c : Code B r) : c.toGeneric.size = c.size := by
  induction c <;> simp_all [Code.toGeneric, Code.size]

/-- The generic assembler emits exactly the existing WordRAM instructions. -/
@[simp] theorem Code.assemble_toGeneric {w : ℕ} (c : Code B r) (pc : ℕ) :
    c.toGeneric.assemble (flatMachine w B r) pc = c.assemble pc := by
  induction c generalizing pc <;>
    simp_all [Code.toGeneric, Code.assemble, Cslib.Program.Code.assemble, flatMachine]

/-- `p` contains the program `q` starting at instruction index `base`. -/
def Program.Contains (p : Program B r) (base : ℕ) (q : Program B r) : Prop :=
  Cslib.Program.Contains p base q

namespace Program.Contains

variable {p q q₁ q₂ : Program B r} {base : ℕ}

/-- Every program contains itself starting at instruction index `0`. -/
theorem self (p : Program B r) : p.Contains 0 p := ⟨[], [], by simp, rfl⟩

/-- If `p` contains `q₁ ++ q₂` at `base`, then `p` contains `q₁` at `base`. -/
theorem append_left (h : p.Contains base (q₁ ++ q₂)) : p.Contains base q₁ :=
  Cslib.Program.Contains.append_left h

/-- If `p` contains `q₁ ++ q₂` at `base`, then `p` contains `q₂` at `base + q₁.length`. -/
theorem append_right (h : p.Contains base (q₁ ++ q₂)) : p.Contains (base + q₁.length) q₂ :=
  Cslib.Program.Contains.append_right h

/-- If `p` contains `i :: q` at `base`, then `p` contains `q` at `base + 1`. -/
theorem cons_tail {i : Instr B r} (h : p.Contains base (i :: q)) : p.Contains (base + 1) q :=
  Cslib.Program.Contains.cons_tail h

/-- Indexing into `p` at `base + k` for `k < q.length` agrees with indexing into `q` at `k`. -/
theorem getElem? (h : p.Contains base q) {k : ℕ} (hk : k < q.length) :
    p[base + k]? = q[k]? := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

/-- If `p` contains `i :: q` at `base`, then instruction `base` of `p` is `i`. -/
theorem head {i : Instr B r} (h : p.Contains base (i :: q)) : p[base]? = some i :=
  Cslib.Program.Contains.head h

end Program.Contains

/-! ## Correctness of assembly -/

section Runs

variable {w : ℕ} {p : Program B r} {x : Data r} {pc : ℕ}

private theorem Exec.toGeneric {c : Code B r} {y : Data r} {n : ℕ}
    (h : Exec w c x y n) :
    Cslib.Program.Exec (instructionSet w B r) c.toGeneric x y n := by
  induction h with
  | op h => exact .op h
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos h _ ih => exact .branch_pos h ih
  | branch_neg h _ ih => exact .branch_neg h ih
  | loop_exit h => exact .loop_exit h
  | loop_iter h _ _ ihb ihl => exact .loop_iter h ihb ihl

/-- **Assembly is correct.** A structured execution is a run of any program containing the
assembled structured program, from its first instruction to the instruction after it, with
exactly the same number of instructions. -/
theorem Exec.runs {c : Code B r} {y : Data r} {n : ℕ} (h : Exec w c x y n)
    (hp : p.Contains pc (c.assemble pc)) : Runs w p ⟨pc, x⟩ ⟨pc + c.size, y⟩ n := by
  obtain ⟨pre, post, rfl, rfl⟩ := hp
  have run := h.toGeneric.runs (flatMachine w B r) pre post
  rw [Code.assemble_toGeneric, Code.size_toGeneric] at run
  exact run.map (r' := Next w (pre ++ c.assemble pre.length ++ post))
    (fun s : ℕ × Data r => (⟨s.1, s.2⟩ : State r)) (fun _ _ hstep => hstep)

/-- A structured execution followed by `halt out` is a halting run of the complete program, with
one more instruction. -/
theorem Exec.executes {c : Code B r} {y : Data r} {n : ℕ} (h : Exec w c x y n) (out : Fin r) :
    Executes w (c.program out) ⟨0, x⟩ (y.regs out) (n + 1) := by
  have hr := h.runs (pc := 0) (p := c.program out) (Program.Contains.self _).append_left
  have hh : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
    step_halt (by simp [Code.program])
  exact Executes.of_runs hr (Executes.halt hh)

end Runs

/-! ## Answering questions with structured programs -/

/-- The structured program `c`, run at word size `w` from the initial data on `input`, leaves
the answer to `b` in register `out` within `time` instructions: `1` if `b` holds and `0`
otherwise. -/
def Code.Answers (c : Code B r) (out : Fin r) (w : ℕ) (input : List ℕ) (b : Prop) (time : ℕ) :
    Prop :=
  ∃ y, ExecWithin w c (.init input) y time ∧ y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ b)

/-- A structured program that answers a question gives a flat program that answers it, with one
more instruction for the final `halt`. -/
theorem Code.Answers.program {c : Code B r} {out : Fin r} {w : ℕ} {input : List ℕ} {b : Prop}
    {time : ℕ} (h : c.Answers out w input b time) : (c.program out).Answers w input b (time + 1) :=
  let ⟨y, ⟨n, hn, he⟩, hv⟩ := h
  ⟨y.regs out, n + 1, he.executes out, Nat.add_le_add_right hn 1, hv⟩

/-- Structured answers give a fixed-program decision certificate, charging the final halt. -/
theorem Code.decidesInTime_program {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      c.Answers out w (encode w a) (a ∈ A) (time a w)) :
    (c.program out).DecidesInTime encode A (fun a w => time a w + 1) allowed :=
  fun a w hw hi => (h a w hw hi).program

/-- Structured decision procedures are uniform deciders. -/
theorem UniformDecidableInTime.of_code {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : Code B r) (out : Fin r)
    (hadmit : InputAdmissible encode allowed)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      c.Answers out w (encode w a) (a ∈ A) (time a w)) :
    UniformDecidableInTime B A encode (fun a w => time a w + 1) allowed :=
  ⟨r, c.program out, c.decidesInTime_program out h, hadmit⟩

/-- Structured families with bounded compiled code give nonuniform deciders. -/
theorem DecidableInTime.of_code {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : ℕ → Code B r) (out : Fin r)
    (hc : ∃ L, ∀ w, (c w).size ≤ L)
    (hadmit : InputAdmissible encode allowed)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      (c w).Answers out w (encode w a) (a ∈ A) (time a w)) :
    DecidableInTime B A encode (fun a w => time a w + 1) allowed :=
  let ⟨L, hL⟩ := hc
  ⟨r, (fun w => (c w).program out), ⟨L + 1, fun w => by
    simpa only [Code.program, List.length_append, Code.length_assemble,
      List.length_cons, List.length_nil] using Nat.add_le_add_right (hL w) 1⟩,
    (fun a w hw hi => (h a w hw hi).program), hadmit⟩

/-! ## Reading the word size -/

/-- An assembled program reads the word size only if the structured program does. -/
private theorem Code.readsWidth_of_assemble {c : Code B r} {pc : ℕ}
    (h : (c.assemble pc).ReadsWidth) : c.ReadsWidth := by
  obtain ⟨i, hi, hr⟩ := h
  induction c generalizing pc with
  | op o =>
    simp only [Code.assemble, List.mem_singleton] at hi
    subst hi
    exact hr
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Code.assemble, List.mem_append] at hi
    exact hi.elim (fun hi => .inl (ih₁ hi)) (fun hi => .inr (ih₂ hi))
  | branch c pos neg ihp ihn =>
    simp only [Code.assemble, List.mem_append, List.mem_cons] at hi
    rcases hi with (rfl | hi) | rfl | hi
    · exact (hr : False).elim
    · exact .inr (ihn hi)
    · exact (hr : False).elim
    · exact .inl (ihp hi)
  | loop c body ih =>
    simp only [Code.assemble, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | hi) | rfl
    · exact (hr : False).elim
    · exact (hr : False).elim
    · exact ih hi
    · exact (hr : False).elim
  | rand _ _ =>
    simp only [Code.assemble, List.mem_singleton] at hi
    subst hi
    exact hr

/-- A compiled program reads the word size only if the structured program does. -/
theorem Code.not_readsWidth_program {c : Code B r} (hc : ¬c.ReadsWidth) (out : Fin r) :
    ¬(c.program out).ReadsWidth := by
  rintro ⟨i, hi, hr⟩
  rcases List.mem_append.1 hi with hi | hi
  · exact hc (Code.readsWidth_of_assemble ⟨i, hi, hr⟩)
  · rw [List.mem_singleton] at hi
    subst hi
    exact (hr : False).elim

/-! ## `rand`-freeness -/

@[simp]
private theorem isRandFree_nil : Program.IsRandFree ([] : Program B r) := by
  intro _ h
  cases h

@[simp]
private theorem isRandFree_cons {i : Instr B r} {p : Program B r} :
    Program.IsRandFree (i :: p) ↔ i.IsRandFree ∧ p.IsRandFree := by
  simp only [Program.IsRandFree, List.mem_cons, forall_eq_or_imp]

@[simp]
private theorem isRandFree_append {p₁ p₂ : Program B r} :
    Program.IsRandFree (p₁ ++ p₂) ↔ p₁.IsRandFree ∧ p₂.IsRandFree := by
  simp only [Program.IsRandFree, List.mem_append, or_imp, forall_and]

/-- Assembling a structured program produces a `rand`-free flat program if and only if the
structured program is `rand`-free. -/
@[simp]
theorem Code.isRandFree_assemble {c : Code B r} {pc : ℕ} :
    (c.assemble pc).IsRandFree ↔ c.IsRandFree := by
  induction c generalizing pc with
  | op o => simp [Code.assemble, Instr.IsRandFree, Code.IsRandFree]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [Code.assemble, ih₁, ih₂, Code.IsRandFree]
  | branch c pos neg ihp ihn =>
    simp only [Code.assemble, isRandFree_cons, isRandFree_append, Instr.IsRandFree, true_and,
      ihn, ihp, Code.IsRandFree]
    exact and_comm
  | loop c body ih =>
    simp [Code.assemble, Instr.IsRandFree, Code.IsRandFree, ih]
  | rand dst src =>
    simp [Code.assemble, Instr.IsRandFree, Code.IsRandFree]

/-- A compiled complete program is `rand`-free if and only if the structured program is
`rand`-free. -/
@[simp]
theorem Code.isRandFree_program {c : Code B r} {out : Fin r} :
    (c.program out).IsRandFree ↔ c.IsRandFree := by
  simp [Code.program, Instr.IsRandFree]

end Cslib.WordRAM

end
