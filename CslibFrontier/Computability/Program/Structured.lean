/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Structured programs over an instruction set

Flat programs are lists of instructions with numeric jump targets, which are inconvenient to
write and to reason about. A *structured program* (`Code`) is built from data instructions by
sequencing, conditionals and loops on tests. This file defines structured programs and their
cost-exact semantics once, for every machine: a machine supplies an `InstructionSet`, that is its
data, its data instructions and tests, and their meaning.

The big-step semantics `Exec` counts exactly the instructions of the flat program a structured
program assembles to (`Code.assemble` and `Exec.runs` in `Program.Assemble`). The costs assume a
machine whose test instruction jumps when the test holds:

* a conditional costs its test, plus a jump when the second alternative runs;
* `Code.loop t body` (while `t` holds) costs a test and a jump per test;
* `Code.loopUntil t body` (while `t` fails) costs a test and a jump per iteration and one test
  to leave.

`ExecWithin` bounds the count instead, and its rules compose like Hoare logic, with time bounds
added along sequences. `Code.eval` is a structurally recursive interpreter with a budget of loop
iterations, so `simp` and `decide` evaluate it, and `Exec.of_eval` turns its result into an
execution.

## Main definitions

* `InstructionSet`: data, data instructions and tests of a machine, with their meaning.
* `Code`, `Code.size`, `Code.seqList`: structured programs, the length of the flat program they
  assemble to, and the sequence of a list of programs.
* `Exec`, `ExecWithin`: executions with an exact instruction count, and within a bound.
* `Code.eval`: an interpreter with a budget of loop iterations.

## Main results

* `Exec.unique`: executions are deterministic.
* `Exec.invariant`, `Exec.invariant_ops`: a property that every data instruction, or every one
  occurring in the program, preserves is preserved by executions.
* `ExecWithin.loop_invariant`, `ExecWithin.loop_potential`, `ExecWithin.loopUntil_invariant`,
  `ExecWithin.loopUntil_potential`: loop rules.
* `Exec.of_eval`: the interpreter only finds executions.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the
  structured programs and their cost-exact semantics generalize `Cslib.WordRAM.Code`, which is
  adapted from its accompanying Lean formalization. `Code.skip` and `Code.loopUntil` are new.
-/

public section

namespace Cslib.Program

universe u v w

/-- The data of a machine, its data instructions and its tests, with their meaning. Control flow
is not part of an instruction set: structured programs (`Code`) supply it. -/
structure InstructionSet where
  /-- What a program transforms: registers and memory. -/
  Data : Type u
  /-- Data instructions. -/
  Op : Type v
  /-- Tests. -/
  Test : Type w
  /-- The data after a data instruction, or `none` if it faults. -/
  eval : Op → Data → Option Data
  /-- Whether a test holds of the data. -/
  Holds : Test → Data → Prop

/-- Structured programs over data instructions `Op` and tests `Test`. -/
inductive Code (Op : Type v) (Test : Type w) where
  /-- Do nothing; no instruction. -/
  | skip
  /-- A data instruction. -/
  | op (o : Op)
  /-- Run `c₁`, then `c₂`. -/
  | seq (c₁ c₂ : Code Op Test)
  /-- Run `pos` if `t` holds, and `neg` otherwise. -/
  | branch (t : Test) (pos neg : Code Op Test)
  /-- Run `body` while `t` holds. -/
  | loop (t : Test) (body : Code Op Test)
  /-- Run `body` until `t` holds. -/
  | loopUntil (t : Test) (body : Code Op Test)
  deriving DecidableEq

/-- The length of the flat program a structured program assembles to. -/
@[expose, simp] def Code.size {Op : Type v} {Test : Type w} : Code Op Test → ℕ
  | .skip => 0
  | .op _ => 1
  | .seq c₁ c₂ => c₁.size + c₂.size
  | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3
  | .loopUntil _ body => body.size + 2

/-- Run the programs of a list in order. -/
@[expose] def Code.seqList {Op : Type v} {Test : Type w} : List (Code Op Test) → Code Op Test
  | [] => .skip
  | c :: cs => .seq c (seqList cs)

/-- The data instructions that occur in a structured program. -/
@[expose, simp] def Code.ops {Op : Type v} {Test : Type w} : Code Op Test → List Op
  | .skip => []
  | .op o => [o]
  | .seq c₁ c₂ => c₁.ops ++ c₂.ops
  | .branch _ pos neg => pos.ops ++ neg.ops
  | .loop _ body => body.ops
  | .loopUntil _ body => body.ops

variable (I : InstructionSet.{u, v, w})

/-! ## Executions -/

/-- `Exec I c x y n`: the structured program `c` leads from data `x` to data `y` executing exactly
`n` instructions of the flat program it assembles to. -/
inductive Exec : Code I.Op I.Test → I.Data → I.Data → ℕ → Prop where
  /-- `skip` is no instruction. -/
  | skip {x : I.Data} : Exec .skip x x 0
  /-- A data instruction is one instruction. -/
  | op {o : I.Op} {x y : I.Data} : I.eval o x = some y → Exec (.op o) x y 1
  /-- Sequencing adds the instruction counts. -/
  | seq {c₁ c₂ : Code I.Op I.Test} {x y z : I.Data} {m n : ℕ} :
      Exec c₁ x y m → Exec c₂ y z n → Exec (.seq c₁ c₂) x z (m + n)
  /-- The first alternative of a conditional costs the test. -/
  | branch_pos {t : I.Test} {pos neg : Code I.Op I.Test} {x y : I.Data} {n : ℕ} :
      I.Holds t x → Exec pos x y n → Exec (.branch t pos neg) x y (n + 1)
  /-- The second alternative of a conditional costs the test and a jump. -/
  | branch_neg {t : I.Test} {pos neg : Code I.Op I.Test} {x y : I.Data} {n : ℕ} :
      ¬I.Holds t x → Exec neg x y n → Exec (.branch t pos neg) x y (n + 2)
  /-- Leaving a `loop` costs the test and a jump. -/
  | loop_exit {t : I.Test} {body : Code I.Op I.Test} {x : I.Data} :
      ¬I.Holds t x → Exec (.loop t body) x x 2
  /-- An iteration of a `loop` costs its body, the test and a jump back. -/
  | loop_iter {t : I.Test} {body : Code I.Op I.Test} {x y z : I.Data} {m n : ℕ} :
      I.Holds t x → Exec body x y m → Exec (.loop t body) y z n →
      Exec (.loop t body) x z (m + n + 2)
  /-- Leaving a `loopUntil` costs the test. -/
  | loopUntil_exit {t : I.Test} {body : Code I.Op I.Test} {x : I.Data} :
      I.Holds t x → Exec (.loopUntil t body) x x 1
  /-- An iteration of a `loopUntil` costs its body, the test and a jump back. -/
  | loopUntil_iter {t : I.Test} {body : Code I.Op I.Test} {x y z : I.Data} {m n : ℕ} :
      ¬I.Holds t x → Exec body x y m → Exec (.loopUntil t body) y z n →
      Exec (.loopUntil t body) x z (m + n + 2)

/-- `ExecWithin I c x y T`: the structured program `c` leads from `x` to `y` within `T`
instructions. -/
@[expose] def ExecWithin (c : Code I.Op I.Test) (x y : I.Data) (T : ℕ) : Prop :=
  ∃ n ≤ T, Exec I c x y n

variable {I}

namespace Exec

variable {c : Code I.Op I.Test} {x y y' : I.Data} {n n' : ℕ}

/-- Executions are deterministic. -/
theorem unique (h : Exec I c x y n) (h' : Exec I c x y' n') : y = y' ∧ n = n' := by
  induction h generalizing y' n' with
  | skip => cases h'; exact ⟨rfl, rfl⟩
  | op ho =>
    cases h' with
    | op ho' => exact ⟨Option.some.inj (ho.symm.trans ho'), rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁ h₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁
      obtain ⟨rfl, rfl⟩ := ih₂ h₂
      exact ⟨rfl, rfl⟩
  | branch_pos ht _ ih =>
    cases h' with
    | branch_pos _ h =>
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩
    | branch_neg hf _ => exact absurd ht hf
  | branch_neg hf _ ih =>
    cases h' with
    | branch_pos ht _ => exact absurd ht hf
    | branch_neg _ h =>
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩
  | loop_exit hf =>
    cases h' with
    | loop_exit => exact ⟨rfl, rfl⟩
    | loop_iter ht _ _ => exact absurd ht hf
  | loop_iter ht _ _ ihb ihl =>
    cases h' with
    | loop_exit hf => exact absurd ht hf
    | loop_iter _ hb hl =>
      obtain ⟨rfl, rfl⟩ := ihb hb
      obtain ⟨rfl, rfl⟩ := ihl hl
      exact ⟨rfl, rfl⟩
  | loopUntil_exit ht =>
    cases h' with
    | loopUntil_exit => exact ⟨rfl, rfl⟩
    | loopUntil_iter hf _ _ => exact absurd ht hf
  | loopUntil_iter hf _ _ ihb ihl =>
    cases h' with
    | loopUntil_exit ht => exact absurd ht hf
    | loopUntil_iter _ hb hl =>
      obtain ⟨rfl, rfl⟩ := ihb hb
      obtain ⟨rfl, rfl⟩ := ihl hl
      exact ⟨rfl, rfl⟩

/-- A property that every data instruction preserves is preserved by executions. -/
theorem invariant (P : I.Data → Prop) (hop : ∀ o x y, I.eval o x = some y → P x → P y)
    (h : Exec I c x y n) (hx : P x) : P y := by
  induction h with
  | skip | loop_exit | loopUntil_exit => exact hx
  | op ho => exact hop _ _ _ ho hx
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih hx
  | loop_iter _ _ _ ihb ihl | loopUntil_iter _ _ _ ihb ihl => exact ihl (ihb hx)

/-- A property that every data instruction occurring in the program preserves is preserved by
its executions. -/
theorem invariant_ops (P : I.Data → Prop) (h : Exec I c x y n)
    (hop : ∀ o ∈ c.ops, ∀ x y, I.eval o x = some y → P x → P y) (hx : P x) : P y := by
  induction h with
  | skip | loop_exit | loopUntil_exit => exact hx
  | op ho => exact hop _ (by simp) _ _ ho hx
  | seq _ _ ih₁ ih₂ =>
    exact ih₂ (fun o ho => hop o (by simp [ho])) (ih₁ (fun o ho => hop o (by simp [ho])) hx)
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih (fun o ho => hop o (by simp [ho])) hx
  | loop_iter _ _ _ ihb ihl | loopUntil_iter _ _ _ ihb ihl => exact ihl hop (ihb hop hx)

/-- An execution is within its instruction count. -/
theorem within (h : Exec I c x y n) : ExecWithin I c x y n := ⟨n, le_rfl, h⟩

end Exec

/-! ## Time bounds -/

namespace ExecWithin

variable {c c₁ c₂ pos neg body : Code I.Op I.Test} {t : I.Test} {x y z : I.Data} {T T₁ T₂ : ℕ}

/-- An execution whose instruction count is within the budget. -/
theorem of_exec {n : ℕ} (h : Exec I c x y n) (hn : n ≤ T) : ExecWithin I c x y T := ⟨n, hn, h⟩

/-- Monotonicity in the instruction budget. -/
theorem mono (h : ExecWithin I c x y T) (hT : T ≤ T₂) : ExecWithin I c x y T₂ :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn.trans hT, he⟩

/-- A property that every data instruction preserves is preserved by executions. -/
theorem invariant (P : I.Data → Prop) (hop : ∀ o x y, I.eval o x = some y → P x → P y)
    (h : ExecWithin I c x y T) (hx : P x) : P y :=
  let ⟨_, _, he⟩ := h
  he.invariant P hop hx

/-- `skip` executes within any bound. -/
theorem skip : ExecWithin I .skip x x T := ⟨0, Nat.zero_le _, .skip⟩

/-- A data instruction executes within one instruction. -/
theorem op {o : I.Op} (h : I.eval o x = some y) : ExecWithin I (.op o) x y 1 := (Exec.op h).within

/-- Sequencing adds the instruction bounds. -/
theorem seq (h₁ : ExecWithin I c₁ x y T₁) (h₂ : ExecWithin I c₂ y z T₂) :
    ExecWithin I (.seq c₁ c₂) x z (T₁ + T₂) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n, Nat.add_le_add hm hn, .seq he₁ he₂⟩

/-- The first alternative of a conditional adds one instruction to the bound. -/
theorem branch_pos (ht : I.Holds t x) (h : ExecWithin I pos x y T) :
    ExecWithin I (.branch t pos neg) x y (T + 1) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 1, Nat.add_le_add_right hn 1, .branch_pos ht he⟩

/-- The second alternative of a conditional adds two instructions to the bound. -/
theorem branch_neg (ht : ¬I.Holds t x) (h : ExecWithin I neg x y T) :
    ExecWithin I (.branch t pos neg) x y (T + 2) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 2, Nat.add_le_add_right hn 2, .branch_neg ht he⟩

/-- A conditional, with one bound for both alternatives. -/
theorem branch (hpos : I.Holds t x → ExecWithin I pos x y T)
    (hneg : ¬I.Holds t x → ExecWithin I neg x y T) :
    ExecWithin I (.branch t pos neg) x y (T + 2) := by
  by_cases ht : I.Holds t x
  · exact (branch_pos ht (hpos ht)).mono (by omega)
  · exact branch_neg ht (hneg ht)

/-- Leaving a `loop` takes two instructions. -/
theorem loop_exit (ht : ¬I.Holds t x) : ExecWithin I (.loop t body) x x 2 :=
  (Exec.loop_exit ht).within

/-- An iteration of a `loop` followed by the rest of it. -/
theorem loop_iter (ht : I.Holds t x) (h₁ : ExecWithin I body x y T₁)
    (h₂ : ExecWithin I (.loop t body) y z T₂) : ExecWithin I (.loop t body) x z (T₁ + T₂ + 2) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n + 2, by omega, .loop_iter ht he₁ he₂⟩

/-- Leaving a `loopUntil` takes one instruction. -/
theorem loopUntil_exit (ht : I.Holds t x) : ExecWithin I (.loopUntil t body) x x 1 :=
  (Exec.loopUntil_exit ht).within

/-- An iteration of a `loopUntil` followed by the rest of it. -/
theorem loopUntil_iter (ht : ¬I.Holds t x) (h₁ : ExecWithin I body x y T₁)
    (h₂ : ExecWithin I (.loopUntil t body) y z T₂) :
    ExecWithin I (.loopUntil t body) x z (T₁ + T₂ + 2) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n + 2, by omega, .loopUntil_iter ht he₁ he₂⟩

/-- **Loop rule, invariant and potential.** If the body leads every data `x` satisfying the
invariant `P` and the test to data `y` satisfying `P`, within `T` instructions with
`T + 2 + Φ y ≤ Φ x`, then from data satisfying `P` the loop ends within `Φ x + 2` instructions,
in data satisfying `P` where the test fails. The two extra instructions of an iteration are the
test and the jump back; the time of the body may differ between iterations, as long as the
potential `Φ` pays for it. -/
theorem loop_potential (P : I.Data → Prop) (Φ : I.Data → ℕ)
    (hbody : ∀ x, P x → I.Holds t x → ∃ y T, ExecWithin I body x y T ∧ P y ∧ T + 2 + Φ y ≤ Φ x)
    (hx : P x) : ∃ y, ExecWithin I (.loop t body) x y (Φ x + 2) ∧ P y ∧ ¬I.Holds t y := by
  induction x using (_root_.measure Φ).wf.induction with
  | h x ih =>
    by_cases ht : I.Holds t x
    · obtain ⟨y, T, hy, hPy, hΦ⟩ := hbody x hx ht
      obtain ⟨z, hz, hPz, htz⟩ := ih y (show Φ y < Φ x by omega) hPy
      exact ⟨z, (loop_iter ht hy hz).mono (by omega), hPz, htz⟩
    · exact ⟨x, (loop_exit ht).mono (by omega), hx, ht⟩

/-- A measure that decreases at each iteration of at most `T` instructions is a potential. -/
private theorem potential_of_measure {μ : I.Data → ℕ} {x y : I.Data} (T : ℕ) (hμ : μ y < μ x) :
    T + 2 + μ y * (T + 2) ≤ μ x * (T + 2) := by
  have := Nat.mul_le_mul_right (T + 2) (Nat.succ_le_of_lt hμ)
  rw [Nat.succ_mul] at this
  omega

/-- **Loop rule, invariant and measure.** If the body leads every data satisfying the invariant
`P` and the test, within `T` instructions, to data satisfying `P` with a smaller measure `μ`,
then from data satisfying `P` the loop ends within `μ x * (T + 2) + 2` instructions, in data
satisfying `P` where the test fails. -/
theorem loop_invariant (P : I.Data → Prop) (μ : I.Data → ℕ) {T : ℕ}
    (hbody : ∀ x, P x → I.Holds t x → ∃ y, ExecWithin I body x y T ∧ P y ∧ μ y < μ x)
    (hx : P x) :
    ∃ y, ExecWithin I (.loop t body) x y (μ x * (T + 2) + 2) ∧ P y ∧ ¬I.Holds t y :=
  loop_potential P (fun x => μ x * (T + 2))
    (fun x hx ht =>
      let ⟨y, hy, hPy, hμ⟩ := hbody x hx ht
      ⟨y, T, hy, hPy, potential_of_measure T hμ⟩) hx

/-- **Until rule, invariant and potential.** If the body leads every data `x` satisfying the
invariant `P` where the test fails to data `y` satisfying `P`, within `T` instructions with
`T + 2 + Φ y ≤ Φ x`, then from data satisfying `P` the loop ends within `Φ x + 1` instructions,
in data satisfying `P` and the test. -/
theorem loopUntil_potential (P : I.Data → Prop) (Φ : I.Data → ℕ)
    (hbody : ∀ x, P x → ¬I.Holds t x → ∃ y T, ExecWithin I body x y T ∧ P y ∧ T + 2 + Φ y ≤ Φ x)
    (hx : P x) : ∃ y, ExecWithin I (.loopUntil t body) x y (Φ x + 1) ∧ P y ∧ I.Holds t y := by
  induction x using (_root_.measure Φ).wf.induction with
  | h x ih =>
    by_cases ht : I.Holds t x
    · exact ⟨x, (loopUntil_exit ht).mono (by omega), hx, ht⟩
    · obtain ⟨y, T, hy, hPy, hΦ⟩ := hbody x hx ht
      obtain ⟨z, hz, hPz, htz⟩ := ih y (show Φ y < Φ x by omega) hPy
      exact ⟨z, (loopUntil_iter ht hy hz).mono (by omega), hPz, htz⟩

/-- **Until rule, invariant and measure.** If the body leads every data satisfying the invariant
`P` where the test fails, within `T` instructions, to data satisfying `P` with a smaller measure
`μ`, then from data satisfying `P` the loop ends within `μ x * (T + 2) + 1` instructions, in data
satisfying `P` and the test. -/
theorem loopUntil_invariant (P : I.Data → Prop) (μ : I.Data → ℕ) {T : ℕ}
    (hbody : ∀ x, P x → ¬I.Holds t x → ∃ y, ExecWithin I body x y T ∧ P y ∧ μ y < μ x)
    (hx : P x) :
    ∃ y, ExecWithin I (.loopUntil t body) x y (μ x * (T + 2) + 1) ∧ P y ∧ I.Holds t y :=
  loopUntil_potential P (fun x => μ x * (T + 2))
    (fun x hx ht =>
      let ⟨y, hy, hPy, hμ⟩ := hbody x hx ht
      ⟨y, T, hy, hPy, potential_of_measure T hμ⟩) hx

end ExecWithin

/-! ## Interpreter -/

section Eval

variable (I) [∀ t x, Decidable (I.Holds t x)]

/-- Run a loop that continues while `continues` and whose body is `body`, for at most `fuel`
iterations. Leaving it costs `exit` instructions. -/
@[expose] def Code.evalLoop (continues : I.Data → Bool) (exit : ℕ)
    (body : I.Data → Option (I.Data × ℕ)) : ℕ → I.Data → Option (I.Data × ℕ)
  | 0, x => if continues x then none else some (x, exit)
  | fuel + 1, x =>
    if continues x then
      (body x).bind fun y =>
        (evalLoop continues exit body fuel y.1).map fun z => (z.1, y.2 + z.2 + 2)
    else some (x, exit)

/-- Run a structured program, allowing each loop at most `fuel` iterations per entry:
`some (y, n)` if it leads to `y` executing `n` instructions, and `none` if it faults or runs out
of iterations. The definition is structurally recursive, so `simp` and `decide` evaluate it. -/
@[expose] def Code.eval (fuel : ℕ) : Code I.Op I.Test → I.Data → Option (I.Data × ℕ)
  | .skip, x => some (x, 0)
  | .op o, x => (I.eval o x).map fun y => (y, 1)
  | .seq c₁ c₂, x =>
    (c₁.eval fuel x).bind fun y => (c₂.eval fuel y.1).map fun z => (z.1, y.2 + z.2)
  | .branch t pos neg, x =>
    if I.Holds t x then (pos.eval fuel x).map fun y => (y.1, y.2 + 1)
    else (neg.eval fuel x).map fun y => (y.1, y.2 + 2)
  | .loop t body, x =>
    evalLoop I (fun y => decide (I.Holds t y)) 2 (fun y => body.eval fuel y) fuel x
  | .loopUntil t body, x =>
    evalLoop I (fun y => !decide (I.Holds t y)) 1 (fun y => body.eval fuel y) fuel x

variable {I}

private theorem Exec.of_evalLoop {t : I.Test} {body : Code I.Op I.Test}
    {f : I.Data → Option (I.Data × ℕ)}
    (hf : ∀ {x y : I.Data} {n : ℕ}, f x = some (y, n) → Exec I body x y n) {fuel : ℕ}
    {x y : I.Data} {n : ℕ}
    (h : Code.evalLoop I (fun y => decide (I.Holds t y)) 2 f fuel x = some (y, n)) :
    Exec I (.loop t body) x y n := by
  induction fuel generalizing x y n with
  | zero =>
    simp only [Code.evalLoop, decide_eq_true_eq] at h
    split at h
    · cases h
    · next ht => cases h; exact .loop_exit ht
  | succ fuel ih =>
    simp only [Code.evalLoop, decide_eq_true_eq] at h
    split at h
    · next ht =>
      obtain ⟨⟨x₁, m⟩, hb, hrest⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨x₂, k⟩, hl, he⟩ := Option.map_eq_some_iff.1 hrest
      cases he
      exact .loop_iter ht (hf hb) (ih hl)
    · next ht => cases h; exact .loop_exit ht

private theorem Exec.of_evalLoopUntil {t : I.Test} {body : Code I.Op I.Test}
    {f : I.Data → Option (I.Data × ℕ)}
    (hf : ∀ {x y : I.Data} {n : ℕ}, f x = some (y, n) → Exec I body x y n) {fuel : ℕ}
    {x y : I.Data} {n : ℕ}
    (h : Code.evalLoop I (fun y => !decide (I.Holds t y)) 1 f fuel x = some (y, n)) :
    Exec I (.loopUntil t body) x y n := by
  induction fuel generalizing x y n with
  | zero =>
    simp only [Code.evalLoop, Bool.not_eq_true', decide_eq_false_iff_not] at h
    split at h
    · cases h
    · next ht => cases h; exact .loopUntil_exit (not_not.mp ht)
  | succ fuel ih =>
    simp only [Code.evalLoop, Bool.not_eq_true', decide_eq_false_iff_not] at h
    split at h
    · next ht =>
      obtain ⟨⟨x₁, m⟩, hb, hrest⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨x₂, k⟩, hl, he⟩ := Option.map_eq_some_iff.1 hrest
      cases he
      exact .loopUntil_iter ht (hf hb) (ih hl)
    · next ht => cases h; exact .loopUntil_exit (not_not.mp ht)

/-- The interpreter only finds executions. -/
theorem Exec.of_eval {fuel : ℕ} {c : Code I.Op I.Test} {x y : I.Data} {n : ℕ}
    (h : c.eval I fuel x = some (y, n)) : Exec I c x y n := by
  induction c generalizing x y n with
  | skip => cases h; exact .skip
  | op o =>
    obtain ⟨y', hy, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    exact .op hy
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x₁, m⟩, h₁, hrest⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨x₂, k⟩, h₂, he⟩ := Option.map_eq_some_iff.1 hrest
    cases he
    exact .seq (ih₁ h₁) (ih₂ h₂)
  | branch t pos neg ihp ihn =>
    simp only [Code.eval] at h
    split at h
    · next ht =>
      obtain ⟨⟨x₁, m⟩, h₁, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact .branch_pos ht (ihp h₁)
    · next ht =>
      obtain ⟨⟨x₁, m⟩, h₁, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact .branch_neg ht (ihn h₁)
  | loop t body ih => exact Exec.of_evalLoop ih h
  | loopUntil t body ih => exact Exec.of_evalLoopUntil ih h

/-- An interpreter result within the budget is an execution within it. -/
theorem ExecWithin.of_eval {fuel : ℕ} {c : Code I.Op I.Test} {x y : I.Data} {n T : ℕ}
    (h : c.eval I fuel x = some (y, n)) (hn : n ≤ T) : ExecWithin I c x y T :=
  ⟨n, hn, .of_eval h⟩

end Eval

end Cslib.Program
