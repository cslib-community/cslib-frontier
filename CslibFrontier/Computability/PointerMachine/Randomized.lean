/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.Computability.Program.Randomized

/-!
# Randomized pointer-machine programs

Scalar instructions can sample from a supplied kernel. Each step uses the program counter
in the machine state. Halt and out-of-range labels are absorbing.

## Main definitions

* `Op.evalRand`: the randomized interpretation of structured data operations.
* `stepRand`, `runRand`: step and bounded execution of flat randomized programs.

## Main results

* `runRand_program`: the output distribution of an assembled structured execution.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- Interpret scalar operations with a probabilistic kernel and retain all other effects. -/
@[expose] def Op.evalRand (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (o : Op M L) (x : State M L) : Option (ProbComp (State M L)) :=
  some (match o with
    | .op primitive dst a b => x.setData dst <$> kernel primitive (x.data a) (x.data b)
    | _ => pure (o.effect x))

/-- Take one randomized step, leaving terminal states unchanged. -/
@[expose] def stepRand (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (program : List (Instr M L)) (x : State M L) : ProbComp (State M L) :=
  match program[x.pc]? with
  | some (.op op dst a b) =>
    (fun v => { x.setData dst v with pc := x.pc + 1 }) <$> kernel op (x.data a) (x.data b)
  | _ => pure ((step program x).getD x)

/-- Run a flat pointer-machine program for a fixed instruction budget. -/
@[expose] def runRand (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (program : List (Instr M L)) : ℕ → State M L → ProbComp (State M L)
  | 0, x => pure x
  | n + 1, x => stepRand kernel program x >>= runRand kernel program n

private abbrev randomizedFlatMachine (kernel : M.Op → M.Value → M.Value → ProbComp M.Value) :
    Program.RandomizedFlatMachine (Op.evalRand kernel) (flatMachine M L) where
  Config := State M L
  running pc x := { x with pc := pc }
  step := stepRand kernel
  step_op := by
    intro program pc o x m hp he
    change program[pc]? = some o.instr at hp
    have hs := step_op (x := x) hp
    cases o <;> simp only [Op.evalRand, Option.some.injEq] at he <;> subst m <;>
      simp [stepRand, Op.instr, hp, hs, State.setData, Functor.map_map]
  step_goto := by
    intro program pc label x hp
    change program[pc]? = some (.goto label) at hp
    simp [stepRand, hp, step_goto (x := x) hp]
  step_jumpIf_pos := by
    intro program pc label t x hp ht
    change program[pc]? = some (t.instr label) at hp
    have hs := step_test_pos hp ht
    cases t <;> simp [stepRand, Test.instr, hp, hs]
  step_jumpIf_neg := by
    intro program pc label t x hp ht
    change program[pc]? = some (t.instr label) at hp
    have hs := step_test_neg hp ht
    cases t <;> simp [stepRand, Test.instr, hp, hs]

private theorem adapter_run (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    (program : List (Instr M L)) (n : ℕ) (x : State M L) :
    (randomizedFlatMachine kernel).run program n x = runRand kernel program n x := by
  induction n generalizing x with
  | zero => rw [Program.RandomizedFlatMachine.run_zero, runRand]
  | succ n ih =>
    rw [Program.RandomizedFlatMachine.run_succ, runRand]
    change (stepRand kernel program x >>= fun y =>
      (randomizedFlatMachine kernel).run program n y) = _
    simp only [ih]

/-- The assembled randomized program reaches its final halt with the structured output
distribution whenever the budget covers each path. -/
theorem runRand_program (kernel : M.Op → M.Value → M.Value → ProbComp M.Value)
    {c : Code M L} {x : State M L} {m : ProbComp (State M L × ℕ)} {T : ℕ}
    (h : Program.ExecRand (I := instructionSet M L) (Op.evalRand kernel) c x m)
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    runRand kernel c.program T { x with pc := 0 } =
      (fun z => { z.1 with pc := c.size }) <$> m := by
  have hblock : Program.Contains c.program 0 (c.assemble 0) := ⟨[], [.halt], rfl, rfl⟩
  have hr := h.runRand_assemble (randomizedFlatMachine kernel) hblock hT
  simp only [adapter_run, randomizedFlatMachine, Nat.zero_add] at hr
  rw [hr]
  have halt (y : State M L) (k : ℕ) :
      runRand kernel c.program k { y with pc := c.size } =
        pure { y with pc := c.size } := by
    have he : c.program[c.size]? = some .halt := by simp [Code.program]
    induction k with
    | zero => rfl
    | succ k ih => simp [runRand, stepRand, step, he, ih]
  simp only [halt, bind_pure_comp]

end Cslib.PointerMachine
