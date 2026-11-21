/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import Cslib.Computability.URM.Execution

/-!
# Unlimited register machines as memory machines

An unlimited register machine (`Cslib.URM`) runs a program on a program counter and a bank of
registers holding natural numbers. Its instructions can only test whether two registers are
equal, so the bank is a memory module (`Cslib.URM.registerBank`) whose observation is the
equality pattern of its registers and whose operations are the instructions themselves: `Z`, `S`
and `T` update the registers and a jump `J` leaves them alone. The program counter is a
`MemoryModule.register`. The controller looks up the instruction at the program counter (halting
past the end of the program), and computes the next program counter from the observed equality
for a jump.

This translation is step-exact (`step_toMemoryComputer_iff`), and the memory computer that loads
the inputs into the registers and outputs register `0` computes `URM.eval`
(`eval_toMemoryComputer`).

## Main definitions

* `Cslib.URM.registerBank`, `Cslib.URM.toMemoryComputer`, `Cslib.URM.stateEquiv`.

## Main results

* `Cslib.URM.step_toMemoryComputer_iff`: one step of the memory machine is one step of the
  program.
* `Cslib.URM.eval_toMemoryComputer`: the memory computer computes what the program computes.
-/

public section

namespace Cslib.URM

open Cslib.Machines Relation

/-- The registers of a URM as a memory module: the controller sees which registers hold equal
values, and an instruction updates the registers as it does in the machine. A jump leaves them
alone. -/
@[expose] def registerBank : MemoryModule Regs (ℕ → ℕ → Bool) Instr where
  tr σ
    | .Z n => σ.write n 0
    | .S n => σ.write n (σ.read n + 1)
    | .T m n => σ.write n (σ.read m)
    | .J .. => σ
  read σ m n := σ.read m = σ.read n

/-- The program counter after an instruction, given the observed equality pattern. -/
@[expose] def Instr.nextPc (pc : ℕ) (eq : ℕ → ℕ → Bool) : Instr → ℕ
  | .J m n q => if eq m n then q else pc + 1
  | _ => pc + 1

variable (p : Program)

/-- A URM program as a memory computer on its program counter and its registers: it starts at
instruction `0` with the inputs in the first registers, and outputs register `0`. -/
@[expose] def toMemoryComputer :
    MemoryComputer (List ℕ) ℕ (ℕ × Regs) (ℕ × (ℕ → ℕ → Bool)) (ℕ × Instr) where
  memory := (MemoryModule.register ℕ).prod registerBank
  control
    | (pc, eq) => p[pc]?.map fun instr => (instr.nextPc pc eq, instr)
  init inputs := (0, Regs.ofInputs inputs)
  output
    | (_, regs) => regs.output

/-- A machine state is its program counter and its registers. -/
@[expose] def stateEquiv : State ≃ ℕ × Regs where
  toFun s := (s.pc, s.regs)
  invFun
    | (pc, regs) => ⟨pc, regs⟩

/-- The memory machine of `p` takes exactly the steps of `p`. -/
theorem step_toMemoryComputer_iff (s s' : State) :
    (toMemoryComputer p).Step (stateEquiv s) (stateEquiv s') ↔ Step p s s' := by
  obtain ⟨pc, regs⟩ := s
  obtain ⟨pc', regs'⟩ := s'
  simp only [MemoryMachine.Step, MemoryMachine.step, toMemoryComputer, stateEquiv,
    Equiv.coe_fn_mk, MemoryModule.prod, MemoryModule.register, id, Option.mem_def,
    Option.map_map]
  rcases h : p[pc]? with _ | instr
  · simp only [Option.map_none, reduceCtorEq, false_iff]
    rintro (⟨h'⟩ | ⟨h'⟩ | ⟨h'⟩ | ⟨h', -⟩ | ⟨h', -⟩) <;> simp_all
  · simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rcases instr with n | n | ⟨m, n⟩ | ⟨m, n, q⟩ <;>
        rintro ⟨rfl, rfl⟩ <;> simp only [Instr.nextPc, registerBank]
      · exact .zero h
      · exact .succ h
      · exact .transfer h
      · by_cases heq : regs.read m = regs.read n
        · simpa [heq] using Step.jump_eq h heq
        · simpa [heq] using Step.jump_ne h heq
    · intro hs
      cases hs with
      | zero h' | succ h' | transfer h' | jump_eq h' _ | jump_ne h' _ =>
        simp only [h, Option.some.injEq] at h'
        subst h'
        simp_all [Instr.nextPc, registerBank]

/-- The memory computer of `p` computes what `p` computes. -/
theorem eval_toMemoryComputer (inputs : List ℕ) :
    (toMemoryComputer p).eval inputs = eval p inputs := by
  ext result
  rw [Part.eq_some_iff.symm.trans (haltsWithResult_iff_eval (p := p)).symm, MemoryComputer.eval,
    Part.mem_map_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [StateTransition.mem_eval] at hc
    obtain ⟨hrun, hhalt⟩ := hc
    refine ⟨stateEquiv.symm c, ?_, ?_, rfl⟩
    · have := ((toMemoryComputer p).reflTransGen_iff_of_step_iff stateEquiv
        (step_toMemoryComputer_iff p) (a := State.init inputs) (b := stateEquiv.symm c)).1
        (by rw [Equiv.apply_symm_apply]; exact hrun)
      exact this
    · simp only [State.isHalted, ← List.getElem?_eq_none_iff]
      simpa [MemoryMachine.step, toMemoryComputer, MemoryModule.prod, MemoryModule.register,
        stateEquiv] using hhalt
  · rintro ⟨s, hrun, hhalt, rfl⟩
    refine ⟨stateEquiv s, StateTransition.mem_eval.2 ⟨?_, ?_⟩, rfl⟩
    · exact ((toMemoryComputer p).reflTransGen_iff_of_step_iff stateEquiv
        (step_toMemoryComputer_iff p)).2 hrun
    · simp only [State.isHalted, ← List.getElem?_eq_none_iff] at hhalt
      simp [MemoryMachine.step, toMemoryComputer, MemoryModule.prod, MemoryModule.register,
        stateEquiv, hhalt]

end Cslib.URM
