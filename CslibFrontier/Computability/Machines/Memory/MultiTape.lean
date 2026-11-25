/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Multi-tape Turing machines as memory machines

On a fixed input, a multi-tape Turing machine with `k` work tapes (`Turing.MultiTapeTM`) is a
memory machine on four modules side by side: a register holding its optional control state
(`none` once halted), the read-only `MemoryModule.boundedInput`, `k` copies of
`MemoryModule.workTape` and the write-only `MemoryModule.output`. While running, the
controller performs the action that the transition function selects (`Turing.Action.toOp`); in
the halting state it halts.

Upstream's `MultiTapeTM.step` is total: a halted configuration steps to itself. The memory
machine stops instead, so it follows exactly the running steps of the Turing machine
(`step_toMemoryMachine`), and runs of the memory machine are the runs of the Turing machine
through running configurations, `MultiTapeNTM.runningStepRel`
(`relatesInSteps_toMemoryMachine_iff`).

## Main definitions

* `Turing.Action.toOp`, `Turing.MultiTapeTM.toMemoryMachine`, `Turing.MultiTapeTM.cfgEquiv`.

## Main results

* `Turing.MultiTapeTM.step_toMemoryMachine`: the memory machine halts in the halting state and
  otherwise takes the step of the Turing machine.
* `Turing.MultiTapeTM.relatesInSteps_toMemoryMachine_iff`: its runs are the running runs of the
  Turing machine.
-/

public section

namespace Turing

open Cslib.Machines Relation

variable {k : ℕ} {Symbol State : Type*}

/-- The memory contents of a `k`-tape machine on `input`: control state, input head, work tapes
and output. -/
abbrev MultiTapeContents (k : ℕ) (Symbol State : Type*) (input : List Symbol) :=
  Option State × Fin (input.length + 2) × (Fin k → CellTape Symbol) × List Symbol

/-- An action as an operation on the memory of a `k`-tape machine: write the successor state,
move the input head, write and move on each work tape (a move is `-1`, `0` or `1`), and emit the
output symbol. -/
@[expose] def Action.toOp (action : Action k Symbol State) :
    Option State × SignType × (Fin k → Option (Option Symbol) × ℤ) × Option Symbol :=
  (action.state, action.inputTape,
    fun i => match action.workTapes i with | (write, move) => (write, (move : ℤ)), action.output)

namespace MultiTapeTM

variable (tm : MultiTapeTM k Symbol State) (input : List Symbol)

/-- A multi-tape Turing machine on `input` as a memory machine. -/
@[expose] noncomputable def toMemoryMachine :
    MemoryMachine (MultiTapeContents k Symbol State input)
      (Option State × Option Symbol × (Fin k → Option Symbol) × Unit)
      (Option State × SignType × (Fin k → Option (Option Symbol) × ℤ) × Option Symbol) where
  memory := (MemoryModule.register _).prod ((MemoryModule.boundedInput input).prod
    ((MemoryModule.pi fun _ => MemoryModule.workTape Symbol).prod (MemoryModule.output Symbol)))
  control
    | (none, _) => none
    | (some q, a, work, ()) => some (tm.tr q a work).toOp

variable {input}

/-- A configuration is its control state, input head, work tapes with their heads, and output. -/
@[expose] def cfgEquiv : Cfg k Symbol State input ≃ MultiTapeContents k Symbol State input where
  toFun c := (c.state, c.inputPos, fun i => ⟨c.workTapes i, c.workTapePos i⟩, c.output)
  invFun
    | (state, inputPos, tapes, output) =>
      ⟨state, inputPos, fun i => (tapes i).cells, fun i => (tapes i).head, output⟩

/-- The memory machine of `tm` halts in the halting state, and otherwise takes the step of `tm`.
-/
theorem step_toMemoryMachine (c : Cfg k Symbol State input) :
    (tm.toMemoryMachine input).step (cfgEquiv c) = c.state.map fun _ => cfgEquiv (tm.step c) := by
  rcases hq : c.state with _ | q
  · simp [MemoryMachine.step, toMemoryMachine, cfgEquiv, MemoryModule.prod,
      MemoryModule.register, hq]
  · have hread : (MemoryModule.boundedInput input).read c.inputPos = c.inputSymbol :=
      MemoryModule.boundedInput_read c
    simp only [MemoryMachine.step, toMemoryMachine, cfgEquiv, MemoryModule.prod,
      MemoryModule.register, MemoryModule.pi, MemoryModule.workTape, id, hq, Equiv.coe_fn_mk,
      hread, Option.map_some, tm.step_of_state hq]
    congr 1
    have hwork : (fun i => c.workTapes i (c.workTapePos i)) = c.workTapeSymbols := rfl
    simp only [Action.toOp, MemoryModule.boundedInput, MemoryModule.output, Action.apply,
      Prod.mk.injEq, hwork, true_and, and_true]
    funext i
    rcases h : (tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i with ⟨_ | s, m⟩ <;> simp [h]

/-- The memory machine of `tm` relates two configurations in `n` steps exactly when `tm` does
through running configurations. -/
theorem relatesInSteps_toMemoryMachine_iff {c d : Cfg k Symbol State input} {n : ℕ} :
    RelatesInSteps (tm.toMemoryMachine input).Step (cfgEquiv c) (cfgEquiv d) n ↔
      RelatesInSteps (fun c d => (c, d) ∈ tm.runningStepRel input) c d n :=
  (tm.toMemoryMachine input).relatesInSteps_iff_of_step_iff cfgEquiv fun a b => by
    rw [MemoryMachine.Step, step_toMemoryMachine]
    rcases ha : a.state with _ | q <;> simp [Cfg.Halted, ha, eq_comm]

end MultiTapeTM

end Turing
