/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import CslibFrontier.Computability.Automata.DPDA.Basic

/-!
# Deterministic pushdown automata as memory machines

A deterministic pushdown automaton (`Cslib.Automata.DPDA`) is a memory machine on a register
holding its control state, a `MemoryModule.stream` holding the unread input and a
`MemoryModule.stack`. The controller halts on the empty stack. Otherwise it takes the epsilon
transition for the state and stack top if there is one, leaving the input in place, and else the
transition on the next input symbol, consuming it; in both cases it writes the destination state
and replaces the stack top. This translation is step-exact (`step_toMemoryMachine`), so runs and
their lengths correspond (`relatesInSteps_toMemoryMachine_iff`).

## Main definitions

* `Cslib.Automata.DPDA.toMemoryMachine`, `Cslib.Automata.DPDA.configEquiv`.

## Main results

* `Cslib.Automata.DPDA.step_toMemoryMachine`: one step of the memory machine is one step of the
  automaton.
* `Cslib.Automata.DPDA.relatesInSteps_toMemoryMachine_iff`: so are runs of any length.
-/

public section

namespace Cslib.Automata.DPDA

open Cslib.Machines

variable {State Symbol Γ : Type*} (M : DPDA State Symbol Γ)

/-- The operation of a move: write its destination state, consume the input symbol or not, and
replace the stack top by its replacement word. -/
@[expose] def Move.toOp (consume : Bool) (move : Move State Γ) : State × Bool × List Γ :=
  (move.state, consume, move.replacement)

/-- A deterministic pushdown automaton as a memory machine on its control register, its unread
input and its stack. -/
@[expose] def toMemoryMachine :
    MemoryMachine (State × List Symbol × List Γ) (State × Option Symbol × Option Γ)
      (State × Bool × List Γ) where
  memory := (MemoryModule.register State).prod
    ((MemoryModule.stream Symbol).prod (MemoryModule.stack Γ))
  control
    | (_, _, none) => none
    | (q, a, some γ) =>
      match M.transition q γ none with
      | some move => some (move.toOp false)
      | none => a.bind fun a => (M.transition q γ (some a)).map (Move.toOp true)

/-- A configuration is its control state, its unread input and its stack. -/
@[expose] def configEquiv : Config State Symbol Γ ≃ State × List Symbol × List Γ where
  toFun c := (c.state, c.input, c.stack)
  invFun | (state, input, stack) => ⟨state, input, stack⟩

/-- The memory machine of `M` takes exactly the steps of `M`. -/
theorem step_toMemoryMachine (c : Config State Symbol Γ) :
    M.toMemoryMachine.step (configEquiv c) = (M.step? c).map configEquiv := by
  obtain ⟨q, input, _ | ⟨γ, tail⟩⟩ := c
  · rfl
  · cases hε : M.transition q γ none with
    | some move => simp [MemoryMachine.step, toMemoryMachine, configEquiv, step?, hε,
        MemoryModule.prod, MemoryModule.register, MemoryModule.stream, MemoryModule.stack,
        Move.toOp]
    | none =>
      cases input with
      | nil => simp [MemoryMachine.step, toMemoryMachine, configEquiv, step?, hε,
          MemoryModule.prod, MemoryModule.register, MemoryModule.stream, MemoryModule.stack]
      | cons a rest =>
        cases ha : M.transition q γ (some a) <;>
          simp [MemoryMachine.step, toMemoryMachine, configEquiv, step?, hε, ha,
            MemoryModule.prod, MemoryModule.register, MemoryModule.stream, MemoryModule.stack,
            Move.toOp]

/-- `M` relates two configurations in `n` steps exactly when its memory machine does. -/
theorem relatesInSteps_toMemoryMachine_iff {c d : Config State Symbol Γ} {n : ℕ} :
    Relation.RelatesInSteps M.toMemoryMachine.Step (configEquiv c) (configEquiv d) n ↔
      Relation.RelatesInSteps M.Step c d n :=
  M.toMemoryMachine.relatesInSteps_iff_of_step_eq configEquiv M.step_toMemoryMachine

end Cslib.Automata.DPDA
