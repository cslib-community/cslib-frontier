/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Partrec

/-!
# Single-tape Turing machines as memory machines

A single-tape Turing machine (`Cslib.Turing.SingleTapeTM`) is a memory machine on a register
holding its optional control state (`none` once halted) beside a `MemoryModule.biTape`. The
controller halts in the halting state; otherwise it looks up the transition table, writes the
successor state to the register and performs the tape statement. This translation is step-exact
(`step_toMemoryComputer`), so runs and their lengths correspond
(`relatesInSteps_toMemoryComputer_iff`). As a `MemoryComputer` that loads the input with
`initCfg` and outputs its tape, it computes what `tm` outputs
(`outputs_iff_mem_eval_toMemoryComputer`).

## Main definitions

* `Cslib.Turing.SingleTapeTM.toMemoryComputer`. Configurations are matched with memory contents
  by `Cslib.Turing.SingleTapeTM.cfgEquiv`.

## Main results

* `Cslib.Turing.SingleTapeTM.step_toMemoryComputer`: one step of the memory machine is one step
  of the Turing machine.
* `Cslib.Turing.SingleTapeTM.relatesInSteps_toMemoryComputer_iff`: so are runs of any length.
* `Cslib.Turing.SingleTapeTM.outputs_iff_mem_eval_toMemoryComputer`: the memory computer
  computes the outputs of the Turing machine.
-/

public section

namespace Cslib.Turing.SingleTapeTM

open Cslib.Machines

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-- A single-tape Turing machine as a memory computer on its control register and its tape: it
starts in the initial state with the input on the tape, and outputs its tape. -/
@[expose] def toMemoryComputer :
    MemoryComputer (List Symbol) (BiTape Symbol) (Option tm.State × BiTape Symbol)
      (Option tm.State × Option Symbol) (Option tm.State × Stmt Symbol) where
  memory := (MemoryModule.register _).prod (MemoryModule.biTape Symbol)
  control
    | (q, a) => q.map fun q => match tm.tr q a with | (stmt, next) => (next, stmt)
  init l := tm.cfgEquiv (tm.initCfg l)
  output
    | (_, tape) => tape

/-- The memory machine of `tm` takes exactly the steps of `tm`. -/
theorem step_toMemoryComputer (c : tm.Cfg) :
    tm.toMemoryComputer.step (tm.cfgEquiv c) = (tm.step c).map tm.cfgEquiv := by
  obtain ⟨_ | q, t⟩ := c <;> rfl

/-- `tm` relates two configurations in `n` steps exactly when its memory machine does. -/
theorem relatesInSteps_toMemoryComputer_iff {c d : tm.Cfg} {n : ℕ} :
    Relation.RelatesInSteps tm.toMemoryComputer.Step (tm.cfgEquiv c) (tm.cfgEquiv d) n ↔
      Relation.RelatesInSteps tm.TransitionRelation c d n :=
  tm.toMemoryComputer.relatesInSteps_iff_of_step_eq tm.cfgEquiv tm.step_toMemoryComputer

/-- `tm` outputs `l'` on `l` exactly when its memory computer, run on `l`, halts with the tape
holding `l'` (head on its first symbol). -/
theorem outputs_iff_mem_eval_toMemoryComputer {l l' : List Symbol} :
    tm.Outputs l l' ↔ BiTape.mk₁ l' ∈ tm.toMemoryComputer.eval l := by
  rw [outputs_iff_mem_eval, MemoryComputer.eval,
    show tm.toMemoryComputer.init l = tm.cfgEquiv (tm.initCfg l) from rfl,
    tm.toMemoryComputer.eval_eq_map_of_step_eq _ tm.step_toMemoryComputer]
  simp only [Part.map_map, Part.mem_map_iff]
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨⟨_ | q, t⟩, h, hc⟩
    · cases hc
      exact h
    · simpa [step] using (StateTransition.mem_eval.1 h).2

end Cslib.Turing.SingleTapeTM
