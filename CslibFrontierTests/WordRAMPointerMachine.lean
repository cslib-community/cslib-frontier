/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.WordRAM.PointerMachine.Input
import CslibFrontier.Computability.WordRAM.PointerMachine.Simulation

/-! Canonical input heaps retain zero cells and satisfy pointer validity. Whole-program
regressions exercise numerical memory addresses, register aliasing, and source control flow. -/

set_option linter.privateModule false

open Cslib.WordRAM
open Cslib.WordRAM.PointerMachine

-- The empty input still has a length cell. An input zero is explicitly represented too.
example : (inputState 8 4 []).heap.length = 1 ∧
    ((inputState 8 4 []).heap[0]?).map (fun n => (n.data 0, n.data 2)) = some (0, 0) := by
  decide +kernel
example : (inputState 8 4 [0, 7]).heap.length = 3 ∧
    ((inputState 8 4 [0, 7]).heap[0]?).map (fun n => (n.data 0, n.data 2)) = some (1, 0) := by
  decide +kernel

example (w r : ℕ) (input : List ℕ) : (inputState w r input).Valid :=
  inputState_valid w r input
example (w r : ℕ) (input : List ℕ) :
    Represents (Data.init input) (inputState w r input) (inputTree w input)
      (inputKeys (input.length + 1)) := inputState_represents w r input

-- Load destination aliases its address; arithmetic destination aliases an argument.
-- The missing address 7 is distinct from the inserted/replaced address 6.
private def memoryProgram : Program Basis.standard 4 :=
  [.op (.const 0 6), .op (.const 1 9), .op (.store 0 1), .op (.load 0 0),
   .op (.copy 3 0), .op (.const 0 6), .op (.const 1 11), .op (.store 0 1), .op (.load 1 0),
   .op (.const 2 7), .op (.load 2 2), .op (.bin .add 1 1 2), .op (.bin .add 1 1 3), .halt 1]

private theorem memoryProgram_executes :
    Executes 8 memoryProgram (State.init [0, 7]) 20 14 :=
  Executes.of_run (fuel := 14) (by decide +kernel)

-- A backward jump and both outcomes of equality branching execute three loop iterations.
private def loopProgram : Program Basis.standard 3 :=
  [.op (.const 0 3), .op (.const 1 1), .op (.const 2 0),
   .branch (.eq 0 2) 6, .op (.bin .sub 0 0 1), .jump 3, .halt 0]

private theorem loopProgram_executes : Executes 8 loopProgram (State.init []) 0 14 :=
  Executes.of_run (fuel := 14) (by decide +kernel)

private def targetRunAux {r : ℕ}
    (code : List (Cslib.PointerMachine.Instr (model 8) (layout r))) :
    ℕ → Cslib.PointerMachine.State (model 8) (layout r) →
      Cslib.PointerMachine.State (model 8) (layout r)
  | 0, s => s
  | fuel + 1, s => match Cslib.PointerMachine.step code s with
    | none => s
    | some t => targetRunAux code fuel t

private def targetRun {r : ℕ} (p : Program Basis.standard r) (input : List ℕ) (fuel : ℕ) :
    Cslib.PointerMachine.State (model 8) (layout r) :=
  targetRunAux (compile 8 p) fuel (inputState 8 r input)

private def atHalt {r : ℕ} (p : Program Basis.standard r)
    (s : Cslib.PointerMachine.State (model 8) (layout r)) : Bool :=
  match (compile 8 p)[s.pc]? with
  | some .halt => true
  | _ => false

-- Check the generated finite program itself, including the output register and terminal halt.
example : let t := targetRun loopProgram [] 60
    t.data 3 = 0 ∧ t.heap.length = 1 ∧ atHalt loopProgram t = true := by
  decide +kernel

-- The uniform simulation theorem supplies charged execution and pointer validity, without
-- assuming a dictionary realization or a target execution certificate.
example : ∃ t time,
    Cslib.PointerMachine.Executes (compile 8 memoryProgram) (inputState 8 4 [0, 7]) t time ∧
      t.data 3 = 20 ∧ time ≤ 17248 ∧ t.heap.length ≤ 16 ∧ t.Valid :=
  executes_input memoryProgram_executes

example : ∃ t time,
    Cslib.PointerMachine.Executes (compile 8 loopProgram) (inputState 8 3 []) t time ∧
      t.data 3 = 0 ∧ time ≤ 13132 ∧ t.heap.length ≤ 14 ∧ t.Valid :=
  executes_input loopProgram_executes
