/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.MaxFlow.RelabelToFront
public import CslibFrontier.Algorithms.WordRAM.PushRelabel
public meta import CslibFrontier.Algorithms.WordRAM.PushRelabel
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Word-RAM Relabel-to-Front Max-Flow Tests

Kernel-checked examples (`by decide +kernel`, no `native_decide`) and fast compiled Word-RAM
executions (`Cslib.WordRAM.Code.eval` and `Cslib.WordRAM.Program.runFast` /
`Program.runFastList` via `FastEval`) for `Cslib.Algorithms.WordRAM.PushRelabel`:

1. **CLRS 6-vertex network (`clrsInst`):**
   verifies `program_spec`, `executes_maxFlowValue`, `computesListInTime_pushRelabel`,
   `computesInTime_maxFlowValue`, maximum-flow value `23`, minimum gap cut `{0, 1, 2, 4}`, and
   joint `[23, cut..., flow...]` list output at 16-bit and 20-bit word widths.
2. **Move-to-front back-push witness (`mtfInst`):**
   5-vertex network triggering move-to-front list shifts (`discharges > |V| - 2`), flow value `5`.
3. **Subtle model boundaries & degenerate instances:**
   self-loops (`selfLoopInst`), arcs entering `s` and leaving `t` (`backArcInst`),
   antiparallel arcs (`antiInst`), direct `s → t` arc (`directInst`, zero non-terminals),
   unreachable sink (`cutOffInst`, value `0`), and `s = t` zero-out branch (`loopInst`,
   `loop2Inst`).
4. **Width independence and determinism:**
   instantiates `not_readsWidth_program`, `isRandFree_program`, `not_readsWidth_flowProgram`, and
   `isRandFree_flowProgram`.
-/

public section

namespace CslibFrontierTests.WordRAMPushRelabel

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.PushRelabel

private meta def runStructured (inst : Instance) (w : ℕ) :
    Option (ℕ × List ℕ × Bool × Bool) :=
  (solver.eval w (prTime inst.n) (Data.init inst.encode)).map fun (y, t) =>
    let out := outputList y.mem (y.regs outBase)
    (y.regs acc, out.take (1 + inst.n), decide (out == inst.answerWords),
      decide (t < prTime inst.n))

private meta def runFlat (inst : Instance) (w : ℕ) : Option (ℕ × Bool × Bool) :=
  do
    let (l, tList) ← program.runFastList w (prTime inst.n) inst.encode
    let (v, tVal) ← flowProgram.runFast w (prTime inst.n) inst.encode
    return (v, decide (l == inst.answerWords),
      decide (tList ≤ prTime inst.n ∧ tVal ≤ prTime inst.n))

/-! ### CLRS 6-vertex network -/

/-- CLRS 6-vertex capacity matrix (`s = 0`, `t = 5`, antiparallel arcs `(1, 2)` and `(2, 1)`). -/
def clrsCap (u v : Fin 6) : ℕ :=
  match u.1, v.1 with
  | 0, 1 => 16
  | 0, 2 => 13
  | 1, 2 => 10
  | 2, 1 => 4
  | 1, 3 => 12
  | 3, 2 => 9
  | 2, 4 => 14
  | 4, 3 => 7
  | 3, 5 => 20
  | 4, 5 => 4
  | _, _ => 0

/-- CLRS 6-vertex Word-RAM instance (`maxFlowValue = 23`). -/
abbrev clrsInst : Instance := ⟨6, 0, 5, clrsCap⟩

example : clrsInst.s ≠ clrsInst.t := by decide

example : clrsInst.maxFlowValue = 23 ∧
    (clrsInst.maxFlowValue : ℤ) = clrsInst.out.flow.value ∧
    clrsInst.out.flow.IsMaxFlow ∧
    clrsInst.toNetwork.IsMinCut clrsInst.out.cut := by
  have hval : clrsInst.maxFlowValue = 23 := by decide +kernel
  exact ⟨hval, clrsInst.natCast_maxFlowValue,
    clrsInst.isMaxFlow_out (by decide), clrsInst.isMinCut_out (by decide)⟩

example : ∃ steps ≤ prTime 6,
    ExecutesList 16 program (State.init clrsInst.encode) clrsInst.answerWords steps ∧
    ∃ vsteps ≤ prTime 6, Executes 16 flowProgram (State.init clrsInst.encode) 23 vsteps := by
  have hfit : Fits 16 clrsInst.wordBound := by decide +kernel
  have hval : clrsInst.maxFlowValue = 23 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec clrsInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue clrsInst hfit
  exact ⟨steps, hle, hex, vsteps, hvle, hval ▸ hvex⟩

example :
    (∃ steps ≤ prTime 6,
      ExecutesList 20 program (State.init clrsInst.encode) clrsInst.answerWords steps) ∧
    (∃ steps ≤ prTime 6,
      Executes 20 flowProgram (State.init clrsInst.encode) clrsInst.maxFlowValue steps) := by
  have hfit : Fits 20 clrsInst.wordBound := by decide +kernel
  have hin : InputFits 20 clrsInst.encode := clrsInst.inputFits_encode hfit
  refine ⟨?_, ?_⟩
  · obtain ⟨steps, hex, hle⟩ := computesListInTime_pushRelabel clrsInst 20 hfit hin
    exact ⟨steps, hle, hex⟩
  · obtain ⟨steps, hex, hle⟩ := computesInTime_maxFlowValue clrsInst 20 hfit hin
    exact ⟨steps, hle, hex⟩

/-- info: some (23, [23, 1, 1, 1, 0, 1, 0], true, true) -/
#guard_msgs in
#eval runStructured clrsInst 16

/-- info: some (23, true, true) -/
#guard_msgs in
#eval runFlat clrsInst 16

/-- info: some (23, true, true) -/
#guard_msgs in
#eval runFlat clrsInst 20

/-! ### Move-to-front back-push witness -/

/-- Network `0 → 2 → 1 → 3 → 4` where vertex `2` relabels past `1` and triggers move-to-front. -/
def mtfCap (u v : Fin 5) : ℕ :=
  match u.1, v.1 with
  | 0, 2 => 5
  | 2, 1 => 5
  | 1, 3 => 5
  | 3, 4 => 5
  | _, _ => 0

/-- Move-to-front Word-RAM instance (`maxFlowValue = 5`). -/
abbrev mtfInst : Instance := ⟨5, 0, 4, mtfCap⟩

example : ∃ steps ≤ prTime 5,
    ExecutesList 16 program (State.init mtfInst.encode) mtfInst.answerWords steps ∧
    ∃ vsteps ≤ prTime 5, Executes 16 flowProgram (State.init mtfInst.encode) 5 vsteps := by
  have hfit : Fits 16 mtfInst.wordBound := by decide +kernel
  have hval : mtfInst.maxFlowValue = 5 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec mtfInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue mtfInst hfit
  exact ⟨steps, hle, hex, vsteps, hvle, hval ▸ hvex⟩

/-- info: some (5, [5, 1, 0, 0, 0, 0], true, true) -/
#guard_msgs in
#eval runStructured mtfInst 16

/-- info: some (5, true, true) -/
#guard_msgs in
#eval runFlat mtfInst 16

/-! ### Model boundaries and degenerate instances -/

/-- Self-loop capacity matrix: high-capacity self-loop `(1, 1)` does not inflate flow. -/
def selfLoopCap (u v : Fin 3) : ℕ :=
  match u.1, v.1 with
  | 0, 1 => 4
  | 1, 1 => 9
  | 1, 2 => 4
  | _, _ => 0

/-- Self-loop Word-RAM instance (`maxFlowValue = 4`). -/
abbrev selfLoopInst : Instance := ⟨3, 0, 2, selfLoopCap⟩

example : ∃ steps ≤ prTime 3,
    ExecutesList 16 program (State.init selfLoopInst.encode) selfLoopInst.answerWords steps ∧
    ∃ vsteps ≤ prTime 3, Executes 16 flowProgram (State.init selfLoopInst.encode) 4 vsteps := by
  have hfit : Fits 16 selfLoopInst.wordBound := by decide +kernel
  have hval : selfLoopInst.maxFlowValue = 4 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec selfLoopInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue selfLoopInst hfit
  exact ⟨steps, hle, hex, vsteps, hvle, hval ▸ hvex⟩

/-- info: some (4, [4, 1, 0, 0], true, true) -/
#guard_msgs in
#eval runStructured selfLoopInst 16

/-- Arcs entering `s = 0` (`(1, 0)`) and leaving `t = 2` (`(2, 1)`). -/
def backArcCap (u v : Fin 3) : ℕ :=
  match u.1, v.1 with
  | 0, 1 => 5
  | 1, 2 => 4
  | 1, 0 => 3
  | 2, 1 => 2
  | _, _ => 0

/-- Back-arc Word-RAM instance (`maxFlowValue = 4`). -/
abbrev backArcInst : Instance := ⟨3, 0, 2, backArcCap⟩

example : ∃ steps ≤ prTime 3,
    Executes 16 flowProgram (State.init backArcInst.encode) 4 steps := by
  have hfit : Fits 16 backArcInst.wordBound := by decide +kernel
  have hval : backArcInst.maxFlowValue = 4 := by decide +kernel
  obtain ⟨steps, hex, hle⟩ := executes_maxFlowValue backArcInst hfit
  exact ⟨steps, hle, hval ▸ hex⟩

/-- info: some (4, [4, 1, 1, 0], true, true) -/
#guard_msgs in
#eval runStructured backArcInst 16

/-- 4-vertex network with antiparallel arcs `(1, 2)` and `(2, 1)`. -/
def antiCap (u v : Fin 4) : ℕ :=
  match u.1, v.1 with
  | 0, 1 => 2
  | 0, 2 => 2
  | 1, 2 => 1
  | 2, 1 => 1
  | 1, 3 => 1
  | 2, 3 => 3
  | _, _ => 0

/-- Antiparallel-arc Word-RAM instance (`maxFlowValue = 4`). -/
abbrev antiInst : Instance := ⟨4, 0, 3, antiCap⟩

example : ∃ steps ≤ prTime 4,
    ExecutesList 16 program (State.init antiInst.encode) antiInst.answerWords steps ∧
    ∃ vsteps ≤ prTime 4, Executes 16 flowProgram (State.init antiInst.encode) 4 vsteps := by
  have hfit : Fits 16 antiInst.wordBound := by decide +kernel
  have hval : antiInst.maxFlowValue = 4 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec antiInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue antiInst hfit
  exact ⟨steps, hle, hex, vsteps, hvle, hval ▸ hvex⟩

/-- info: some (4, [4, 1, 0, 0, 0], true, true) -/
#guard_msgs in
#eval runStructured antiInst 16

/-- Direct `s → t` network (`n = 2`, zero non-terminal vertices). -/
abbrev directInst : Instance := ⟨2, 0, 1, fun u v => if u.1 = 0 ∧ v.1 = 1 then 7 else 0⟩

example : ∃ steps ≤ prTime 2,
    ExecutesList 16 program (State.init directInst.encode) [7, 1, 0, 0, 7, 0, 0] steps ∧
    ∃ vsteps ≤ prTime 2, Executes 16 flowProgram (State.init directInst.encode) 7 vsteps := by
  have hfit : Fits 16 directInst.wordBound := by decide +kernel
  have hans : directInst.answerWords = [7, 1, 0, 0, 7, 0, 0] := by decide +kernel
  have hval : directInst.maxFlowValue = 7 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec directInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue directInst hfit
  exact ⟨steps, hle, hans ▸ hex, vsteps, hvle, hval ▸ hvex⟩

/-- info: some (7, [7, 1, 0], true, true) -/
#guard_msgs in
#eval runStructured directInst 16

/-- info: some (7, true, true) -/
#guard_msgs in
#eval runFlat directInst 16

/-- Unreachable sink `t = 2`: flow value `0`. -/
def cutOffCap (u v : Fin 3) : ℕ :=
  match u.1, v.1 with
  | 0, 1 => 5
  | 2, 1 => 5
  | _, _ => 0

/-- Unreachable-sink Word-RAM instance (`maxFlowValue = 0`). -/
abbrev cutOffInst : Instance := ⟨3, 0, 2, cutOffCap⟩

example : ∃ steps ≤ prTime 3,
    Executes 16 flowProgram (State.init cutOffInst.encode) 0 steps := by
  have hfit : Fits 16 cutOffInst.wordBound := by decide +kernel
  have hval : cutOffInst.maxFlowValue = 0 := by decide +kernel
  obtain ⟨steps, hex, hle⟩ := executes_maxFlowValue cutOffInst hfit
  exact ⟨steps, hle, hval ▸ hex⟩

/-- info: some (0, [0, 1, 1, 0], true, true) -/
#guard_msgs in
#eval runStructured cutOffInst 16

/-- Degenerate `s = t`, `n = 1`: enters the `zeroOutCode` branch and returns `[0, 0, 0]`. -/
abbrev loopInst : Instance := ⟨1, 0, 0, fun _ _ => 5⟩

example : ∃ steps ≤ prTime 1,
    ExecutesList 16 program (State.init loopInst.encode) [0, 0, 0] steps ∧
    ∃ vsteps ≤ prTime 1, Executes 16 flowProgram (State.init loopInst.encode) 0 vsteps := by
  have hfit : Fits 16 loopInst.wordBound := by decide +kernel
  have hans : loopInst.answerWords = [0, 0, 0] := by decide +kernel
  have hval : loopInst.maxFlowValue = 0 := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec loopInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue loopInst hfit
  exact ⟨steps, hle, hans ▸ hex, vsteps, hvle, hval ▸ hvex⟩

/-- info: some (0, [0, 0], true, true) -/
#guard_msgs in
#eval runStructured loopInst 16

/-- Degenerate `s = t`, `n = 2`: `zeroOutCode` zeros `[1 + n + n²]` output block cleanly. -/
abbrev loop2Inst : Instance := ⟨2, 0, 0, fun _ _ => 3⟩

example : ∃ steps ≤ prTime 2,
    ExecutesList 16 program (State.init loop2Inst.encode) [0, 0, 0, 0, 0, 0, 0] steps := by
  have hfit : Fits 16 loop2Inst.wordBound := by decide +kernel
  have hans : loop2Inst.answerWords = [0, 0, 0, 0, 0, 0, 0] := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec loop2Inst hfit
  exact ⟨steps, hle, hans ▸ hex⟩

/-- info: some (0, true, true) -/
#guard_msgs in
#eval runFlat loop2Inst 16

/-- All-zero capacity matrix with `s ≠ t` (`maxCap = 0`): tests the edge `0`-capacity word-bound
and outputs `[0, 1, 0, 0, ...]`. -/
abbrev zeroCapInst : Instance := ⟨3, 0, 2, fun _ _ => 0⟩

example : zeroCapInst.s ≠ zeroCapInst.t ∧
    zeroCapInst.maxCap = 0 ∧
    zeroCapInst.maxFlowValue = 0 ∧
    (∃ steps ≤ prTime 3,
      ExecutesList 16 program (State.init zeroCapInst.encode) zeroCapInst.answerWords steps) ∧
    (∃ vsteps ≤ prTime 3,
      Executes 16 flowProgram (State.init zeroCapInst.encode) 0 vsteps) := by
  have hmc : zeroCapInst.maxCap = 0 := by decide +kernel
  have hval : zeroCapInst.maxFlowValue = 0 := by decide +kernel
  have hfit : Fits 16 zeroCapInst.wordBound := by decide +kernel
  obtain ⟨steps, hle, hex⟩ := program_spec zeroCapInst hfit
  obtain ⟨vsteps, hvex, hvle⟩ := executes_maxFlowValue zeroCapInst hfit
  exact ⟨by decide, hmc, hval, ⟨steps, hle, hex⟩, ⟨vsteps, hvle, hval ▸ hvex⟩⟩

/-- info: some (0, [0, 1, 0, 0], true, true) -/
#guard_msgs in
#eval runStructured zeroCapInst 16

/-- Negative word-bound check: `6`-bit words (`2^6 = 64`) fail `Fits 6 clrsInst.wordBound`. -/
example : ¬ Fits 6 clrsInst.wordBound := by decide +kernel

/-! ### Width independence and determinism -/

example : ¬ program.ReadsWidth ∧ program.IsRandFree ∧
    ¬ flowProgram.ReadsWidth ∧ flowProgram.IsRandFree :=
  ⟨not_readsWidth_program, isRandFree_program,
    not_readsWidth_flowProgram, isRandFree_flowProgram⟩

end CslibFrontierTests.WordRAMPushRelabel
