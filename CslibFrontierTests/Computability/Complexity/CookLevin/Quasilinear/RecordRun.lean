/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.RecordRun

/-!
# Tests for the records of a run

Concrete checks for
`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.RecordRun`:

* `StepRecord.moveIn` clamps the input head to `[0, n + 1]`;
* `StepRecord.inSym` is blank at `0` and at `n + 1`, and reads the input in between;
* `tapeAt` reads what the latest earlier visit of a cell left, and a blank when no earlier step
  visited it;
* a halted record is followed by itself (`StepRecord.Follows`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.RecordRun

open Cslib.Complexity.CookLevin.Quasilinear Turing

/-! ### The input head -/

/-- Moving left at the left end, and right at the right end of an input of length `3`, stays. -/
example : StepRecord.moveIn 3 0 .neg = 0 ∧ StepRecord.moveIn 3 4 .pos = 4 := by decide

/-- Moves inside the tape. -/
example : StepRecord.moveIn 3 2 .zero = 2 ∧ StepRecord.moveIn 3 2 .pos = 3 ∧
    StepRecord.moveIn 3 2 .neg = 1 := by decide

/-- The symbol under the input head: blank at position `0` and at `n + 1`. -/
example : StepRecord.inSym [true, false] 0 = none ∧ StepRecord.inSym [true, false] 1 = some true ∧
    StepRecord.inSym [true, false] 2 = some false ∧ StepRecord.inSym [true, false] 3 = none := by
  decide

/-! ### The work tape -/

/-- A run of one work head that writes `true` and moves right at each step, from cell `0`. -/
def run (t : ℕ) : StepRecord 1 Unit where
  state := some ()
  inPos := 1
  pos _ := t
  reads _ := none
  out := .empty
  action := ⟨0, fun _ => (some (some true), 1), none, some ()⟩

/-- Cell `0` was written at step `0`; cell `1` at step `1`. -/
example : StepRecord.tapeAt run 0 2 0 = some true ∧
    StepRecord.tapeAt run 0 2 1 = some true := by decide

/-- A cell that no earlier step visited is blank, as is every cell before the first step. -/
example : StepRecord.tapeAt run 0 2 5 = none ∧ StepRecord.tapeAt run 0 0 0 = none ∧
    StepRecord.tapeAt run 0 1 1 = none := by decide

/-- A run whose head stays on cell `0`, writing `true` at step `0` and `false` afterwards. -/
def stay (t : ℕ) : StepRecord 1 Unit where
  state := some ()
  inPos := 1
  pos _ := 0
  reads _ := none
  out := .empty
  action := ⟨0, fun _ => (some (some (decide (t = 0))), 0), none, some ()⟩

/-- A later visit overwrites an earlier one. -/
example : StepRecord.tapeAt stay 0 1 0 = some true ∧ StepRecord.tapeAt stay 0 2 0 = some false := by
  decide

/-- A halted record is followed by itself. -/
example : StepRecord.Follows 3 ({ run 0 with state := none } : StepRecord 1 Unit)
    { run 0 with state := none } := ⟨rfl, rfl, rfl, rfl⟩

/-- A running record is followed by the record its action leads to: input head kept, work head
moved right, and the output view unchanged (the action of `run 0` writes no output symbol, so
pushing `none` preserves it). -/
example : StepRecord.Follows 3 (run 0) { run 1 with out := (run 0).out.push none } := by
  refine ⟨rfl, rfl, funext fun j => ?_, rfl⟩
  simp [run]

end CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.RecordRun
