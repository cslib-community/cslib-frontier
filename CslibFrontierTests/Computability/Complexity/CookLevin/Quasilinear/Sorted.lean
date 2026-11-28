/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Sorted

/-!
# Tests for tape contents from records sorted by position

A concrete run of four steps whose single work head alternates between cells `0` and `1`, checked
against `CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Sorted`:

* the keys `t + 4 * p t` list the times in the order `0, 2, 1, 3`;
* a repeated visit (time `2`, cell `0`) reads what its sorted predecessor (time `0`) wrote;
* the first visit of a different cell (time `1`, cell `1`) has the previous time in the sorted
  order, which visits another cell, and reads a blank;
* the repeated visit of cell `1` (time `3`) reads what time `1` wrote.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Sorted

open Cslib.Complexity.CookLevin.Quasilinear

/-- A run of four steps visiting cells `0, 1, 0, 1`; step `t` writes `true` exactly when `t = 0`. -/
def run (t : ℕ) : StepRecord 1 Unit where
  state := some ()
  inPos := 1
  pos _ := ((t % 2 : ℕ) : ℤ)
  reads _ := none
  out := .empty
  action := ⟨0, fun _ => (some (some (decide (t = 0))), 0), none, some ()⟩

/-- The position label of a time: its cell. -/
def label (t : ℕ) : ℕ := t % 2

/-- The sorted order of the times by the keys `t + 4 * label t`: `0, 2, 1, 3`. -/
def order : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- The keys increase along `order`, and equal labels are exactly equal cells. -/
private theorem sorted_hyps :
    (∀ s < 4, ∀ t < 4, (run s).pos 0 = (run t).pos 0 ↔ label s = label t) ∧
    ∀ u (hu : u < 4), 0 < u →
      (order ⟨u - 1, by omega⟩ : ℕ) + 4 * label (order ⟨u - 1, by omega⟩) <
        order ⟨u, hu⟩ + 4 * label (order ⟨u, hu⟩) := by
  refine ⟨by decide, ?_⟩
  decide

/-- A repeated visit: time `2` reads cell `0`, which time `0` wrote (`true`). -/
example : StepRecord.tapeAt run 0 2 ((run 2).pos 0) = some true := by
  have h := StepRecord.tapeAt_of_sorted run 0 (M := 4) (by decide) order label
    sorted_hyps.1 sorted_hyps.2 ⟨2, by decide⟩
  rw [h]
  decide

/-- The first visit of cell `1`: the time before `1` in the sorted order is `2`, which visits
the other cell, so time `1` reads a blank. -/
example : StepRecord.tapeAt run 0 1 ((run 1).pos 0) = none := by
  have h := StepRecord.tapeAt_of_sorted run 0 (M := 4) (by decide) order label
    sorted_hyps.1 sorted_hyps.2 ⟨1, by decide⟩
  rw [h]
  decide

/-- The repeated visit of cell `1`: time `3` reads what time `1` wrote (`false`). -/
example : StepRecord.tapeAt run 0 3 ((run 3).pos 0) = some false := by
  have h := StepRecord.tapeAt_of_sorted run 0 (M := 4) (by decide) order label
    sorted_hyps.1 sorted_hyps.2 ⟨3, by decide⟩
  rw [h]
  decide

end CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Sorted
