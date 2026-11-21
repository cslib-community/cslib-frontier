/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan

/-! # Kernel evaluation of the double-counting replay -/

namespace CslibFrontierTests.DoubleCountingScanReplay

open Cslib.DoubleCounting

private def edge (u v : Fin 3) : Bool := u == 0 && v == 1

private def branch : Scan.Branch 3 := fun v =>
  if v = 0 then some [] else if v = 1 then some [1] else none

-- A singleton source walk, a one-edge walk, and a skip contribute count two and sum one.
example : (Scan.runM (Scan.readSelection branch) Scan.readNext (fun u v => pure (edge u v))
    0 1 1 ⟨2, 1⟩ []).1 = some true := by decide +kernel

-- An unsuccessful branch and a successful negative answer are distinguishable.
example : Scan.run edge 0 2 1 ⟨2, 1⟩ branch = some false := by decide +kernel
example : Scan.run edge 0 2 1 ⟨2, 0⟩ branch = none := by decide +kernel

-- Reject both a real edge over the budget and a stutter without a real edge.
example : Scan.run edge 0 1 0 ⟨2, 1⟩ branch = none := by decide +kernel
example : Scan.run edge 0 0 1 ⟨1, 1⟩
    (fun v => if v = 0 then some [0] else none) = none := by decide +kernel

-- A provider that never stops is rejected after one selection, three reads, and two queries.
private def tick {α : Type} (value : α) : StateM ℕ α := fun n => (value, n + 1)

private def overBudget := Scan.tallyM (fun _ : Fin 3 => tick true)
  (tick (some 0)) (fun _ _ => tick true) 0 1 2 0

example : overBudget.1.isNone ∧ overBudget.2 = 6 := by decide +kernel

example : overBudget.2 ≤ 3 * (2 * 2 + 2) :=
  Scan.tallyM_clock id _ _ _ 0 1 2 (fun _ _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ _ => le_rfl) 0

end CslibFrontierTests.DoubleCountingScanReplay
