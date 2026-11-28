/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call
import Mathlib.Data.Nat.Find

/-!
# First returns of bounded query-machine calls

A known halting bound supplies the exact first-return clock required by the same-input call
rules. The first returned state equals the state at the known bound, because halted states are
fixed. This is an existence theorem, not a requirement that callers compute a time bound.
-/

public section

namespace Turing.QueryMachine

/-- A bounded call has a first halted clock and returns the same state as at its known bound. -/
theorem exists_first_halt_le {σ : Type} (M : QueryMachine σ) (w : List Bool) (start : σ)
    (bound : ℕ) (hbound : M.halted (M.runFrom w start bound) = true) :
    ∃ T, T ≤ bound ∧ M.halted (M.runFrom w start T) = true ∧
      (∀ t < T, M.halted (M.runFrom w start t) = false) ∧
      M.runFrom w start T = M.runFrom w start bound := by
  have hex : ∃ t, M.halted (M.runFrom w start t) = true := ⟨bound, hbound⟩
  have hT : M.halted (M.runFrom w start (Nat.find hex)) = true := Nat.find_spec hex
  have hle : Nat.find hex ≤ bound := Nat.find_min' hex hbound
  refine ⟨Nat.find hex, hle, hT, fun _ ht => Bool.eq_false_iff.mpr (Nat.find_min hex ht), ?_⟩
  have hstable : M.runFrom w start (Nat.find hex + (bound - Nat.find hex)) =
      M.runFrom w start (Nat.find hex) :=
    ({ M with init := start } : QueryMachine σ).run_add_of_halted w hT (bound - Nat.find hex)
  rwa [Nat.add_sub_of_le hle, eq_comm] at hstable

end Turing.QueryMachine
