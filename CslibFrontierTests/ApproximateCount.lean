/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.ApproximateCount

/-! Nonvacuous boundary witnesses for overlapping approximate counts. -/

set_option linter.privateModule false

open Cslib.Circuits.Boolean.ApproximateCount

-- Equal overlaps, including the zero value.
example : correctBlock 4 3 15 = ⟨3, false⟩ := by rfl
example : (correctBlock 4 0 0).extend 4 0 = 0 := by decide

-- The previous high part rounded up; its residue wraps from three to zero.
example : correctBlock 4 4 15 = ⟨3, true⟩ := by rfl
example : (correctBlock 4 4 15).extend 4 4 = 15 := by decide

-- The new estimate rounded up across a radix boundary. Replacing the zero digit
-- by the largest radix digit recovers the true value, rather than the new estimate.
example : correctBlock 4 3 16 = ⟨3, false⟩ := by rfl
example : (correctBlock 4 3 16).extend 4 3 = 15 := by decide

-- Both estimates may round up, and the decoder may legitimately return the successor.
example : (correctBlock 4 4 16).extend 4 4 = 16 := by decide

-- Independently chosen errors at all three levels: true high parts of 59 are 59, 14, 3.
private def mixedEstimates (i : ℕ) : ℕ := if i = 0 then 60 else if i = 1 then 14 else 4

example : (∀ i ≤ 2, mixedEstimates i = 59 / 4 ^ i ∨
    mixedEstimates i = 59 / 4 ^ i + 1) ∧ reconstruct 4 2 mixedEstimates = 59 := by
  constructor
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · decide

-- The implementation depends on its inputs: choosing all upper approximations changes
-- the returned value to 60. It does not choose an exact code from the specification's value.
example : reconstruct 4 2 (fun i => 59 / 4 ^ i + 1) = 60 := by decide

-- A unit radix is outside the paper's two-bit implementation, but the generalized
-- arithmetic invariant covers it. This exercises radix=1 and the initial-estimate case.
example : reconstruct 1 2 (fun _ => 1) = 1 := by decide
example : reconstruct 4 0 (fun _ => 7) = 7 := by decide

-- The native formula and arithmetic agree on the wraparound borrow.
example : (borrowFormula (0 : Fin 4) 1 2 3).eval Cslib.Circuits.Boolean.interpretation
    ![false, false, true, true] = true := by decide
