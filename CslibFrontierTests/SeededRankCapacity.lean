/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.PolyTime.SeededRankCapacity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.FinCases

open Cslib.SeededRankCapacity Turing Turing.MultiTapeTM

-- The first two examples straddle the exact rank threshold. A truncated quotient, an
-- oversize shift count, zero edges and a zero-length label exercise the other boundaries.
private def cases : Fin 6 → Input × Bool := ![
  (⟨4096, 1, 1⟩, true), (⟨4096, 1, 2⟩, false), (⟨4095, 1, 1⟩, false),
  (⟨4096, 300, 0⟩, false), (⟨0, 0, 0⟩, false), (⟨2, 0, 3⟩, true)]

private theorem cases_fits (i : Fin 6) : fits (cases i).1 = (cases i).2 := by
  fin_cases i <;> decide

-- The same native finite machine processes all examples within a single polynomial in the
-- length of its mixed binary/unary input, including the 3600-place shift on a 14-bit operand.
example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ i,
    let word := encInput (cases i).1
    let budget := c * (word.length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace word (encBool (cases i).2) budget budget := by
  obtain ⟨c, d, k, Q, hQ, tm, htm⟩ := Internal.NormalForm.polyTime computableInPolyTime_fits
  exact ⟨c, d, k, Q, hQ, tm, fun i => by simpa only [cases_fits] using htm (cases i).1⟩
