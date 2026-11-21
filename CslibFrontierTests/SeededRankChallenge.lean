/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.PolyTime.SeededRankChallenge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.FinCases

open Cslib Cslib.SeededRankChallenge Turing Turing.MultiTapeTM

-- For five edges there are three edge digits, three rank digits and two bit-index digits.
-- The last two cases check the empty word at width zero, for two different label capacities.
private def cases : Fin 7 → Input × Result := ![
  (⟨5, 0, [true, false, false, false, true, false, true, false]⟩, .inr ⟨1, 1, true⟩),
  (⟨5, 0, [true, false, false, false, true, false, false, true]⟩, .inr ⟨1, 2, false⟩),
  (⟨5, 0, [true, false, false, false, true, false, true, true]⟩, .inl true),
  (⟨5, 1, [true, false, false, false, true, false, true, true]⟩, .inl false),
  (⟨5, 1, [true, false, true, false, true, false, true, true]⟩, .inl true),
  (⟨1, 0, []⟩, .inl true), (⟨1, 1, []⟩, .inl false)]

private theorem cases_run (i : Fin 7) : run (cases i).1 = (cases i).2 := by fin_cases i <;> decide

example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ i,
    let word := encInput (cases i).1
    let budget := c * (word.length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace word (encResult (cases i).2) budget budget := by
  obtain ⟨c, d, k, Q, hQ, tm, htm⟩ := Internal.NormalForm.polyTime computableInPolyTime_run
  exact ⟨c, d, k, Q, hQ, tm, fun i => by simpa only [cases_run] using htm (cases i).1⟩
