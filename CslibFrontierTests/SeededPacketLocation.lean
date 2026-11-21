/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.PolyTime.SeededPacketLocation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.FinCases

open Cslib.SeededPacketLocation Turing Turing.MultiTapeTM

-- An unequal symbol pair keeps its slot across two rank orientations. An equal pair reads
-- the rank bit. Large ranks with zero and one coordinate retain the complete block number.
private def cases : Fin 5 → Input × (ℕ × ℕ) := ![
  (⟨1, 5, 1, 0⟩, (69, 1)), (⟨1, 5, 1, 1⟩, (321, 1)),
  (⟨1, 3, 3, 5⟩, (8387, 1)),
  (⟨0, 111, 222, 2 ^ 100⟩, (2 ^ 100, 0)),
  (⟨1, 0, 0, 2 ^ 100⟩, (2 ^ 111, 0))]

private theorem cases_run (i : Fin 5) : run (cases i).1 = (cases i).2 := by fin_cases i <;> decide

example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ i,
    let word := encInput (cases i).1
    let budget := c * (word.length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace word ((encPair encNat encNat) (cases i).2) budget budget := by
  obtain ⟨c, d, k, Q, hQ, tm, htm⟩ := Internal.NormalForm.polyTime computableInPolyTime_run
  exact ⟨c, d, k, Q, hQ, tm, fun i => by simpa only [cases_run] using htm (cases i).1⟩
