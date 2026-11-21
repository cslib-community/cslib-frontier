/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAlgorithm
import Mathlib.Tactic.FinCases

open Turing Turing.MultiTapeTM RootEndpointQuery RootEndpointInput RootEndpointFinish

private def requests : Fin 6 → RootEndpointQuery.Input × Option (ℕ × ℕ) := ![
  (⟨List.replicate 8 false, 2, 1⟩, some (0, 11)),
  (⟨List.replicate 8 false, 2, 17⟩, some (1, 11)),
  (⟨[false, false, false, true, false, false, false, false], 1, 10⟩, some (4, 12)),
  (⟨[false, false, false, true, false, false, false, false], 1, 12⟩, some (1, 14)),
  (⟨[false, false, true, true], 1, 0⟩, none),
  (⟨List.replicate 8 false, 1, 2 ^ 100⟩, none)]

-- One finite machine handles direct rows, work hits, work exhaustion, malformed schedules
-- and large padded edges. Its input word includes the full raw schedule and both binary keys.
example : ∃ (d c K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q), ∀ i,
    let a := (requests i).1
    let budget := c * (a.raw.length + shortSize a ^ d + 1)
    tm.ComputesInTimeAndSpace (RootEndpointInput.encInput a) (encOutput (requests i).2)
      budget budget := by
  obtain ⟨d, c, ⟨K, Q, hQ, tm, htm⟩, _⟩ := RootEndpointAlgorithm.exists_computableInO 1
  refine ⟨d, c, K, Q, hQ, tm, fun i => ?_⟩
  have h : query 1 (requests i).1 = (requests i).2 := by fin_cases i <;> decide
  simpa only [h] using htm (requests i).1
