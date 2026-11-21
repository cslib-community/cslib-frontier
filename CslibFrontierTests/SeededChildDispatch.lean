/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.CountingRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.FinCases

open Turing Turing.MultiTapeTM Cslib Cslib.BitString
open SeededChildWitness SeededChildWitness.Dispatch

private def b : Public := ⟨5, 6, 3⟩
private def p : Proposal := ⟨4, (1, 2), ⟨3, 0, 3, 1, 5, 2⟩⟩

private def choices (s j : ℕ) := word 3 p ++ (lowBits 3 s ++ lowBits 2 j)

-- The row-total boundary selects the column endpoint for the retained vertex rank. The
-- last selector compares the same parent edge and endpoints that the first checks received.
private def expected : Fin 8 → Branch := ![
  .inl false, .inl true, .inr (some (.inr (.inl (false, 4)), 1, true)),
  .inr (some (.inr (.inl (true, 4)), 1, false)), .inr (some (.inr (.inl (false, 5)), 1, true)),
  .inr (some (.inl 2, 1, false)), .inr (some (.inl 6, 1, false)),
  .inr (some (.inr (.inr (4, (1, 2))), 1, true))]

private theorem route (s : Fin 8) : (Dispatch.run (b, choices s.val 1)).2 = expected s := by
  fin_cases s <;> rfl

-- One actual finite machine realizes each of the eight branch outcomes.
example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ s : Fin 8,
    let x := (b, choices s.val 1)
    let input := encPair encPublic encBits x
    let bound := c * (input.length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace input
      (encPair encProposal encBranch ((Dispatch.run x).1, expected s)) bound bound := by
  obtain ⟨c, d, k, Q, hQ, tm, h⟩ := Internal.NormalForm.polyTime Dispatch.computableInPolyTime_run
  exact ⟨c, d, k, Q, hQ, tm, fun s => by simpa only [← route s] using h (b, choices s.val 1)⟩

-- Index 3 lies outside this width-three count. The two non-count branches remain available.
example : (Dispatch.run (b, choices 7 3)).2 = .inr none ∧
    (Dispatch.run (b, choices 1 3)).2 = .inl true := ⟨rfl, rfl⟩

-- The physical count uses the clamped vertex prefix, the exact port prefix, or all edges.
example : (params b (.inl 17, 2, true)).count = 6 ∧
    (params b (.inr (.inl (true, 4)), 2, true)).count = 4 ∧
    (params b (.inr (.inr (4, (1, 2))), 2, true)).count = 5 ∧
    (params b (.inl 17, 2, true)).query.width = 3 := ⟨rfl, rfl, rfl, rfl⟩
