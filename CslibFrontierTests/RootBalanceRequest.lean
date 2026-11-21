/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest

open Cslib Turing Turing.MultiTapeTM RootBalanceRequest Circuits.Boolean.CarryLookahead.Query

private def arg (raw : List Bool) (copies : ℕ) (c : SeededPredecessor.Context) :
    RootPredecessorQuery.Input := ⟨raw, copies, {c with labelLength := 0}⟩

private def request (p : RootPredecessorQuery.Input) : Input :=
  ((p, 5), [true, false, false, false, true, false, true, false])

private theorem prepared_request (raw : List Bool) (copies : ℕ) (c : SeededPredecessor.Context) :
    prepare (request (arg raw copies c)) =
      (RootPredecessorContext.word (withEdge (arg raw copies c) 1), ⟨5, ⟨3, 1, true⟩⟩) := by
  have h : SeededRankChallenge.run (challenge (request (arg raw copies c))) =
      .inr ⟨1, 1, true⟩ := by
    change SeededRankChallenge.run
      ⟨5, 0, [true, false, false, false, true, false, true, false]⟩ = .inr ⟨1, 1, true⟩
    decide
  simp only [prepare, selected, SeededRankRequest.run_of_query _ _ h]
  have hw : Nat.clog 2 5 = 3 := by decide
  simp only [request, challenge, hw]

-- Across all raw schedules, the same native machine retains the seed, installs edge 1, and
-- requests its second rank bit at width 3. The original edge and candidate may be arbitrary.
example : ∃ (d c k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q),
    ∀ (raw : List Bool) (copies : ℕ) (seed : SeededPredecessor.Context),
      let a := arg raw copies seed
      let p := request a
      let budget := c * (raw.length + shortSize p ^ d + 1)
      tm.ComputesInTimeAndSpace (encInput p)
        (encOutput (RootPredecessorContext.word (withEdge a 1), ⟨5, ⟨3, 1, true⟩⟩))
        budget budget := by
  obtain ⟨d, c, ⟨k, Q, hQ, tm, htm⟩, _⟩ := exists_computableInO
  exact ⟨d, c, k, Q, hQ, tm, fun raw copies seed => by
    have hraw : (request (arg raw copies seed)).1.1.raw = raw := rfl
    simpa only [prepared_request, hraw] using htm (request (arg raw copies seed))⟩
