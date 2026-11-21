/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortQuery

open Cslib Turing Turing.MultiTapeTM RootPortQuery

private def sample (seed : SeededPredecessor.Context) (column : Bool) (i : ℕ) : Input :=
  let ctx := { seed with edge := 1, candidate := 0 }
  (⟨column, i, RootPortFinish.symbol ctx i (if column then 10 else 0)⟩,
    ⟨List.replicate 8 false, 1, ctx⟩)

private theorem query_sample (seed : SeededPredecessor.Context) (column : Bool) (i : ℕ) :
    query 1 (sample seed column i) = true := by
  have he : RootEndpointQuery.query 1 ⟨List.replicate 8 false, 1, 0⟩ = some (0, 10) := by decide
  simp only [query, finishInput, sample, RootPredecessorQuery.request, he, RootPortFinish.run_some]
  simp

-- The first half-edge in this two-row schedule has keys (0, 10). For every shared seed,
-- the same finite machine recognizes both of its groups at any requested coordinate.
example : ∃ (d c k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q),
    ∀ (seed : SeededPredecessor.Context) (column : Bool) (i : ℕ),
      let a := sample seed column i
      let budget := c * (a.2.raw.length + shortSize a ^ d + 1)
      tm.ComputesInTimeAndSpace (encInput a) (encBool true) budget budget := by
  obtain ⟨d, c, ⟨k, Q, hQ, tm, htm⟩, _⟩ := exists_computableInO 1
  exact ⟨d, c, k, Q, hQ, tm, fun seed column i => by
    simpa only [query_sample] using htm (sample seed column i)⟩
