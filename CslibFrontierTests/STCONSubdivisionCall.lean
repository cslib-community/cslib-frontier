/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionCall

/-! Ordinary-import clients for the subdivision call to original STCON adjacency. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSubdivisionCall

open Cslib.Complexity.STCON Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

-- The subdivision kernel calls the original adjacency machine on the original word.
example (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w))
    (seed : ℕ) (weight : QueryMachine.Subdivision.Query (LayeredParameters × ℕ) → ℕ)
    (i j : ℕ) :
    let I := configurationInstance ntm c w
    let q : QueryMachine.Subdivision.Query (LayeredParameters × ℕ) :=
      ⟨(layeredParameters ntm c w.length, seed), (finProdFinEquiv (layeredCoordinates I a)).val,
        (finProdFinEquiv (layeredCoordinates I b)).val, i, j⟩
    ∃ edge, (edge = true ↔ layeredRelation I a b) ∧
      (QueryMachine.Subdivision.callback (layeredCallback ntm)
        (subdivisionLayeredCall Prod.fst) weight (Sum.elim (fun _ => false) id)).runFrom
        w (.inl (.inl q)) 3 =
        .inl (.inr (QueryMachine.Subdivision.edgeQuery q (weight q) edge)) := by
  dsimp only
  obtain ⟨edge, hrun, hedge⟩ := layeredCallback_agrees ntm c w a b
  have hreq := subdivisionLayeredCall_eq ntm c w a b i j Prod.fst
    (layeredParameters ntm c w.length, seed) rfl
  refine ⟨edge, hedge, ?_⟩
  rw [QueryMachine.Subdivision.callback_runFrom _ _ _ _ _ _ 1]
  · rw [hreq, hrun]
    rfl
  · intro clock hclock
    have : clock = 0 := Nat.lt_one_iff.mp hclock
    subst clock
    rfl
  · rw [hreq, hrun]
    rfl

-- The request's workspace certificate accepts a projection from a larger retained context.
example :
    let enc := QueryMachine.Subdivision.encQuery (encPair encLayeredParameters encNat)
    ComputableInSpace (subdivisionLayeredCall Prod.fst) enc encLayeredCallback
      (fun q => (enc q).length) :=
  subdivisionLayeredCall_inSpace _ Prod.fst (fst encLayeredParameters encNat)

end CslibFrontierTests.STCONSubdivisionCall
