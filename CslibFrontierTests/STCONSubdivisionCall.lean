/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionCall
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.FlatQuery

/-! Ordinary-import clients for the subdivision call to original STCON adjacency. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSubdivisionCall

open Cslib.Complexity.STCON Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.QueryMachine.Subdivision

variable {k : ℕ} {State : Type} [Fintype State]

-- Starting from two flat scan IDs, the subdivision kernel calls the original adjacency
-- machine on the original word and returns the caller's edge verdict.
example (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (a b : LayeredGraphVertex (configurationInstance ntm c w))
    (seed : ℕ) (weight : Query (LayeredParameters × ℕ) → ℕ)
    {bound : ℕ} (i j : Fin (bound + 1)) :
    let I := configurationInstance ntm c w
    let ctx := (layeredParameters ntm c w.length, seed)
    let u := finProdFinEquiv (layeredCoordinates I a)
    let v := finProdFinEquiv (layeredCoordinates I b)
    let index := flatIndex (((I.n - 1) + 1) * I.n) bound
    let flat : FlatQuery (LayeredParameters × ℕ) :=
      ⟨ctx, bound, (index ⟨u, i⟩).val, (index ⟨v, j⟩).val⟩
    let q : Query (LayeredParameters × ℕ) := ⟨ctx, u.val, v.val, i.val, j.val⟩
    ∃ edge, (edge = true ↔ layeredRelation I a b) ∧
      (callback (layeredCallback ntm) (subdivisionLayeredCall Prod.fst)
        weight (Sum.elim (fun _ => false) id)).runFrom w (flatCallbackStart flat) 3 =
        .inl (.inr (edgeQuery q (weight q) edge)) := by
  dsimp only
  obtain ⟨edge, hrun, hedge⟩ := layeredCallback_agrees ntm c w a b
  have hreq := subdivisionLayeredCall_eq ntm c w a b i j Prod.fst
    (layeredParameters ntm c w.length, seed) rfl
  refine ⟨edge, hedge, ?_⟩
  rw [flatCallbackStart, decodeFlatQuery_flatIndex, callback_runFrom _ _ _ _ _ _ 1]
  · rw [hreq, hrun]
    rfl
  · intro clock hclock
    have : clock = 0 := Nat.lt_one_iff.mp hclock
    subst clock
    rfl
  · rw [hreq, hrun]
    rfl

-- The flat request can supply an initial state directly to this encoded call interface.
example :
    let encCtx := encPair encLayeredParameters encNat
    let encFlat := encFlatQuery encCtx
    ComputableInSpace flatCallbackStart encFlat (encCallback encCtx encLayeredCallback)
      (fun q => (encFlat q).length) :=
  flatCallbackStart_inSpace _ _

-- The request's workspace certificate accepts a projection from a larger retained context.
example :
    let enc := QueryMachine.Subdivision.encQuery (encPair encLayeredParameters encNat)
    ComputableInSpace (subdivisionLayeredCall Prod.fst) enc encLayeredCallback
      (fun q => (enc q).length) :=
  subdivisionLayeredCall_inSpace _ Prod.fst (fst encLayeredParameters encNat)

end CslibFrontierTests.STCONSubdivisionCall
