/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionEndpoints
import CslibFrontier.Foundations.Relation.Transport

/-! Ordinary-import client for the scanner's binary source and target IDs. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSubdivisionEndpoints

open Cslib.Complexity Cslib.Complexity.STCON Cslib.LayeredDigraph.Subdivision
open Turing Turing.QueryMachine.Subdivision

-- The callback decodes an indexed edge using the same numbering used for the endpoints.
example (I : STCONInstance) (bound : ℕ)
    (a b : Vertex (Fin ((I.n - 1) + 1) × Fin I.n) bound) :
    decodeFlatQuery
      ⟨(), bound, (subdivisionIndex I bound a).val, (subdivisionIndex I bound b).val⟩ =
        ⟨(), (finProdFinEquiv a.vertex).val, (finProdFinEquiv b.vertex).val,
          a.offset.val, b.offset.val⟩ := by
  rw [subdivisionIndex_apply, subdivisionIndex_apply, decodeFlatQuery_flatIndex]

-- A scanner using the flat adjacency relation and native endpoint IDs asks the original
-- configuration reachability question. The weight bound allows unused subdivision slots.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (bound : ℕ) :
    let I := configurationInstance ntm c w
    let index := subdivisionIndex I bound
    let ids := subdivisionEndpointIDs (layeredParameters ntm c w.length, bound)
    ∀ (weight : Fin ((I.n - 1) + 1) × Fin I.n → ℕ),
      (∀ v, weight v ≤ bound) →
      ∃ s t : Fin ((((I.n - 1) + 1) * I.n) * (bound + 1)),
        (s.val, t.val) = ids ∧
        (Relation.ReflTransGen
          (fun a b => (graph (layeredDigraph I) weight bound).Adj (index.symm a) (index.symm b))
          s t ↔ I ∈ STCON) := by
  intro I index ids weight hw
  let s := root bound (layeredCoordinates I (layeredStart I))
  let t := root bound (layeredCoordinates I (layeredTarget I))
  have hindex := Relation.reflTransGen_equiv_iff index
    (r := (graph (layeredDigraph I) weight bound).Adj)
    (s := fun a b => (graph (layeredDigraph I) weight bound).Adj (index.symm a) (index.symm b))
    (fun a b => by simp) s t
  exact ⟨index s, index t, (subdivisionEndpointIDs_eq ntm c w bound).symm,
    hindex.symm.trans ((reachable_root_iff hw _ _).trans (layeredDigraph_reachable_iff I))⟩

end CslibFrontierTests.STCONSubdivisionEndpoints
