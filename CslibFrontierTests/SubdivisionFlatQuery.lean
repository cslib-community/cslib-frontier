/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.FlatQuery

/-! Ordinary-import clients for the native flat subdivision-ID adapter. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SubdivisionFlatQuery

open Cslib Turing.QueryMachine.Subdivision Turing.MultiTapeTM
open Cslib.LayeredDigraph.Subdivision

-- The two IDs differ in their chain positions but decode to the same original label.
example : decodeFlatQuery ⟨true, 3, 8, 11⟩ = ⟨true, 2, 2, 0, 3⟩ := rfl

example : ComputableInSpace (fun p : ℕ × ℕ => rootID p.1 p.2) (encPair encNat encNat) encNat
    (fun p => (encPair encNat encNat p).length) :=
  rootID_inSpace

example : ComputableInSpace decodeFlatQuery (encFlatQuery encBool) (encQuery encBool)
    (fun q => (encFlatQuery encBool q).length) :=
  decodeFlatQuery_inSpace encBool

private def label (n : ℕ) : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

-- Start at an original root and query any slot through the existing adjacency kernel.
example {n : ℕ} (G : LayeredDigraph (Fin n)) (weight : Fin n → ℕ) (bound : ℕ)
    (a : Fin n) (b : Vertex (Fin n) bound) (baseEdge : Bool)
    (hbase : baseEdge = true ↔ G.Adj a b.vertex) :
    edgeQuery (decodeFlatQuery ⟨false, bound, rootID a.val bound, (flatIndex n bound b).val⟩)
      (weight a) baseEdge = true ↔ (graph G weight bound).Adj (root bound a) b := by
  rw [rootID_eq_flatIndex a bound, decodeFlatQuery_flatIndex]
  exact edgeQuery_agrees G (label n) weight bound false (root bound a) b baseEdge hbase

end CslibFrontierTests.SubdivisionFlatQuery
