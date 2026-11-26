/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.RowLabels
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.OriginCount
import Mathlib.Tactic.Ring

/-!
# Row capacity of the actual planarization

Each row receives original source vertices, bounded cap gadgets, and bounded crossover gadgets.

## Main definitions

* `Planar.Embedding.rowBudget`: source, cap, and crossing contributions to one row.

## Main results

* `Planar.Embedding.planeVertexRow_card_le`: the actual output respects the row budget.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding
open Diagram

/-- Vertex capacity contributed by source vertices, edge caps, and actual wire crossings. -/
@[expose] def rowBudget (sources edges labels : ℕ) : ℕ := sources + 16 * edges + 1144 * labels ^ 2

section Layout
variable {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (vertexRow : Fin vs.length → ℕ) (srcRow : Port (Fin m) → ℕ) (ownerRow : Fin m → ℕ)
    (hxs : (Sources.vertexLabels vs).Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : (Sinks.pairLabels (List.finRange m)).Pairwise
      (fun a b => ownerRow a.edge ≤ ownerRow b.edge))
    (hrow : ∀ a ∈ Sources.vertexLabels vs,
      ownerRow a.edge ≤ srcRow a ∧ srcRow a ≤ ownerRow a.edge + 1)
    (A E B : ℕ) (hA : ∀ r, Nat.card {i // vertexRow i = r} ≤ A)
    (hE : ∀ r, Nat.card {e // ownerRow e = r} ≤ E)
    (hB : ∀ r, ((Sources.vertexLabels vs).filter (fun a => ownerRow a.edge == r)).length ≤ B)

include hxs hys hrow hA hE hB in
/-- The actual planarized vertex rows have a uniform capacity determined by the source data. -/
theorem planeVertexRow_card_le (r : ℕ) :
    Nat.card {v : (planeDiagram vs hw).Vtx Prim.interp //
      planeVertexRow vs hw vertexRow ownerRow v = r} ≤ rowBudget A E B := by
  let row : VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram) → ℕ
    | .vertex i => vertexRow i
    | .cap e => ownerRow e
    | .crossing i => crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i
  have h := planeVertexOrigin_row_fiber_le vs hw row r
  have hx : Nat.card {i // crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i = r} ≤
      4 * B ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      crossingRow_card_le vs (color vs) hw srcRow (fun p => ownerRow p.edge) hxs hys hrow B hB r
  calc
    _ ≤ _ := h
    _ ≤ A + 16 * E + 286 * (4 * B ^ 2) :=
      Nat.add_le_add (Nat.add_le_add (hA r) (Nat.mul_le_mul_left 16 (hE r)))
        (Nat.mul_le_mul_left 286 hx)
    _ = rowBudget A E B := by unfold rowBudget; ring

end Layout
end Cslib.Complexity.NCL.Planar.Embedding
