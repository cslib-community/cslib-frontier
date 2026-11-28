/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Origin
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CrossingRows
import Mathlib.Data.Fintype.Fin

/-!
# Row ownership for canonical incidence crossings

Assign each actual crossing the smaller owner row of its two original wire labels. The
canonical incidence permutation inherits the constant row budget of its labeled swaps.

## Main results

* `Planar.Embedding.crossingRow_card_le`: at most `4 * B²` crossings belong to one row.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding
open Diagram
variable {m : ℕ}

/-- The owner row of a syntactic crossing in the actual canonical incidence routing. -/
@[expose] def crossingRow (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (ownerRow : Port (Fin m) → ℕ)
    (i : Fin (swapCount (routing vs color hw).diagram)) : ℕ :=
  let pair := ((routing vs color hw).diagram.crossingPairs (routing vs color hw).labeling.label).get
    (i.cast (length_crossingPairs _ _).symm)
  min (ownerRow pair.1) (ownerRow pair.2)

private theorem crossingRow_ofFn (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (ownerRow : Port (Fin m) → ℕ) :
    List.ofFn (crossingRow vs color hw ownerRow) =
      ((routing vs color hw).diagram.crossingPairs (routing vs color hw).labeling.label).map
        (fun pair => min (ownerRow pair.1) (ownerRow pair.2)) := by
  let pairs := (routing vs color hw).diagram.crossingPairs (routing vs color hw).labeling.label
  let row := fun pair : Port (Fin m) × Port (Fin m) => min (ownerRow pair.1) (ownerRow pair.2)
  have hlen : pairs.length = swapCount (routing vs color hw).diagram := length_crossingPairs _ _
  change List.ofFn (fun i => row (pairs.get (i.cast hlen.symm))) = pairs.map row
  exact (List.ofFn_congr hlen (fun i => row (pairs.get i))).symm.trans
    ((List.ofFn_comp' pairs.get row).trans (congrArg (List.map row) (List.ofFn_get pairs)))

/-- The actual incidence routing has a constant number of crossing indices at each owner row. -/
theorem crossingRow_card_le (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (srcRow ownerRow : Port (Fin m) → ℕ)
    (hxs : (Sources.vertexLabels vs).Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : (Sinks.pairLabels (List.finRange m)).Pairwise (fun a b => ownerRow a ≤ ownerRow b))
    (hrow : ∀ a ∈ Sources.vertexLabels vs,
      ownerRow a ≤ srcRow a ∧ srcRow a ≤ ownerRow a + 1)
    (B : ℕ) (hb : ∀ r, ((Sources.vertexLabels vs).filter (fun a => ownerRow a == r)).length ≤ B)
    (r : ℕ) :
    Fintype.card {i // crossingRow vs color hw ownerRow i = r} ≤ 4 * B ^ 2 := by
  rw [Fintype.card_subtype, ← List.count_ofFn, crossingRow_ofFn, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  unfold routing
  rw [Wiring.crossingPairs_cast]
  exact crossingPairs_reorder_row_le (fun p => color p.edge) _ _ (incidencePerm vs hw)
    (vertexLabels_nodup vs hw) srcRow ownerRow hxs hys hrow B hb r

/-- Assign each actual output vertex to its source, cap, or crossing owner row. -/
@[expose] def planeVertexRow (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (srcRow : Fin vs.length → ℕ) (ownerRow : Fin m → ℕ)
    (v : (planeDiagram vs hw).Vtx Prim.interp) : ℕ :=
  match planeVertexOrigin vs hw v with
  | .vertex i => srcRow i
  | .cap e => ownerRow e
  | .crossing i => crossingRow vs (color vs) hw (fun p => ownerRow p.edge) i

end Cslib.Complexity.NCL.Planar.Embedding
