/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Size
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Origin

/-!
# Origins of canonical planarization vertices

Every new vertex belongs to an original vertex, an original edge's cap, or a crossing of the
canonical incidence permutation. Source indices retain the original vertex order; cap labels
retain the original edge numbers; crossing indices use syntax order.

## Main definitions

* `Planar.Embedding.VertexOrigin`: the three origins of a canonical planarization vertex.
* `Planar.Embedding.planeVertexOrigin`: classify every vertex of the actual output diagram.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

/-- The original local piece responsible for a vertex of the canonical planarization. -/
inductive VertexOrigin (vertices edges crossings : ℕ)
  /-- The original vertex with this index. -/
  | vertex (index : Fin vertices)
  /-- The cap joining this original edge's two incidences. -/
  | cap (edge : Fin edges)
  /-- The crossover replacing this syntactic swap in the incidence routing. -/
  | crossing (index : Fin crossings)
  deriving @[expose] DecidableEq

/-- Reindex the original vertices while retaining edge and crossing labels. -/
@[expose] def VertexOrigin.mapVertices {n n' m k : ℕ} (f : Fin n → Fin n') :
    VertexOrigin n m k → VertexOrigin n' m k
  | .vertex i => .vertex (f i)
  | .cap e => .cap e
  | .crossing i => .crossing i

/-- A vertex of a planarized source bundle retains its original list position. -/
@[expose] def sourceVertexOrigin {E : Type*} (c : Port E → Color) :
    (vs : List (Vertex E)) →
      (planarizeAlong Cell.expand (Sources.vertices c vs).diagram).Vtx Prim.interp → Fin vs.length
  | [] => fun v => v.elim
  | _ :: vs =>
    show (Fin 1 ⊕ (planarizeAlong Cell.expand (Sources.vertices c vs).diagram).Vtx Prim.interp) →
        Fin (vs.length + 1) from
      Sum.elim (fun _ => (0 : Fin (vs.length + 1))) (fun w => (sourceVertexOrigin c vs w).succ)

/-- A vertex of a planarized cap bundle retains the original edge label. -/
@[expose] def capVertexOrigin {E : Type*} (c : E → Color) : (es : List E) →
    (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp → E
  | [] => fun v => v.elim
  | e :: es =>
    show ((Gadgets.Wire.cap (c e)).Vtx Prim.interp ⊕
        (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp) → E from
      Sum.elim (fun _ => e) (capVertexOrigin c es)

/-- Classify each output vertex by its original source vertex, edge cap, or routing crossing. -/
@[expose] def planeVertexOrigin {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (planeDiagram vs hw).Vtx Prim.interp →
      VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram) :=
  show ((planarizeAlong Cell.expand (sourceBundle vs (color vs)).diagram).Vtx Prim.interp ⊕
      ((planarizeAlong Cell.expand (routing vs (color vs) hw).diagram).Vtx Prim.interp ⊕
        (planarizeAlong Cell.expand (sinkBundle (color vs)).diagram).Vtx Prim.interp)) →
      VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram) from
    Sum.elim
      (fun v => .vertex (sourceVertexOrigin (fun p => color vs p.edge) vs v))
      (Sum.elim
        (fun v => .crossing (crossingOrigin Cell.expand _ (routing vs (color vs) hw).noGens v))
        (fun v => .cap (capVertexOrigin (color vs) (List.finRange m) v)))

end Cslib.Complexity.NCL.Planar.Embedding
