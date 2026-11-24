/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity

/-!
# Crossing counts of regular polygonal drawings

`EvenCrossings` records the parity condition on independent edges and on pairs of distinct
edges incident with a designated vertex.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Cslib.Polygonal

/-- Independent edge pairs and pairs incident with a marked vertex have even indexed
open-segment crossing parity. Edges and their incidences are distinguished by list position. -/
@[expose] def EvenCrossings {G : Graph} (D : PolygonalDrawing G) (marked : ℕ → Prop) : Prop :=
  ∀ e f : Fin G.edges.length, e ≠ f →
    ((∀ b c : Bool, Dart.vertex (e, b) ≠ Dart.vertex (f, c)) ∨
      ∃ b c : Bool, Dart.vertex (e, b) = Dart.vertex (f, c) ∧ marked (Dart.vertex (e, b))) →
    (D.route e).intersectionParity (D.route f) = false

end Cslib.Complexity.Graph.PolygonalDrawing
