/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Geometric
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal

/-!
# Standard continuous drawings of compiled plane words

The complete grid drawing of the exact compiled graph supplies a simple continuous planar
orthogonal drawing in the standard finite incidence-graph format. The listed vertices and edge
occurrences keep the original finite numbering; `Closed.incidenceGraph_incident_iff` identifies
every endpoint with the corresponding original port incidence.

## Main results

* `Word.planarOrthogonalDrawing_compile`: a standard continuous drawing of every closed
  well-typed plane word's compiled graph.
-/

public section

namespace Cslib.Complexity.NCL

/-- The exact compiled graph has a standard continuous planar orthogonal drawing, with one
listed incidence edge for each original edge in its finite numbering. -/
theorem Word.planarOrthogonalDrawing_compile {w : Word} (hP : w.checkPlane = true)
    (hT : w.WellTyped [] []) :
    ∃ D : GridDrawing.Closed w.compile.graph,
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing D.incidenceGraph D.orthogonalDrawing := by
  obtain ⟨D⟩ := Word.orthogonalDrawing_compile hP hT
  exact ⟨D, D.isPlanarOrthogonalDrawing⟩

end Cslib.Complexity.NCL
