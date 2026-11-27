/-
Copyright (c) 2026 Samuel Schlesinger, Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Graph

/-!
# Reachability in planar AND/OR multigraphs

The three problems take explicit AND/OR graph data under the general graph encodings. Planarity
means existence of a continuous polygonal embedding of the incidence multigraph. Self-loops and
parallel edges are admitted, as in [HearnDemaine2005, Section 2.2, footnote 2].

## Main definitions

* `PlanarAndOrNCL` asks configuration-to-configuration reachability on planar graphs.
* `PlanarAndOrNCLEdge` asks configuration-to-edge reachability on planar graphs.
* `PlanarAndOrNCLEdgeToEdge` asks directional edge-to-edge reachability on planar graphs.

## References

* [Hearn and Demaine][HearnDemaine2005, Sections 2.1–2.2 and Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

/-- Fixed-target AND/OR multigraph reachability with a planar underlying graph. -/
@[expose] def PlanarAndOrNCL : Set AndOrNCL.Instance :=
  {x | x ∈ AndOrNCL ∧ x.graph.IsPlanar}

/-- Configuration-to-edge AND/OR multigraph reachability with a planar underlying graph. -/
@[expose] def PlanarAndOrNCLEdge : Set AndOrNCLEdge.Instance :=
  {x | x ∈ AndOrNCLEdge ∧ x.graph.IsPlanar}

/-- Directional edge-to-edge AND/OR multigraph reachability with a planar underlying graph. -/
@[expose] def PlanarAndOrNCLEdgeToEdge : Set AndOrNCLEdgeToEdge.Instance :=
  {x | x ∈ AndOrNCLEdgeToEdge ∧ x.graph.IsPlanar}

end Cslib.Complexity.NCL
