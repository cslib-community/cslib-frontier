/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance

/-!
# AND/OR NCL decision problems

The three questions use explicit finite AND/OR multigraphs with loops and parallel edges.
Configuration inputs contain one bit per edge, and their initial configuration must be legal.
Edge-to-edge reachability quantifies a legal start with the first prescribed direction and
a reachable end with the second.

## Main definitions

* `Cslib.Complexity.NCL.AndOrNCL`: configuration-to-configuration reachability.
* `Cslib.Complexity.NCL.AndOrNCLEdge`: configuration-to-edge reachability.
* `Cslib.Complexity.NCL.AndOrNCLEdgeToEdge`: directional edge-to-edge reachability.

## References

* The AND/OR instances of the three problems defined in
  [Hearn and Demaine][HearnDemaine2005, Sections 2.1–2.2 and footnote 2].
-/

public section

namespace Cslib.Complexity.NCL

/-- An explicit graph with initial and target configuration lists. -/
structure AndOrNCL.Instance where
  /-- The finite graph data. -/
  graph : AndOrGraph
  /-- The initial orientation bits. -/
  initial : List Bool
  /-- The target orientation bits. -/
  target : List Bool

/-- An explicit graph with an initial configuration and an edge to reverse. -/
structure AndOrNCLEdge.Instance where
  /-- The finite graph data. -/
  graph : AndOrGraph
  /-- The initial orientation bits. -/
  initial : List Bool
  /-- The edge to reverse. -/
  edge : ℕ

/-- An explicit graph with two prescribed edge directions. -/
structure AndOrNCLEdgeToEdge.Instance where
  /-- The finite graph data. -/
  graph : AndOrGraph
  /-- The prescribed direction in the starting configuration. -/
  first : Port ℕ
  /-- The prescribed direction in the reachable configuration. -/
  second : Port ℕ

/-- A valid AND/OR graph with a legal initial bit list can reach the given target bit list. -/
@[expose] def AndOrNCL : Set AndOrNCL.Instance := {x |
  x.graph.Valid ∧ x.initial.length = x.graph.edgeCount ∧ x.target.length = x.graph.edgeCount ∧
    x.graph.graph.Legal (x.graph.config x.initial) ∧
      x.graph.graph.Reachable (x.graph.config x.initial) (x.graph.config x.target)}

/-- A valid AND/OR graph with a legal initial bit list can eventually reverse the named edge. -/
@[expose] def AndOrNCLEdge : Set AndOrNCLEdge.Instance := {x |
  ∃ he : x.edge < x.graph.edgeCount, x.graph.Valid ∧ x.initial.length = x.graph.edgeCount ∧
    x.graph.graph.Legal (x.graph.config x.initial) ∧
      x.graph.graph.CanReverse (x.graph.config x.initial) ⟨x.edge, he⟩}

/-- In a valid AND/OR graph, some legal start with the first prescribed edge direction reaches
an end with the second prescribed edge direction. -/
@[expose] def AndOrNCLEdgeToEdge : Set AndOrNCLEdgeToEdge.Instance := {x |
  ∃ hA : x.first.edge < x.graph.edgeCount, ∃ hB : x.second.edge < x.graph.edgeCount, x.graph.Valid ∧
    ∃ s t, x.graph.graph.Legal s ∧ s ⟨x.first.edge, hA⟩ = x.first.dir ∧
      t ⟨x.second.edge, hB⟩ = x.second.dir ∧ x.graph.graph.Reachable s t}

end Cslib.Complexity.NCL
