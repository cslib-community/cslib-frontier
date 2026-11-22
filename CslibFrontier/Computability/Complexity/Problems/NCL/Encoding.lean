/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Bit encodings of NCL instances

Encode ports, vertices, and graph data with the existing framed pair, list, natural-number,
and Boolean encodings. Constructors and projections preserve polynomial-time computability.

## Main definitions

* `Cslib.Complexity.NCL.encPort`, `Cslib.Complexity.NCL.encVertex`: structural bit encodings.
* `Cslib.Complexity.NCL.encAndOrGraph`: vertex data and edge count.
* `Cslib.Complexity.NCL.encAndOrNCL`, `Cslib.Complexity.NCL.encAndOrNCLEdge`,
  `Cslib.Complexity.NCL.encAndOrNCLEdgeToEdge`: the three instance encodings.

## Main results

* `Cslib.Complexity.NCL.AndOrGraph.computableInPolyTime_checkVertices` recognizes the vertex
  shapes in polynomial time.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

variable {E : Type}

/-- Encode the framed edge name followed by its direction bit. -/
enc_structure encPort (encE : E ↪ List Bool) : Port E where
  edge : encE, dir : encBool

/-- Encode a weighted incidence by framing its port and appending its binary weight. -/
enc_structure encWeightedPort (encE : E ↪ List Bool) : WeightedPort E where
  port : (encPort encE), weight : encNat

/-- Encode the list of weighted incidences by framing each encoded incidence. -/
abbrev encWeightedPorts (encE : E ↪ List Bool) : List (WeightedPort E) ↪ List Bool :=
  encList (encWeightedPort encE)

/-- Encode the framed list of weighted ports followed by the binary minimum inflow. -/
enc_structure encVertex (encE : E ↪ List Bool) : Vertex E where
  ports : (encWeightedPorts encE), minInflow : encNat

/-- Encode explicit graph data using binary edge names and edge count. -/
enc_structure encAndOrGraph : AndOrGraph where
  vertices : (encList (encVertex encNat)), edgeCount : encNat

/-- Encode a graph and its initial and target bit lists. -/
enc_structure encAndOrNCL : AndOrNCL.Instance where
  graph : encAndOrGraph, initial : (encList encBool), target : (encList encBool)

/-- Encode a graph, its initial bit list, and a target edge number. -/
enc_structure encAndOrNCLEdge : AndOrNCLEdge.Instance where
  graph : encAndOrGraph, initial : (encList encBool), edge : encNat

/-- Encode a graph and two edge numbers with their prescribed directions. -/
enc_structure encAndOrNCLEdgeToEdge : AndOrNCLEdgeToEdge.Instance where
  graph : encAndOrGraph, first : (encPort encNat), second : (encPort encNat)

/-- Checking the declared bounds of every port is polynomial-time on explicit graph data. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkBounded :
    ComputableInPolyTime AndOrGraph.checkBounded encAndOrGraph encBool := by
  unfold AndOrGraph.checkBounded
  fun_prop

/-- AND/OR vertex recognition is polynomial-time in the structural vertex encoding. -/
@[fun_prop]
theorem Vertex.computableInPolyTime_checkAndOr (encE : E ↪ List Bool) :
    ComputableInPolyTime Vertex.checkAndOr (encVertex encE) encBool := by
  have hw : ComputableInPolyTime (fun v : Vertex E => v.ports.map WeightedPort.weight)
      (encVertex encE) (encList encNat) := by fun_prop
  unfold Vertex.checkAndOr
  simp only [List.contains_eq_any_beq, List.any_cons, List.any_nil, Bool.or_false]
  fun_prop

/-- The AND/OR checks on all vertex records run in polynomial time. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkVertices :
    ComputableInPolyTime AndOrGraph.checkVertices encAndOrGraph encBool := by
  unfold AndOrGraph.checkVertices
  fun_prop

end Cslib.Complexity.NCL
