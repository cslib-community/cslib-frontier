/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Incidence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time recognition of valid NCL graph data

All scans range over the explicit port records. Binary edge counts are compared with the port
list length, and incidence checking uses a unary list-length bound for its range.

## Main results

* `Cslib.Complexity.NCL.AndOrGraph.computableInPolyTime_checkValid`: validity of graph data is
  decidable in polynomial time in the instance encoding.

## References

* The instance conditions are those of [Hearn and Demaine][HearnDemaine2005, Section 2].
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph

open _root_.Turing.MultiTapeTM

/-- Checking the opposite weighted pair at a computed edge is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_checkEdge {α : Type} {input : α ↪ List Bool}
    {ps : α → List (WeightedPort ℕ)} {edge : α → ℕ}
    (hp : ComputableInPolyTime ps input (encWeightedPorts encNat))
    (he : ComputableInPolyTime edge input encNat) :
    ComputableInPolyTime (fun x => checkEdge (ps x) (edge x)) input encBool := by
  have hq : ComputableInPolyTime
      (fun x => (ps x).filter (fun p => decide (p.port.edge = edge x)))
      input (encWeightedPorts encNat) := by
    fun_prop
  unfold checkEdge
  fun_prop

private theorem computableInPolyTime_portList :
    ComputableInPolyTime (fun g : AndOrGraph => g.vertices.flatMap Vertex.ports)
      encAndOrGraph (encWeightedPorts encNat) := by
  fun_prop

private theorem computableInPolyTime_index :
    ComputableInPolyTime (fun p : AndOrGraph × ℕ =>
      if p.2 < p.1.edgeCount then checkEdge (p.1.vertices.flatMap Vertex.ports) p.2 else true)
      (encPair encAndOrGraph encUnary) encBool := by
  have hi' : ComputableInPolyTime (fun p : AndOrGraph × ℕ => p.2)
      (encPair encAndOrGraph encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hg : ComputableInPolyTime (fun p : AndOrGraph × ℕ => p.1)
      (encPair encAndOrGraph encUnary) encAndOrGraph := by fun_prop
  have he := computableInPolyTime_checkEdge (computableInPolyTime_portList.comp hg) hi'
  have hc : ComputableInPolyTime (fun p : AndOrGraph × ℕ => decide (p.2 < p.1.edgeCount))
      (encPair encAndOrGraph encUnary) encBool := by fun_prop
  fun_prop

/-- The complete incidence scan is polynomial-time in explicit graph data. -/
@[fun_prop]
theorem computableInPolyTime_checkIncidences :
    ComputableInPolyTime checkIncidences encAndOrGraph encBool := by
  have hp := computableInPolyTime_portList
  have hn : ComputableInPolyTime (fun g : AndOrGraph => (g.vertices.flatMap Vertex.ports).length)
      encAndOrGraph encUnary := by fun_prop
  have hn' := ComputableInPolyTime.unary_to_binary.comp hn
  unfold checkIncidences
  exact ComputableInPolyTime.bool_and' (by fun_prop)
    (ComputableInPolyTime.allWithEncoding computableInPolyTime_index (by fun_prop) (by fun_prop))

/-- Every structural condition defining a valid AND/OR graph is polynomial-time decidable. -/
@[fun_prop]
theorem computableInPolyTime_checkValid :
    ComputableInPolyTime checkValid encAndOrGraph encBool := by
  unfold checkValid
  fun_prop

end Cslib.Complexity.NCL.AndOrGraph
