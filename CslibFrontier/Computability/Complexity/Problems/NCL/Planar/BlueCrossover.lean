/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.HalfCrossover
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Interface
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Pad

/-!
# The blue crossover

The ten-vertex network of [HearnDemaine2005, Figure 8(a)] contains six AND vertices and four
four-red-port threshold vertices. All four threshold vertices use the same two-input,
two-output drawing, so their half-crossover implementations compose directly. The expanded
planar AND/OR diagram has 118 vertices.

Nine canonical boundary states, seven static refutations and twenty-four directed boundary
moves certify the abstract network. Refutations use two propagation rounds and at most one
split; each move uses at most ten internal reversals. The proof then composes four copies of
the certified half-crossover, without enumerating expanded configurations.

## Main definitions

* `Cslib.Complexity.NCL.Planar.BlueCrossover.network`: the network with a supplied four-port cell.
* `Cslib.Complexity.NCL.Planar.BlueCrossover.diagram`: the expanded blue crossover.

## Main results

* `Cslib.Complexity.NCL.Planar.BlueCrossover.openSim`: implementation of the crossing interface.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.BlueCrossover

open Diagram
local notation "R" => Color.red
local notation "B" => Color.blue

/-- The Figure 8(a) network with a supplied implementation of each four-red-port vertex. -/
@[expose] def network (half : Diagram Prim [R, R] [R, R]) : Diagram Prim [B, B] [B, B] :=
  let node (a b : List Color) : Diagram Prim a b := gen [genVertex a b 2]
  (pad [] (node [B] [R, R]) [B]).comp <|
  (pad [R, R] (node [B] [R, R]) []).comp <|
  (pad [R, R, R, R] (node [] [R, R, B]) []).comp <|
  (pad [R, R, R] half [R, B]).comp <|
  (pad [R, R, R, R] half [B]).comp <|
  (pad [R, R, R] (node [R, R] [B]) [R, B]).comp <|
  (pad [R] half [B, R, B]).comp <|
  (pad [] half [R, B, R, B]).comp <|
  (pad [R] (node [R, R, B] []) [R, B]).comp
  (pad [] (node [R, R] [B]) [B])

/-- The abstract Figure 8(a) network, before expanding its four degree-four vertices. -/
@[expose] def frame : Diagram Prim [B, B] [B, B] := network (gen HalfCrossover.vertex)

/-- The blue crossover with four expanded half-crossovers. -/
@[expose] def diagram : Diagram Prim [B, B] [B, B] := network HalfCrossover.diagram

end Cslib.Complexity.NCL.Planar.BlueCrossover

end

public section

namespace Cslib.Complexity.NCL.Planar.BlueCrossover

open Diagram
local notation "R" => Color.red
local notation "B" => Color.blue

private def innerBits : ℕ → List ℕ
  | 0 | 1 | 2 | 3 => [6, 7, 9, 11, 13]
  | 6 => [4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 16]
  | 7 => [2, 5, 6, 7, 9, 10, 11, 12, 13, 16]
  | 9 | 11 => [2, 3, 15, 17]
  | 15 => [2, 3, 4, 5, 10, 12, 14, 15, 16, 17]
  | _ => []

private def refute : ℕ → Refutation ℕ
  | 5 => (.split 9 .conflict .conflict)
  | 10 => (.split 9 .conflict .conflict)
  | _ => .conflict

private def forwardMoves : ℕ → ℕ → List (Fin 19) × List (Fin 19)
  | 1, 3 => ([2, 3, 15, 17, 13, 9, 6, 11, 7], [])
  | 2, 2 => ([4, 5, 10, 12, 14, 16], [])
  | 3, 2 => ([2, 5, 10, 12, 16], [])
  | 3, 3 => ([2, 3, 15, 17, 13, 9, 6, 11, 7], [])
  | 6, 0 => ([], [2, 14, 4])
  | 7, 3 => ([3, 4, 14, 15, 17, 13, 9, 6, 11, 7], [])
  | 11, 2 => ([4, 5, 10, 12, 14, 16], [])
  | _, _ => ([], [])

private def cert : Cert (Prim.cross B B) frame :=
  .ofTable { innerBits, rounds := 2, refute, forward := forwardMoves }

private theorem cert_valid : cert.Valid Prim.interp Prim.interp := by decide +kernel

private def frameSim : OpenSim Prim.interp Prim.interp (gen (Prim.cross B B)) frame :=
  OpenSim.ofCert cert cert_valid

private def frameExpansion : OpenSim Prim.interp Prim.interp frame diagram :=
  let node (a b : List Color) : Diagram Prim a b := gen [genVertex a b 2]
  (OpenSim.pad [] [B] (.refl (node [B] [R, R]))).comp <|
  (OpenSim.pad [R, R] [] (.refl (node [B] [R, R]))).comp <|
  (OpenSim.pad [R, R, R, R] [] (.refl (node [] [R, R, B]))).comp <|
  (OpenSim.pad [R, R, R] [R, B] HalfCrossover.openSim).comp <|
  (OpenSim.pad [R, R, R, R] [B] HalfCrossover.openSim).comp <|
  (OpenSim.pad [R, R, R] [R, B] (.refl (node [R, R] [B]))).comp <|
  (OpenSim.pad [R] [B, R, B] HalfCrossover.openSim).comp <|
  (OpenSim.pad [] [R, B, R, B] HalfCrossover.openSim).comp <|
  (OpenSim.pad [R] [R, B] (.refl (node [R, R, B] []))).comp
  (OpenSim.pad [] [B] (.refl (node [R, R] [B])))

/-- The planar blue crossover implements two independent crossing wires. -/
def openSim : OpenSim Prim.interp Prim.interp (gen (Prim.cross B B)) diagram :=
  frameSim.trans frameExpansion

/-- The expanded crossover contains no swaps. -/
theorem planar : diagram.Planar := by decide +kernel

/-- The expanded gadget has 118 vertices. -/
theorem length_vertexList : (vertexList Prim.interp diagram).length = 118 := by decide +kernel

/-- The expanded gadget has 179 edges, including its four boundary wires. -/
theorem card_edge : Fintype.card diagram.Edge = 179 := by
  exact (Fintype.card_congr diagram.numEquiv).trans (Fintype.card_fin _)

end Cslib.Complexity.NCL.Planar.BlueCrossover
