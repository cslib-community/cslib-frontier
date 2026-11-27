/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.HalfCrossover.Core
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.ConvDrawings
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CheckGens
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Incidence
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# The half-crossover

Four red-blue conversions surround the blue core of [HearnDemaine2005, Figure 8(b)]. The extra
red wires join `C` to `B` on the left and `A` to `D` on the right. The resulting planar AND/OR
diagram implements a four-red-port vertex that requires at least two edges inward.

The proof composes the core simulation with four conversion simulations. A small intermediate
frame contains abstract conversions and the blue threshold vertex; its certificates have one
internal reversal per boundary move. Each conversion has a fixed internal extension.

## Main definitions

* `Cslib.Complexity.NCL.Planar.HalfCrossover.diagram`: the complete half-crossover.
* `Cslib.Complexity.NCL.Planar.HalfCrossover.vertex`: its four-red-port interface.

## Main results

* `Cslib.Complexity.NCL.Planar.HalfCrossover.openSim`: the open simulation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.HalfCrossover

open Diagram Gadgets
local notation "R" => Color.red
local notation "B" => Color.blue

/-- The four-red-port threshold vertex with minimum inflow two. -/
@[expose] def vertex : Prim [R, R] [R, R] := [genVertex [R, R] [R, R] 2]

/-- The half-crossover: top `[C, A]`, bottom `[B, D]`, with free reds paired on each side. -/
@[expose] def diagram : Diagram Prim [R, R] [R, R] := Conv.surround Core.diagram

end Cslib.Complexity.NCL.Planar.HalfCrossover

end

public section

namespace Cslib.Complexity.NCL.Planar.HalfCrossover

open Diagram Gadgets
local notation "R" => Color.red
local notation "B" => Color.blue

/-- The half-crossover implements the four-red-port threshold vertex. -/
def openSim : OpenSim Prim.interp Prim.interp (gen vertex) diagram :=
  (OpenSim.ofCert (Conv.frameCert vertex Core.vertex) (by decide +kernel)).trans
    (Conv.surroundOpenSim Core.openSim)

/-- The drawing contains no swaps. -/
theorem planar : diagram.Planar := by decide +kernel

/-- The expanded gadget has 28 vertices. -/
theorem length_vertexList : (vertexList Prim.interp diagram).length = 28 := by decide +kernel

/-- The expanded gadget has 44 edges, including its four boundary wires. -/
theorem card_edge : Fintype.card diagram.Edge = 44 := by
  exact (Fintype.card_congr diagram.numEquiv).trans (Fintype.card_fin _)

end Cslib.Complexity.NCL.Planar.HalfCrossover
