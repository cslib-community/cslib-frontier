/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.BlueCrossover

/-!
# The red crossover

Four conversions surround the blue crossover, with their free red wires joined along the two
sides [HearnDemaine2005, Section 3.2]. The conversion frame has one internal reversal for each
allowed boundary move. Composing its certificate with the blue crossover gives a planar AND/OR
implementation of two independent crossing red wires, with 138 vertices.

## Main definitions

* `Cslib.Complexity.NCL.Planar.RedCrossover.diagram`: the red crossover.

## Main results

* `Cslib.Complexity.NCL.Planar.RedCrossover.openSim`: the crossing implementation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.RedCrossover

open Diagram Gadgets

/-- The red crossover, with conversion free ends paired along its sides. -/
@[expose]
def diagram : Diagram Prim [.red, .red] [.red, .red] := Conv.surround BlueCrossover.diagram

end Cslib.Complexity.NCL.Planar.RedCrossover

end

public section

namespace Cslib.Complexity.NCL.Planar.RedCrossover

open Diagram Gadgets

/-- The red crossover implements two independent crossing red wires. -/
def openSim : OpenSim Prim.interp Prim.interp (gen (Prim.cross .red .red)) diagram :=
  (OpenSim.ofCert (Conv.frameCert (Prim.cross .red .red) (Prim.cross .blue .blue))
    (by decide +kernel)).trans (Conv.surroundOpenSim BlueCrossover.openSim)

/-- The expanded crossover contains no swaps. -/
theorem planar : diagram.Planar := by decide +kernel

/-- The expanded gadget has 138 vertices. -/
theorem length_vertexList : (vertexList Prim.interp diagram).length = 138 := by decide +kernel

/-- The expanded gadget has 209 edges, including its four boundary wires. -/
theorem card_edge : Fintype.card diagram.Edge = 209 := by
  exact (Fintype.card_congr diagram.numEquiv).trans (Fintype.card_fin _)

end Cslib.Complexity.NCL.Planar.RedCrossover
