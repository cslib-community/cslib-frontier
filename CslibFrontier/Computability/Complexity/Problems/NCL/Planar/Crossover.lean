/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.MixedCrossover
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Standard

/-!
# A planar AND/OR crossover for every color pair

Select the blue, red or mixed-color implementation of the crossing relation. Each replacement
preserves its four boundary wires by an open simulation. The largest drawing has 286 vertices
and 431 edges, constants independent of the circuit being planarized.

## Main definitions

* `Cslib.Complexity.NCL.Planar.Crossover.diagram`: a crossover for any pair of wire colors.
* `Cslib.Complexity.NCL.Planar.Crossover.openSim`: its certified open implementation.

## Main results

* `Cslib.Complexity.NCL.Planar.Crossover.planar`,
  `Cslib.Complexity.NCL.Planar.Crossover.andOr`,
  `Cslib.Complexity.NCL.Planar.Crossover.loopFree`,
  `Cslib.Complexity.NCL.Planar.Crossover.checkPorts`: replacement properties.
* `Cslib.Complexity.NCL.Planar.Crossover.length_vertexList_le`,
  `Cslib.Complexity.NCL.Planar.Crossover.card_edge_le`: uniform size bounds.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Crossover

open Diagram

/-- The planar AND/OR implementation for a pair of crossing wire colors. -/
@[expose] def diagram : (c d : Color) → Diagram Prim [c, d] [d, c]
  | .blue, .blue => BlueCrossover.diagram
  | .red, .red => RedCrossover.diagram
  | .red, .blue => MixedCrossover.redBlue
  | .blue, .red => MixedCrossover.blueRed

/-- Each drawing implements the corresponding two independent wire relations. -/
def openSim : (c d : Color) →
    OpenSim Prim.interp Prim.interp (gen (Prim.cross c d)) (diagram c d)
  | .blue, .blue => BlueCrossover.openSim
  | .red, .red => RedCrossover.openSim
  | .red, .blue => MixedCrossover.redBlueOpenSim
  | .blue, .red => MixedCrossover.blueRedOpenSim

/-- Every crossover drawing contains no swaps. -/
theorem planar (c d : Color) : (diagram c d).Planar := by
  cases c <;> cases d
  · exact RedCrossover.planar
  · exact MixedCrossover.redBlue_planar
  · exact MixedCrossover.blueRed_planar
  · exact BlueCrossover.planar

/-- Every crossover passes the three local standard-cell checks. -/
theorem checkStandard (c d : Color) : (diagram c d).checkGens Prim.checkStandard = true := by
  cases c <;> cases d <;> decide +kernel

/-- Every primitive cell of a crossover contains one vertex. -/
theorem checkSingle (c d : Color) :
    (diagram c d).checkGens (fun g => g.length == 1) = true := by
  cases c <;> cases d <;> decide +kernel

/-- Every crossover uses only AND/OR vertices. -/
theorem andOr (c d : Color) : ((diagram c d).graph Prim.interp).IsAndOr :=
  isAndOr_of_checkGens Prim.interp _ ((checkGens_checkStandard_iff _).1 (checkStandard c d)).1

/-- No crossover vertex repeats an edge. -/
theorem loopFree (c d : Color) : ((diagram c d).graph Prim.interp).LoopFree :=
  loopFree_of_checkGens Prim.interp _ ((checkGens_checkStandard_iff _).1 (checkStandard c d)).2.1

/-- Every crossover preserves its colored boundary incidences. -/
theorem checkPorts (c d : Color) : (diagram c d).checkGens Prim.interp.checkPorts = true :=
  ((checkGens_checkStandard_iff _).1 (checkStandard c d)).2.2

/-- Every crossover has at most 286 vertices. -/
theorem length_vertexList_le (c d : Color) :
    (vertexList Prim.interp (diagram c d)).length ≤ 286 := by
  cases c <;> cases d <;>
    simp only [diagram, RedCrossover.length_vertexList, MixedCrossover.redBlue_length_vertexList,
      MixedCrossover.blueRed_length_vertexList, BlueCrossover.length_vertexList] <;> omega

/-- Every crossover has at most 431 edges, including its boundary wires. -/
theorem card_edge_le (c d : Color) : Fintype.card (diagram c d).Edge ≤ 431 := by
  cases c <;> cases d
  · calc
      _ = Fintype.card RedCrossover.diagram.Edge := Fintype.card_congr (Equiv.refl _)
      _ ≤ 431 := by rw [RedCrossover.card_edge]; omega
  · calc
      _ = Fintype.card MixedCrossover.redBlue.Edge := Fintype.card_congr (Equiv.refl _)
      _ ≤ 431 := by rw [MixedCrossover.redBlue_card_edge]
  · calc
      _ = Fintype.card MixedCrossover.blueRed.Edge := Fintype.card_congr (Equiv.refl _)
      _ ≤ 431 := by rw [MixedCrossover.blueRed_card_edge]
  · calc
      _ = Fintype.card BlueCrossover.diagram.Edge := Fintype.card_congr (Equiv.refl _)
      _ ≤ 431 := by rw [BlueCrossover.card_edge]; omega

/-- A crossover creates at most 429 wires beyond its two incoming wires. -/
theorem innerCount_le (c d : Color) : (diagram c d).innerCount ≤ 429 := by
  have hc := card_edge_le c d
  have he : Fintype.card (diagram c d).Edge = 2 + (diagram c d).innerCount :=
    (Fintype.card_congr (diagram c d).numEquiv).trans (Fintype.card_fin _)
  omega

end Cslib.Complexity.NCL.Planar.Crossover
