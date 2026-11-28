/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.RedCrossover

import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Pad

/-!
# Crossovers of different colors

Convert the blue wire to red, cross its two red continuations with the other red wire, and
convert it back to blue [HearnDemaine2005, Section 3.2]. The two red crossovers also route the
extra free red continuation to the final converter. Both input orders admit a progressive
planar drawing, with 286 AND/OR vertices.

The abstract frames contain only wire relations. Canonical internal directions copy the
corresponding bottom port; changing a bottom port reverses its one or two internal segments.
Unit propagation refutes every forbidden boundary. The checked frames then compose with the
converters and red crossovers.

## Main definitions

* `Cslib.Complexity.NCL.Planar.MixedCrossover.redBlue`,
  `Cslib.Complexity.NCL.Planar.MixedCrossover.blueRed`: the two mixed-color crossings.

## Main results

* `Cslib.Complexity.NCL.Planar.MixedCrossover.redBlueOpenSim`,
  `Cslib.Complexity.NCL.Planar.MixedCrossover.blueRedOpenSim`: their open simulations.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.MixedCrossover

open Diagram Gadgets
local notation "R" => Color.red
local notation "B" => Color.blue

/-- Red-blue layout with supplied converters and a red crossing cell. -/
@[expose] def redBlueNetwork (start : Diagram Prim [B] [R, R])
    (crossing : Diagram Prim [R, R] [R, R]) (finish : Diagram Prim [R, R] [B]) :
    Diagram Prim [R, B] [B, R] :=
  (pad [R] start []).comp <|
  (pad [] crossing [R]).comp <|
  (pad [R] crossing []).comp
  (pad [] finish [R])

/-- Blue-red layout with supplied converters and a red crossing cell. -/
@[expose] def blueRedNetwork (start : Diagram Prim [B] [R, R])
    (crossing : Diagram Prim [R, R] [R, R]) (finish : Diagram Prim [R, R] [B]) :
    Diagram Prim [B, R] [R, B] :=
  (pad [] start [R]).comp <|
  (pad [R] crossing []).comp <|
  (pad [] crossing [R]).comp
  (pad [R] finish [])

/-- The red-blue frame before expanding wire relations. -/
@[expose] def redBlueFrame : Diagram Prim [R, B] [B, R] :=
  redBlueNetwork (gen Conv.blueToRedRedGenerator) (gen (Prim.cross R R))
    (gen Conv.redRedToBlueGenerator)

/-- The blue-red frame before expanding wire relations. -/
@[expose] def blueRedFrame : Diagram Prim [B, R] [R, B] :=
  blueRedNetwork (gen Conv.blueToRedRedGenerator) (gen (Prim.cross R R))
    (gen Conv.redRedToBlueGenerator)

/-- A red wire crosses a blue wire. -/
@[expose] def redBlue : Diagram Prim [R, B] [B, R] :=
  redBlueNetwork vnoc RedCrossover.diagram Conv.redRedToBlue

/-- A blue wire crosses a red wire. -/
@[expose] def blueRed : Diagram Prim [B, R] [R, B] :=
  blueRedNetwork vnoc RedCrossover.diagram Conv.redRedToBlue

end Cslib.Complexity.NCL.Planar.MixedCrossover

end

public section

namespace Cslib.Complexity.NCL.Planar.MixedCrossover

open Diagram Gadgets
local notation "R" => Color.red
local notation "B" => Color.blue

private def cert {c d : Color} (D : Diagram Prim [c, d] [d, c])
    (paths : Fin 2 → List D.Edge) : Cert (Prim.cross c d) D where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else if y = D.bottom 0 then β (.inr 0) else if y = D.bottom 1 then β (.inr 1)
    else (paths 0).contains y && β (.inr 0) || (paths 1).contains y && β (.inr 1)
  rounds := 2
  refute _ := .conflict
  pre β x := Sum.elim (fun _ => []) (fun i => if β (.inr i) then [] else paths i) x
  post β x := Sum.elim (fun _ => []) (fun i => if β (.inr i) then (paths i).reverse else []) x

private def redBlueCert : Cert (Prim.cross R B) redBlueFrame :=
  cert redBlueFrame fun i =>
    ((if i = 0 then [2, 4] else [5]) : List (Fin 9)).map redBlueFrame.numEquiv.symm

private def blueRedCert : Cert (Prim.cross B R) blueRedFrame :=
  cert blueRedFrame fun i =>
    ((if i = 0 then [4] else [2, 7]) : List (Fin 9)).map blueRedFrame.numEquiv.symm

private def redBlueExpansion : OpenSim Prim.interp Prim.interp redBlueFrame redBlue :=
  (OpenSim.pad [R] [] Conv.blueToRedRedOpenSim).comp <|
  (OpenSim.pad [] [R] RedCrossover.openSim).comp <|
  (OpenSim.pad [R] [] RedCrossover.openSim).comp
  (OpenSim.pad [] [R] Conv.redRedToBlueOpenSim)

private def blueRedExpansion : OpenSim Prim.interp Prim.interp blueRedFrame blueRed :=
  (OpenSim.pad [] [R] Conv.blueToRedRedOpenSim).comp <|
  (OpenSim.pad [R] [] RedCrossover.openSim).comp <|
  (OpenSim.pad [] [R] RedCrossover.openSim).comp
  (OpenSim.pad [R] [] Conv.redRedToBlueOpenSim)

/-- The red-blue drawing implements independent crossing wires. -/
def redBlueOpenSim : OpenSim Prim.interp Prim.interp (gen (Prim.cross R B)) redBlue :=
  (OpenSim.ofCert redBlueCert (by decide +kernel)).trans redBlueExpansion

/-- The blue-red drawing implements independent crossing wires. -/
def blueRedOpenSim : OpenSim Prim.interp Prim.interp (gen (Prim.cross B R)) blueRed :=
  (OpenSim.ofCert blueRedCert (by decide +kernel)).trans blueRedExpansion

/-- The red-blue drawing contains no swaps. -/
theorem redBlue_planar : redBlue.Planar := by decide +kernel

/-- The blue-red drawing contains no swaps. -/
theorem blueRed_planar : blueRed.Planar := by decide +kernel

/-- The red-blue drawing has 286 vertices. -/
theorem redBlue_length_vertexList : (vertexList Prim.interp redBlue).length = 286 := by
  decide +kernel

/-- The blue-red drawing has 286 vertices. -/
theorem blueRed_length_vertexList : (vertexList Prim.interp blueRed).length = 286 := by
  decide +kernel

/-- The red-blue drawing has 431 edges, including its boundary wires. -/
theorem redBlue_card_edge : Fintype.card redBlue.Edge = 431 := by
  exact (Fintype.card_congr redBlue.numEquiv).trans (Fintype.card_fin _)

/-- The blue-red drawing has 431 edges, including its boundary wires. -/
theorem blueRed_card_edge : Fintype.card blueRed.Edge = 431 := by
  exact (Fintype.card_congr blueRed.numEquiv).trans (Fintype.card_fin _)

end Cslib.Complexity.NCL.Planar.MixedCrossover
