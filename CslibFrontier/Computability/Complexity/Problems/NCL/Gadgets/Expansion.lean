/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Vnoc
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Ends
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Generator
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Standard
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CheckGens
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Incidence

/-!
# Expanding circuit gates into primitive diagrams

Replace conversions, free ends, red caps and single-wire constraints by their checked gadgets.
Ordinary threshold vertices retain their vertex data. Open substitution composes these local
simulations, so the resulting primitive diagram preserves all three reachability questions of
the source circuit [HearnDemaine2005, Section 3.1].

## Main definitions

* `Cslib.Complexity.NCL.Gate.expand`: the replacement of a circuit generator.
* `Cslib.Complexity.NCL.Gate.expandSimulation`: the simulation of a whole circuit by its
  primitive expansion.

## Main results

* `Cslib.Complexity.NCL.Gate.expandOpenSim`: every replacement is an open simulation.
* `Cslib.Complexity.NCL.Gate.expand_isAndOr_of_check`,
  `Cslib.Complexity.NCL.Gate.expand_loopFree_of_check`: local checks establish the two graph
  properties of an expanded circuit.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gate

open Diagram Gadgets

variable {a b : List Color}

/-- Treat the vertex list of a circuit generator as a primitive generator. -/
@[expose] def interpretOpenSim (g : Gate a b) :
    OpenSim Gate.interp Prim.interp (gen g) (gen (Gate.interp.verts g)) :=
  OpenSim.genOfVerts (I := Gate.interp) (I' := Prim.interp) g (Gate.interp.verts g) rfl

/-- A primitive replacement paired with its open simulation. The one-wire threshold is the
constant-false source; the other threshold generators retain their original vertex lists. -/
@[expose] def implementation : {a b : List Color} → (g : Gate a b) →
    Σ H : Diagram Prim a b, OpenSim Gate.interp Prim.interp (gen g) H
  | [], [.blue], .vert 2 => ⟨fixedBlue, FixedBlue.openSim⟩
  | _, _, .vert n => ⟨_, interpretOpenSim (.vert n)⟩
  | _, _, .conv => ⟨Gadgets.conv, (interpretOpenSim .conv).trans Conv.openSim⟩
  | _, _, .vnoc => ⟨Gadgets.vnoc, Vnoc.openSim⟩
  | _, _, .free => ⟨freeEnd, (interpretOpenSim .free).trans FreeEnd.openSim⟩
  | _, _, .start => ⟨freeStart, FreeStart.openSim⟩
  | _, _, .cap => ⟨redCap, RedCap.openSim⟩

/-- Expand a circuit generator into a primitive diagram. -/
@[expose] def expand (g : Gate a b) : Diagram Prim a b := (implementation g).1

/-- Every circuit-generator expansion preserves its open interface. -/
@[expose] def expandOpenSim (g : Gate a b) : OpenSim Gate.interp Prim.interp (gen g) (expand g) :=
  (implementation g).2

/-- Substitution expands a whole circuit while preserving configurations and reachability. -/
@[expose] def expandSimulation (D : Diagram Gate a b) :
    ConstraintGraph.Simulation (D.graph Gate.interp) ((D.subst expand).graph Prim.interp) :=
  substSimulation expandOpenSim D

/-- Check AND/OR shape, distinct port edges, and consistent boundary incidences. -/
@[expose] def checkStandard (g : Gate a b) : Bool := (expand g).checkGens Prim.checkStandard

private theorem checks_of_standard (D : Diagram Gate a b)
    (h : D.checkGens checkStandard = true) :
    (D.subst expand).checkGens (fun p => p.all Vertex.checkAndOr) = true ∧
      (D.subst expand).checkGens (fun p => p.all Vertex.checkLoopFree) = true ∧
      (D.subst expand).checkGens Prim.interp.checkPorts = true := by
  apply (checkGens_checkStandard_iff _).1
  rwa [checkGens_subst]

/-- Standard circuit generators expand into a graph consisting of AND/OR vertices. -/
theorem expand_isAndOr_of_check (D : Diagram Gate a b) (h : D.checkGens checkStandard = true) :
    ((D.subst expand).graph Prim.interp).IsAndOr := by
  apply isAndOr_of_checkGens Prim.interp
  exact (checks_of_standard D h).1

/-- The same local checks also exclude self-loops in the expanded graph. -/
theorem expand_loopFree_of_check (D : Diagram Gate a b) (h : D.checkGens checkStandard = true) :
    ((D.subst expand).graph Prim.interp).LoopFree :=
  loopFree_of_checkGens Prim.interp _ (checks_of_standard D h).2.1

/-- Closing checked generator expansions gives exactly two consistent endpoints per edge. -/
theorem expand_wellFormed_of_check (D : Diagram Gate [] [])
    (h : D.checkGens checkStandard = true) :
    ((D.subst expand).graph Prim.interp).WellFormed :=
  wellFormed_of_checkGens Prim.interp _ (checks_of_standard D h).2.2

end Cslib.Complexity.NCL.Gate
