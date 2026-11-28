/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Planarize
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane

/-!
# Planar AND/OR expansion of circuit diagrams

Expand every circuit cell into its primitive implementation and route all swaps through the
certified crossover family. Standard source cells give a planar, loop-free AND/OR diagram;
closing its boundary gives consistent opposite endpoints for every edge.

## Main definitions

* `Cslib.Complexity.NCL.Planar.Circuit.diagram`: the planar primitive expansion.
* `Cslib.Complexity.NCL.Planar.Circuit.simulation`: its simulation of the source circuit.
* `Cslib.Complexity.NCL.Planar.Circuit.edge`: the representative of an original edge.

## Main results

* `Cslib.Complexity.NCL.Planar.Circuit.planar`,
  `Cslib.Complexity.NCL.Planar.Circuit.andOr`,
  `Cslib.Complexity.NCL.Planar.Circuit.loopFree`,
  `Cslib.Complexity.NCL.Planar.Circuit.wellFormed`: the output graph properties.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

open Diagram

private theorem Gate.expand_properties {a b : List Color} (g : Gate a b) : (expand g).Planar ∧
    (expand g).checkGens (fun p => p.length == 1) = true := by
  cases g with
  | vert n =>
    match a, b, n with
    | [], [.blue], 2 => decide +kernel
    | _ :: _, _, _ | [], [], _ | [], .red :: _, _ | [], .blue :: _ :: _, _
    | [], [.blue], 0 | [], [.blue], 1 | [], [.blue], _ + 3 => exact ⟨True.intro, rfl⟩
  | _ => decide +kernel

/-- Every circuit-generator implementation contains no swaps. -/
private theorem Gate.expand_planar {a b : List Color} (g : Gate a b) : (expand g).Planar :=
  (expand_properties g).1

namespace Planar.Circuit

variable {a b : List Color}

/-- Expand a circuit into a planar primitive diagram. -/
@[expose] def diagram (D : Diagram Gate a b) : Diagram Prim a b := planarizeAlong Gate.expand D

/-- The planar expansion simulates the original circuit, including its legal configurations. -/
@[expose] def simulation (D : Diagram Gate a b) :
    ConstraintGraph.Simulation (D.graph Gate.interp) ((diagram D).graph Prim.interp) :=
  planarizeAlongSimulation Gate.interp_forward Gate.expandOpenSim D

/-- The concrete representative of an original circuit edge. -/
@[expose] def edge (D : Diagram Gate a b) (e : D.Edge) : (diagram D).Edge :=
  planarizeAlongEdge Gate.expandOpenSim D e

/-- Original edges in the upper component keep their planar edge numbers after stacking. -/
theorem num_edge_compLeft {a b c : List Color} (D₁ : Diagram Gate a b)
    (D₂ : Diagram Gate b c) (e : D₁.Edge) :
    (diagram (D₁.comp D₂)).num
      (edge (D₁.comp D₂) (compLeft D₁ D₂ e)) =
      (diagram D₁).num (edge D₁ e) := by
  have he : edge (D₁.comp D₂) (compLeft D₁ D₂ e) =
      compLeft (diagram D₁) (diagram D₂)
        (edge D₁ e) := by
    cases e with
    | inl i =>
      change (.inl i : ((diagram D₁).comp (diagram D₂)).Edge) =
        compLeft (diagram D₁) (diagram D₂)
          ((openSimSubst (Routed.expandOpenSim Gate.expandOpenSim)
            (Route.diagram D₁)).ι (.inl i))
      rw [OpenSim.ι_top]
      rfl
    | inr e => rfl
  rw [he]
  exact Diagram.name_compLeft _ _ _ _ _

/-- Abstraction reads the representative of the original edge. -/
theorem simulation_abs (D : Diagram Gate a b) (t : (diagram D).Edge → Bool) (e : D.Edge) :
    (simulation D).abs t e = t (edge D e) :=
  planarizeAlongSimulation_abs Gate.interp_forward Gate.expandOpenSim D t e

/-- Circuit expansions are planar. -/
theorem planar (D : Diagram Gate a b) : (diagram D).Planar :=
  planarizeAlong_planar Gate.expand_planar D

/-- Every cell of a standard source circuit has a standard planar implementation. -/
theorem checkStandard (D : Diagram Gate a b) (hD : D.checkGens Gate.checkStandard = true) :
    (diagram D).checkGens Prim.checkStandard = true :=
  (checkGens_planarizeAlong Prim.checkStandard Crossover.checkStandard Gate.expand D).trans hD

/-- Every primitive cell of the planar circuit contains one vertex. -/
private theorem checkSingle (D : Diagram Gate a b) :
    (diagram D).checkGens (fun g => g.length == 1) = true := by
  rw [diagram, checkGens_planarizeAlong _ Crossover.checkSingle]
  induction D with
  | gen g => exact (Gate.expand_properties g).2
  | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact congrArg₂ Bool.and ih₁ ih₂

/-- A standard circuit emits a word of standard single-vertex layers. -/
theorem checkPlane_word (D : Diagram Gate a b) (hD : D.checkGens Gate.checkStandard = true) :
    ((diagram D).toWord Prim.interp 0).checkPlane = true := by
  apply checkPlane_toWord _ _ (planar D)
  rw [checkGens_and]
  exact congrArg₂ Bool.and (checkSingle D) (checkStandard D hD)

/-- Standard source cells expand into AND/OR vertices. -/
theorem andOr (D : Diagram Gate a b) (hD : D.checkGens Gate.checkStandard = true) :
    ((diagram D).graph Prim.interp).IsAndOr :=
  isAndOr_of_checkGens Prim.interp _ ((checkGens_checkStandard_iff _).1 (checkStandard D hD)).1

/-- No expanded vertex repeats an edge. -/
theorem loopFree (D : Diagram Gate a b) (hD : D.checkGens Gate.checkStandard = true) :
    ((diagram D).graph Prim.interp).LoopFree :=
  loopFree_of_checkGens Prim.interp _ ((checkGens_checkStandard_iff _).1 (checkStandard D hD)).2.1

/-- Colored boundary incidences are preserved by planar expansion. -/
theorem checkPorts (D : Diagram Gate a b) (hD : D.checkGens Gate.checkStandard = true) :
    (diagram D).checkGens Prim.interp.checkPorts = true :=
  ((checkGens_checkStandard_iff _).1 (checkStandard D hD)).2.2

/-- Closed planar expansions have consistent opposite endpoints on every edge. -/
theorem wellFormed (D : Diagram Gate [] []) (hD : D.checkGens Gate.checkStandard = true) :
    ((diagram D).graph Prim.interp).WellFormed :=
  wellFormed_of_checkGens Prim.interp _ (checkPorts D hD)

end Planar.Circuit
end Cslib.Complexity.NCL
