/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Standard
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileReachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing

/-!
# Planarizing canonical incidence drawings

The canonical drawing is passed to `planarizeAlong` with the source and cap implementations.
The result is a closed plane AND/OR diagram and a word in the L1 instance format.

## Main definitions

* `Planar.Embedding.planeDiagram`, `Planar.Embedding.word`: the planarized drawing and word.
* `Planar.Embedding.planeSimulation`: the simulation from the original finite graph.

## Main results

* `Planar.Embedding.plane_isAndOr`, `Planar.Embedding.plane_loopFree`,
  `Planar.Embedding.plane_wellFormed`: structural properties.
* `Planar.Embedding.checkPlane_word`, `Planar.Embedding.wellTyped_word`,
  `Planar.Embedding.compile_valid_word`: the L1 instance filters.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

variable {m : ℕ}

/-- The canonical incidence drawing with every crossing expanded. -/
@[expose] def planeDiagram (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) : Diagram Prim [] [] :=
  planarizeAlong Cell.expand (diagram vs (color vs) hw)

/-- The fully planar diagram simulates the original graph. -/
@[expose] def planeSimulation (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i)) :
    ConstraintGraph.Simulation (fun i : Fin vs.length => vs.get i)
      ((planeDiagram vs hw).graph Prim.interp) :=
  (simulation vs (color vs) hw
    (fun i _ hp => port_weight_color ha hw (List.get_mem _ i) hp) hl).trans
    (planarizeAlongSimulation Cell.interp_forward Cell.expandOpenSim (diagram vs (color vs) hw))

/-- The representative of an original edge after crossing replacement. -/
@[expose] def planeEdge (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) (e : Fin m) :
    (planeDiagram vs hw).Edge :=
  planarizeAlongEdge Cell.expandOpenSim (diagram vs (color vs) hw) (edge vs (color vs) hw e)

/-- Abstraction reads the tracked original edge in the planarized diagram. -/
theorem planeSimulation_abs (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (s : (planeDiagram vs hw).Edge → Bool) (e : Fin m) :
    (planeSimulation vs ha hw hl).abs s e = s (planeEdge vs hw e) := by
  change (simulation vs (color vs) hw
    (fun i _ hp => port_weight_color ha hw (List.get_mem _ i) hp) hl).abs
      ((planarizeAlongSimulation Cell.interp_forward Cell.expandOpenSim
        (diagram vs (color vs) hw)).abs s) e = _
  rw [simulation_abs]
  exact planarizeAlongSimulation_abs Cell.interp_forward Cell.expandOpenSim
    (diagram vs (color vs) hw) s (edge vs (color vs) hw e)

/-- Crossing replacement gives a diagram without swaps. -/
theorem plane_planar (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (planeDiagram vs hw).Planar :=
  planarizeAlong_planar Cell.expand_planar _

private theorem crossover_single_standard (c d : Color) :
    (Crossover.diagram c d).checkGens
      (fun g => (g.length == 1) && Prim.checkStandard g) = true := by
  rw [checkGens_and, Crossover.checkSingle, Crossover.checkStandard]
  rfl

/-- Every primitive cell in the planarized graph is one standard AND/OR vertex. -/
theorem plane_checkSingleStandard (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (planeDiagram vs hw).checkGens (fun g => (g.length == 1) && Prim.checkStandard g) = true :=
  (checkGens_planarizeAlong _ crossover_single_standard Cell.expand _).trans
    (checkStandard_diagram vs ha hw)

private theorem plane_standard (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (planeDiagram vs hw).checkGens Prim.checkStandard = true := by
  have h := plane_checkSingleStandard vs ha hw
  rw [checkGens_and] at h
  exact (Bool.and_eq_true_iff.1 h).2

/-- All vertices of the planarized graph are AND or OR vertices. -/
theorem plane_isAndOr (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    ((planeDiagram vs hw).graph Prim.interp).IsAndOr :=
  isAndOr_of_checkGens _ _ ((checkGens_checkStandard_iff _).1 (plane_standard vs ha hw)).1

/-- No vertex of the planarized graph contains both ends of an edge. -/
theorem plane_loopFree (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    ((planeDiagram vs hw).graph Prim.interp).LoopFree :=
  loopFree_of_checkGens _ _ ((checkGens_checkStandard_iff _).1 (plane_standard vs ha hw)).2.1

/-- The planarized graph has one endpoint of each direction per edge. -/
theorem plane_wellFormed (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    ((planeDiagram vs hw).graph Prim.interp).WellFormed :=
  wellFormed_of_checkGens _ _ ((checkGens_checkStandard_iff _).1 (plane_standard vs ha hw)).2.2

/-- The planar word representing the original finite graph. -/
@[expose] def word (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) : Word :=
  (planeDiagram vs hw).toWord Prim.interp 0

/-- The emitted word consists entirely of standard plane single-vertex layers. -/
theorem checkPlane_word (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (word vs hw).checkPlane = true :=
  checkPlane_toWord _ _ (plane_planar vs hw) (plane_checkSingleStandard vs ha hw)

/-- The emitted word is closed and well typed. -/
theorem wellTyped_word (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (word vs hw).WellTyped [] [] := wellTyped_toWord _ _

/-- Compiling the emitted word gives valid finite AND/OR graph data. -/
theorem compile_valid_word (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (Word.compile (word vs hw)).Valid :=
  compile_valid _ _ (plane_isAndOr vs ha hw) (plane_wellFormed vs ha hw)

end Cslib.Complexity.NCL.Planar.Embedding
