/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Colors
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane

/-!
# Standard cells in canonical planarizations

Original AND/OR vertices remain standard source cells, and the cap and crossover implementations
are standard single-vertex diagrams. Their composition therefore satisfies the primitive-cell
checks used by the plane-word interface.

## Main results

* `Planar.Embedding.checkStandard_diagram`: expanded cells of the canonical incidence drawing
  are standard single-vertex AND/OR cells.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

private theorem source_loopFree (cs : List Color) (need : ℕ) :
    (genVertex [] cs need).checkLoopFree = true := by
  apply (Vertex.checkLoopFree_eq_true_iff _).2
  simp only [genVertex, List.length_nil, List.finRange_zero, List.map_nil,
    List.nil_append, List.map_map, Function.comp_def]
  exact (List.nodup_finRange cs.length).map Sum.inr_injective

private theorem source_ports (cs : List Color) (need : ℕ) :
    Prim.interp.checkPorts [genVertex [] cs need] = true := by
  simp only [Interp.checkPorts, Prim.interp, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, decide_eq_true_eq]
  exact List.Perm.refl _

private theorem source_andOr {E : Type*} (v : Vertex E) (c : Port E → Color)
    (ha : v.IsAndOr) (hc : ∀ p ∈ v.ports, p.weight = (c p.port).weight) :
    (genVertex [] ((v.ports.map WeightedPort.port).map c) v.minInflow).checkAndOr = true := by
  have hweights : v.ports.map (fun p => (c p.port).weight) = v.ports.map WeightedPort.weight :=
    List.map_congr_left (fun p hp => (hc p hp).symm)
  have he : (Sources.spec c (v.ports.map WeightedPort.port) v.minInflow).checkAndOr =
      v.checkAndOr := by
    simp only [Vertex.checkAndOr, Sources.spec, List.map_map, Function.comp_def]
    rw [hweights]
  calc
    _ = ((genVertex [] ((v.ports.map WeightedPort.port).map c) v.minInflow).map
        (Sources.sourceLabel c (v.ports.map WeightedPort.port))).checkAndOr :=
      (Vertex.checkAndOr_map _ _).symm
    _ = (Sources.spec c (v.ports.map WeightedPort.port) v.minInflow).checkAndOr := by
      rw [Sources.map_source]
    _ = v.checkAndOr := he
    _ = true := (Vertex.checkAndOr_eq_true_iff v).2 ha

private theorem source_standard {E : Type*} (v : Vertex E) (c : Port E → Color)
    (ha : v.IsAndOr) (hc : ∀ p ∈ v.ports, p.weight = (c p.port).weight) :
    (Cell.expand (.source ((v.ports.map WeightedPort.port).map c) v.minInflow)).checkGens
      (fun g => (g.length == 1) && Prim.checkStandard g) = true := by
  have hs : Prim.checkStandard
      [genVertex [] ((v.ports.map WeightedPort.port).map c) v.minInflow] = true := by
    simp only [Prim.checkStandard, List.all_cons, List.all_nil, Bool.and_true,
      source_andOr v c ha hc, source_loopFree, source_ports]
  simpa only [Cell.expand, checkGens, List.length_singleton,
    beq_self_eq_true, Bool.true_and] using hs

private theorem sources_standard {E : Type*} (vs : List (Vertex E)) (c : Port E → Color)
    (ha : ∀ v ∈ vs, v.IsAndOr) (hc : ∀ v ∈ vs, ∀ p ∈ v.ports, p.weight = (c p.port).weight) :
    (Sources.vertices c vs).diagram.checkGens
      (fun g => (Cell.expand g).checkGens
        (fun p => (p.length == 1) && Prim.checkStandard p)) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (_ && _) = true
    exact Bool.and_eq_true_iff.2
      ⟨source_standard v c (ha v (List.mem_cons_self ..))
        (hc v (List.mem_cons_self ..)),
        ih (fun w hw => ha w (List.mem_cons_of_mem v hw))
          (fun w hw => hc w (List.mem_cons_of_mem v hw))⟩

private theorem caps_standard {E : Type*} (es : List E) (c : E → Color) :
    (Sinks.caps c es).diagram.checkGens
      (fun g => (Cell.expand g).checkGens
        (fun p => (p.length == 1) && Prim.checkStandard p)) = true := by
  induction es with
  | nil => rfl
  | cons e es ih => exact Bool.and_eq_true_iff.2 ⟨Gadgets.Wire.cap_checkStandard _, ih⟩

/-- Every expanded cell of the canonical incidence drawing is a standard single-vertex cell. -/
theorem checkStandard_diagram {m : ℕ} (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (diagram vs (color vs) hw).checkGens
      (fun g => (Cell.expand g).checkGens
        (fun p => (p.length == 1) && Prim.checkStandard p)) = true := by
  change (_ && (_ && _)) = true
  exact Bool.and_eq_true_iff.2
    ⟨sources_standard vs (fun p => color vs p.edge) ha
      (fun _ hv _ hp => port_weight_color ha hw hv hp),
      Bool.and_eq_true_iff.2 ⟨(routing vs (color vs) hw).all_checks _, caps_standard _ _⟩⟩

end Cslib.Complexity.NCL.Planar.Embedding
