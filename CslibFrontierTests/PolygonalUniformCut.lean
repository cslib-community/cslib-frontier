/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary-import uniform vertex cut regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star

set_option linter.privateModule false

/-! Uniform cut ports and exact contacts of cut stubs and trimmed spokes. -/

namespace CslibFrontierTests.PolygonalUniformCut

open Cslib.Complexity.Graph Cslib.Polygonal
open Cslib.Complexity.Graph.PolygonalDrawing Cslib.Complexity.Graph.RotationSystem

private abbrev G := starGraph 2
private abbrev D : PolygonalDrawing G := PolygonalDrawing.star 2
private abbrev spoke : Fin G.edges.length := ⟨0, by decide⟩
private abbrev other : Fin G.edges.length := ⟨1, by decide⟩

example : ∃ ρ : ℝ, 0 < ρ ∧
    Disjoint (Metric.closedBall (D.vertex 0) ρ) (Metric.closedBall (D.vertex 2) ρ) ∧
    let stub (d : Dart G) := segment ℝ (D.vertex d.vertex) (D.cutPort ρ d)
    let time (d : Dart G) := ρ / ‖D.germ d‖
    let p := (D.route spoke).cutEnds (time (spoke, false)) (time (spoke, true))
    Function.Injective (D.cutPort ρ) ∧
    stub (spoke, true) ∩ stub (other, true) = {D.vertex 2} ∧
    stub (spoke, true) ∩ (D.route other).support = {D.vertex 2} ∧
    p.support ∩ Metric.closedBall (D.vertex 2) ρ = {D.cutPort ρ (spoke, true)} := by
  have hD := star_isEmbedding 2
  have hdeclared := vertex_mem (starGraph_endpoints_declared 2)
  obtain ⟨ε, hε, hcut⟩ := D.exists_uniform_restriction hD.vertex_contacts hD.vertices_injective
    hdeclared hD.germ_ne_zero
  let ρ := ε / 2
  have hρ : ρ ∈ Set.Ioo 0 ε := ⟨half_pos hε, half_lt_self hε⟩
  obtain ⟨hdisjoint, _, hlocal, hcontact⟩ := hcut ρ hρ
  let stub (d : Dart G) := segment ℝ (D.vertex d.vertex) (D.cutPort ρ d)
  have hc : Dart.vertex (G := G) (spoke, true) = 2 := by decide
  have hc' : Dart.vertex (G := G) (other, true) = 2 := by decide
  have hcenter (d : Dart G) (hd : d.vertex = 2) : D.vertex 2 ∈ stub d :=
    (congrArg D.vertex hd) ▸ left_mem_segment ℝ (D.vertex d.vertex) (D.cutPort ρ d)
  refine ⟨ρ, hρ.1, hdisjoint 0 (by decide) 2 (by decide) (by decide),
    D.cutPort_injective_of_disjoint_balls hρ.1 hdeclared hD.germ_ne_zero
      hD.directions_injective hdisjoint, ?_, ?_, ?_⟩
  · change stub (spoke, true) ∩ stub (other, true) = {D.vertex 2}
    ext z
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨_, hz⟩ := D.eq_vertex_of_mem_cutPort_segments hρ.1 hdeclared hD.germ_ne_zero
        hD.directions_injective hdisjoint (by decide : (spoke, true) ≠ (other, true)) ha hb
      exact Set.mem_singleton_iff.mpr (hz.trans (congrArg D.vertex hc))
    · intro hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨hcenter _ hc, hcenter _ hc'⟩
  · change stub (spoke, true) ∩ (D.route other).support = {D.vertex 2}
    ext z
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨_, _, hz⟩ := D.eq_vertex_of_mem_cutPort_segment_and_route hρ.1 (spoke, true)
        (hD.germ_ne_zero _) hD.directions_injective other (by decide)
        (hlocal _ (hdeclared _) other) ha hb
      exact Set.mem_singleton_iff.mpr (hz.trans (congrArg D.vertex hc))
    · intro hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      have hpoint : (D.route other).eval 0 1 = (D.route other).endpoint true := by
        change AffineMap.lineMap _ (0 : ℂ) (1 : ℝ) = 0
        exact AffineMap.lineMap_apply_one _ _
      rw [D.endpoint_eq, hc'] at hpoint
      exact ⟨hcenter _ hc, hpoint ▸ (D.route other).at_mem_support 0 (by simp)⟩
  let time (d : Dart G) := ρ / ‖D.germ d‖
  let p := (D.route spoke).cutEnds (time (spoke, false)) (time (spoke, true))
  change p.support ∩ Metric.closedBall (D.vertex 2) ρ = {D.cutPort ρ (spoke, true)}
  ext z
  constructor
  · rintro ⟨hz, hball⟩
    obtain ⟨i, t, htime, hpoint⟩ := (p.mem_support_iff z).mp hz
    obtain ⟨b, _, hv, he⟩ := hcontact spoke 2 (by decide) i t htime (hpoint.symm ▸ hball)
    cases b
    · exact ((by decide : Dart.vertex (G := G) (spoke, false) ≠ 2) hv).elim
    · exact Set.mem_singleton_iff.mpr (hpoint.symm.trans he)
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hend : p.endpoint true = D.cutPort ρ (spoke, true) := by
      rw [Route.endpoint_cutEnds, D.cutPort_eq_eval]
      rfl
    have heval : p.eval (p.endSegment true) 1 = p.endpoint true := by
      have h := p.eval_near_end true 0
      change p.eval (p.endSegment true) (1 - 0) = p.endpoint true + (0 : ℝ) • p.germ true at h
      simpa only [sub_zero, zero_smul, add_zero] using h
    refine ⟨(heval.trans hend) ▸ p.at_mem_support (p.endSegment true) (by simp), ?_⟩
    rw [Metric.mem_closedBall, ← hc, D.dist_cutPort hρ.1.le _ (hD.germ_ne_zero _)]

end CslibFrontierTests.PolygonalUniformCut
