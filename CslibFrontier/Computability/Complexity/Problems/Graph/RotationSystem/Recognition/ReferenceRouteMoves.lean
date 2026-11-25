/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Moves
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds

/-!
# Parity moves on reference routes

Each free subdivision edge receives its prescribed parity excursion at its midpoint.
The resulting routes keep the reference vertices and outgoing rays, and no excursion
visits a declared vertex. The construction is original finite polygonal geometry;
it admits retracing and makes no assertion about general position or pair crossings.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

/-- Realize the entire finite move table as ray-parity differences from the reference
routes. Frozen routes remain literal, outgoing germs keep their positive rays, and each
route avoids the declared vertices other than its endpoints. -/
theorem exists_reference_drawing_with_move_rayParity {I : FixedRotationInput} (hI : Valid I)
    (moves : Moves (frame I)) (hfrozen : FrozenMoves (frame I) moves) {u : ℂ} (hu : u ≠ 0) :
    let ref := referenceDrawing I
    ∃ D : PolygonalDrawing (subdivisionGraph I), D.vertex = ref.vertex ∧
      (∀ e, ((frame I).segments.getD e.val ((0, 0), false)).frozen = true →
        D.route e = ref.route e) ∧
      (∀ e side, ∃ k : ℝ, 0 < k ∧ (D.route e).germ side = k • (ref.route e).germ side) ∧
      (∀ e (v : Fin (frame I).vertexCount),
        (∀ side, Dart.vertex (e, side) ≠ v.val) → D.vertex v.val ∉ (D.route e).support) ∧
      ∀ e (v : Fin (frame I).vertexCount),
        (D.route e).rayParity u (D.vertex v.val) =
          (ref.route e).rayParity u (ref.vertex v.val) + readMove (frame I) moves e.val v.val := by
  classical
  let F := frame I
  let G := subdivisionGraph I
  let ref := referenceDrawing I
  let V := Fin F.vertexCount
  let E := Fin G.edges.length
  have hvertex (v : V) : v.val ∈ G.vertices := List.mem_range.mpr v.isLt
  let point : V ↪ ℂ := ⟨fun v => ref.vertex v.val, fun a b hab =>
    Fin.ext (referenceDrawing_vertices_injective hI (hvertex a) (hvertex b) hab)⟩
  let points : Finset ℂ := Finset.univ.map point
  have hpoint (v : V) : point v ∈ points := Finset.mem_map_of_mem point (Finset.mem_univ v)
  let frozen (e : E) := (F.segments.getD e.val ((0, 0), false)).frozen = true
  have each (e : E) : ∃ r : Route,
      (∀ side, r.endpoint side = (ref.route e).endpoint side) ∧
      (frozen e → r = ref.route e) ∧
      (∀ side, ∃ k : ℝ, 0 < k ∧ r.germ side = k • (ref.route e).germ side) ∧
      (∀ v : V, (∀ side, Dart.vertex (e, side) ≠ v.val) → point v ∉ r.support) ∧
      ∀ v : V, r.rayParity u (point v) =
        (ref.route e).rayParity u (point v) + readMove F moves e.val v.val := by
    have heIdx : e.val < F.segments.length := by
      simpa only [G, F, subdivisionGraph, frame, List.length_map] using e.isLt
    let idx : Fin F.segments.length := ⟨e.val, heIdx⟩
    have hread (v : V) : readMove F moves e.val v.val = moves idx v := by
      simp only [readMove, heIdx, v.isLt, dite_true, idx]
      rfl
    let a := ref.vertex (Dart.vertex (e, false))
    let b := ref.vertex (Dart.vertex (e, true))
    have havoid (v : V) (hne : ∀ side, Dart.vertex (e, side) ≠ v.val) :
        point v ∉ segment ℝ a b := by
      rw [segment_eq_image_lineMap]
      rintro ⟨t, ht, heq⟩
      obtain ⟨side, _, hs⟩ := referenceDrawing_vertex_contacts hI e 0 ht (hvertex v)
        ((Route.eval_line a b 0 t).trans heq)
      exact hne side hs
    by_cases hfixed : frozen e
    · refine ⟨ref.route e, fun _ => rfl, fun _ => rfl,
        fun _ => ⟨1, one_pos, (one_smul ℝ _).symm⟩,
        fun v hne => show point v ∉ (Route.line a b).support from
          Route.support_line a b ▸ havoid v hne,
        fun v => by rw [hread, hfrozen idx v hfixed, ← Bool.zero_eq_false, add_zero]⟩
    let odd := (Finset.univ.filter fun v : V => moves idx v = true).map point
    have hsub : odd ⊆ points := Finset.map_subset_map.mpr (Finset.filter_subset _ _)
    have hbit (v : V) : decide (point v ∈ odd) = readMove F moves e.val v.val := by
      rw [hread, Bool.decide_congr (show point v ∈ odd ↔ moves idx v = true by
        simp only [odd, Finset.mem_map' point, Finset.mem_filter, Finset.mem_univ, true_and])]
      cases moves idx v <;> rfl
    have hmid : AffineMap.lineMap a b (1 / 2 : ℝ) ∈ Set.univ \ (↑points : Set ℂ) :=
      ⟨Set.mem_univ _, fun h => by
        obtain ⟨v, _, hv⟩ := Finset.mem_map.mp h
        obtain ⟨side, hs, _⟩ := referenceDrawing_vertex_contacts hI e 0
          (by constructor <;> norm_num) (hvertex v) ((Route.eval_line a b 0 _).trans hv.symm)
        have ht := (Route.atEnd_line_iff a b 0 (1 / 2 : ℝ) side).mp hs
        cases side <;> norm_num at ht⟩
    obtain ⟨r, he, hg, _, hsupport, hpar⟩ :=
      Route.exists_line_add_rayParity isOpen_univ isPathConnected_univ points odd hsub
        (fun z _ => Set.mem_univ z) a b (by constructor <;> norm_num) hmid hu
    exact ⟨r, he, fun h => (hfixed h).elim,
      fun side => ⟨if side then 1 - (1 / 2 : ℝ) else 1 / 2, by cases side <;> norm_num, hg side⟩,
      fun v hne hv => (hsupport hv).elim (havoid v hne) fun h => h.2 (hpoint v),
      fun v => hbit v ▸ hpar (point v) (hpoint v)⟩
  choose routes hroutes using each
  exact ⟨⟨ref.vertex, routes, fun e side => ((hroutes e).1 side).trans (ref.endpoint_eq e side)⟩,
    rfl, fun e => (hroutes e).2.1, fun e => (hroutes e).2.2.1,
    fun e => (hroutes e).2.2.2.1, fun e => (hroutes e).2.2.2.2⟩

end Cslib.Complexity.Graph.RotationRecognition
