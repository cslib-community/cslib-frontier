/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceSpokeEmbedding
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexPlacement
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionContraction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEmbedding
import Mathlib.Order.Filter.Finite

/-!
# Recognition subdivisions with short reference spokes

Place the original centers at their reference points, align the prescribed outgoing rays,
and cut the recovered routes again. With one sufficiently small factor common to all fixed
darts, their retained end routes are literally the scaled straight reference spokes. The
other routes still form an actual subdivision embedding, including at either end of a loop.
This is original geometry.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal
open scoped Topology

/-- At every sufficiently small positive common scale, the recognition subdivision has a
polygonal embedding with the prescribed reference centers and literal scaled frozen spokes.
Each fixed leaf is the corresponding point of its reference segment at that scale. -/
theorem exists_subdivision_embedding_with_scaled_reference_spokes
    {I : FixedRotationInput} (hI : Valid I) {D : PolygonalDrawing I.graph}
    (hD : D.IsEmbedding) {r : RotationSystem I.graph} (hReal : D.Realizes r)
    (hfixed : Realizes I r) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ s ∈ Set.Ioo (0 : ℝ) ε,
      ∃ E : PolygonalDrawing (subdivisionGraph I), E.IsEmbedding ∧
        (∀ v ∈ I.graph.vertices, E.vertex v = referencePoint I v) ∧
        ∀ d : Dart I.graph, (I.orders.getD d.vertex none).isSome →
          let a := referencePoint I d.vertex
          let b := a + s • (referenceDrawing I).germ (subdivisionDart I d)
          E.vertex (subdivisionDart I d).reverse.vertex = b ∧
            E.route (subdivisionDart I d).1 = if d.2 then Route.line b a else Route.line a b := by
  classical
  have hdecl : I.graph.incidenceVertices ⊆ I.graph.vertices :=
    fun v hv => hI.1 ▸ List.mem_range.mpr (hI.2.1 v hv)
  have hsub {v : ℕ} (hv : v ∈ I.graph.vertices) : v ∈ (subdivisionGraph I).vertices := by
    rw [hI.1] at hv
    change v ∈ List.range (subdivisionSize I)
    exact List.mem_range.mpr ((List.mem_range.mp hv).trans_le (Nat.le_add_right _ _))
  have href : Set.InjOn (referencePoint I) {v | v ∈ I.graph.vertices} :=
    fun _ hv _ hw h => referenceDrawing_vertices_injective hI (hsub hv) (hsub hw) h
  obtain ⟨P, hP, hposition, _, hdir, _, _⟩ := hD.exists_vertex_placement hdecl _ href
  have hPReal : P.Realizes r := by
    refine ⟨hP.germ_ne_zero, hP.directions_injective, ?_⟩
    intro a b c hab hbc hnab hnbc hnac
    simpa only [hdir] using hReal.clockwise a b c hab hbc hnab hnbc hnac
  obtain ⟨δ, hδ, halign⟩ := exists_subdivision_embedding_with_reference_spokes hI hP hPReal hfixed
  obtain ⟨_, F, _, hF, _, hcenter, _, _, _, hfixedGerm⟩ :=
    halign (δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩
  obtain ⟨A, hA, hvertices, _, hAgerm⟩ := exists_contracted_subdivision_embedding hI hF
  have hAcenter (v : ℕ) (hv : v ∈ I.graph.vertices) : A.vertex v = referencePoint I v := by
    rw [hvertices, hcenter v hv, hposition v hv]
  have hfactor (d : Dart I.graph) : ∃ c > (0 : ℝ),
      (I.orders.getD d.vertex none).isSome →
        A.germ d = c • (referenceDrawing I).germ (subdivisionDart I d) := by
    by_cases hd : (I.orders.getD d.vertex none).isSome
    · obtain ⟨c, hc, h⟩ := hfixedGerm d hd
      exact ⟨c, hc, fun _ => (hAgerm d).trans h⟩
    · exact ⟨1, zero_lt_one, fun h => (hd h).elim⟩
  choose factor hfactor_pos hfactor_eq using hfactor
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ d, s < factor d / 2 :=
    Filter.eventually_all.mpr fun d => eventually_lt_nhds (half_pos (hfactor_pos d))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨min ε 1, ⟨lt_min hε zero_lt_one, min_le_right _ _⟩, fun s hs => ?_⟩
  have hsε := hs.2.trans_le (min_le_left ε 1)
  have hsball : s ∈ Metric.ball (0 : ℝ) ε :=
    Metric.mem_ball.mpr (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hs.1] using hsε)
  have htime (d : Dart I.graph) : s / factor d ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    refine ⟨div_pos hs.1 (hfactor_pos d), (div_lt_iff₀ (hfactor_pos d)).mpr ?_⟩
    have h := hball hsball d
    linarith only [h]
  obtain ⟨E, hE, hkeep, hends⟩ :=
    exists_subdivision_embedding_at_endTimes hI hA (fun d => s / factor d) htime
  refine ⟨E, hE, fun v hv => (hkeep v hv).trans (hAcenter v hv), ?_⟩
  intro d hd
  have hv := RotationSystem.vertex_mem hdecl d
  have h := hends d
  dsimp only at h ⊢
  rw [hAcenter _ hv, hfactor_eq d hd, smul_smul, div_mul_cancel₀ _ (hfactor_pos d).ne'] at h
  exact h

end Cslib.Complexity.Graph.RotationRecognition
