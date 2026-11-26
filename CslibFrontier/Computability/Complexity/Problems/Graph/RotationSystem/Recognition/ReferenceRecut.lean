/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceSpokeEmbedding
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.CutTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexPlacement
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.FrozenReference
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionContraction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEmbedding
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Order.Filter.Finite


/-!
# Recognition subdivisions with literal reference spokes

Place the original centers at their reference points, align the prescribed outgoing rays,
and cut the recovered routes again. With one sufficiently small factor common to all fixed
darts, their retained end routes are literally the scaled straight reference spokes. The
other routes still form an actual subdivision embedding, including at either end of a loop.
Inverse strip compression then restores each frozen route as a single literal reference segment.
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
  have hPReal : P.Realizes r := ⟨hP.germ_ne_zero, hP.directions_injective,
    fun a b c hab hbc hnab hnbc hnac => by
      simpa only [hdir] using hReal.clockwise a b c hab hbc hnab hnbc hnac⟩
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
  have htime (d : Dart I.graph) : s / factor d ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    ⟨div_pos hs.1 (hfactor_pos d),
      (div_lt_iff₀ (hfactor_pos d)).mpr (by linarith [hball hsball d])⟩
  obtain ⟨E, hE, hkeep, hends⟩ :=
    exists_subdivision_embedding_at_endTimes hI hA (fun d => s / factor d) htime
  refine ⟨E, hE, fun v hv => (hkeep v hv).trans (hAcenter v hv), fun d hd => ?_⟩
  simpa only [hAcenter _ (RotationSystem.vertex_mem hdecl d), hfactor_eq d hd, smul_smul,
    div_mul_cancel₀ _ (hfactor_pos d).ne'] using hends d

/-- A realization of the prescribed rotation admits a subdivision embedding at the original
reference centers with every frozen edge equal to its complete literal reference route.
The endpoints of those routes are therefore at their exact reference coordinates. -/
theorem exists_subdivision_embedding_with_frozen_reference_routes
    {I : FixedRotationInput} (hI : Valid I) {D : PolygonalDrawing I.graph}
    (hD : D.IsEmbedding) {r : RotationSystem I.graph} (hReal : D.Realizes r)
    (hfixed : Realizes I r) :
    ∃ E : PolygonalDrawing (subdivisionGraph I), E.IsEmbedding ∧
      (∀ v ∈ I.graph.vertices, E.vertex v = referencePoint I v) ∧
      ∀ e : Fin (subdivisionGraph I).edges.length,
        ((subdivide I)[e.val]'(by
          simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
        E.route e = (referenceDrawing I).route e := by
  classical
  obtain ⟨ε, hε, hrecut⟩ := exists_subdivision_embedding_with_scaled_reference_spokes
    hI hD hReal hfixed
  let s := ε / 2
  have hs : s ∈ Set.Ioo (0 : ℝ) ε := ⟨half_pos hε.1, half_lt_self hε.1⟩
  obtain ⟨P, hP, hcenter, hspoke⟩ := hrecut s hs
  obtain ⟨F, cuts, hFcenter, hFspoke, hline⟩ :=
    exists_frozen_reference_compression hI (s := s) ⟨hs.1, hs.2.le.trans hε.2⟩
  let c : ℂ →ᵃ[ℝ] ℝ := Complex.reCLM.toLinearMap.toAffineMap
  let Q := referenceDrawing I
  let frozen (e : Fin (subdivisionGraph I).edges.length) :=
    ((subdivide I)[e.val]'(by simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen =
      true
  have hparam (e : Fin (subdivisionGraph I).edges.length) (he : frozen e) :
      let a := (Q.route e).start
      let b := (Q.route e).finish
      P.route e = Route.line (F a) (F b) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          F (AffineMap.lineMap a b t) = AffineMap.lineMap (F a) (F b) t := by
    obtain ⟨d, rfl, hd⟩ := (frozen_iff_exists_subdivisionDart I e).mp he
    let f := (subdivisionDart I d).1
    let a := (Q.route f).start
    let b := (Q.route f).finish
    let o := referencePoint I d.vertex
    let T : ℂ →ᵃ[ℝ] ℂ := AffineMap.homothety o s
    have hQ : Q.route f = Route.line a b := rfl
    have hT (z : ℂ) : T z = o + s • (z - o) :=
      (AffineMap.homothety_apply o s z).trans (add_comm _ _)
    have hFt (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        F (AffineMap.lineMap a b t) = T (AffineMap.lineMap a b t) := by
      rw [hT]
      exact hFspoke d hd _ ((Route.support_line a b).symm ▸ lineMap_mem_segment ℝ a b ht)
    have ha : F a = T a := by
      simpa only [AffineMap.lineMap_apply_zero] using hFt 0 ⟨le_rfl, zero_le_one⟩
    have hb : F b = T b := by
      simpa only [AffineMap.lineMap_apply_one] using hFt 1 ⟨zero_le_one, le_rfl⟩
    have ho : (Q.route f).endpoint d.2 = o :=
      (Q.endpoint_eq f d.2).trans (congrArg (referencePoint I) (subdivisionDart_endpoints I d).1)
    have hg : Q.germ (subdivisionDart I d) = if d.2 then a - b else b - a := by
      change (Q.route f).germ d.2 = _
      rw [hQ, Route.germ_line]
    refine ⟨?_, fun t ht => ?_⟩
    · have hp := (hspoke d hd).2
      change P.route f = _ at hp ⊢
      rw [hp, ha, hb, hg, hT a, hT b]
      cases htag : d.2 <;>
        simp only [htag, Route.endpoint, Bool.false_eq_true, ↓reduceIte, a, b] at ho ⊢ <;>
        simp [ho, o]
    · calc
        F (AffineMap.lineMap a b t) = T (AffineMap.lineMap a b t) := hFt t ht
        _ = AffineMap.lineMap (T a) (T b) t := AffineMap.apply_lineMap T a b t
        _ = _ := by rw [← ha, ← hb]
  let M := P.mapAtCuts (c := c) hline
  let E : PolygonalDrawing (subdivisionGraph I) :=
    { vertex := M.vertex
      route e := if frozen e then Q.route e else M.route e
      endpoint_eq := fun e side => by
        by_cases he : frozen e
        · have heq := (hparam e he).1 ▸ P.endpoint_eq e side
          have hx : F ((Q.route e).endpoint side) = P.vertex (Dart.vertex (e, side)) := by
            cases side <;> exact heq
          rw [ite_eq_left he]
          exact (F.symm_apply_apply _).symm.trans (congrArg F.symm hx)
        · simpa only [ite_eq_right he] using M.endpoint_eq e side }
  have hSimple (e : Fin (subdivisionGraph I).edges.length) : (E.route e).IsSimple := by
    by_cases he : frozen e
    · simpa only [E, ite_eq_left he] using referenceDrawing_simple hI e
    · simpa only [E, ite_eq_right he] using (hP.mapAtCuts (c := c) hline F.symm.injective).simple e
  refine ⟨E, hP.of_route_map F.symm.injective (fun _ => rfl) hSimple ?_, ?_,
    fun e he => ite_eq_left he⟩
  · intro e
    by_cases he : frozen e
    · obtain ⟨hshort, hFt⟩ := hparam e he
      dsimp only [E]
      rw [ite_eq_left he]
      intro i
      rw [hshort]
      refine ⟨0, 0, 1, le_rfl, zero_lt_one, le_rfl, fun t ht => ?_⟩
      simp only [AffineMap.lineMap_apply_ring, mul_zero, mul_one, zero_add]
      change (Route.line (Q.route e).start (Q.route e).finish).eval i t = _ ∧ _
      exact ⟨(Route.eval_line _ _ i t).trans
          (F.injective ((hFt t ht).trans (F.apply_symm_apply _).symm)),
        fun side => (Route.atEnd_line_iff _ _ i t side).trans
          (Route.atEnd_line_iff _ _ 0 t side).symm⟩
    · dsimp only [E]
      rw [ite_eq_right he]
      intro i
      obtain ⟨j, a, b, ha, hab, hb, _, h⟩ :=
        Route.eval_mapAtCuts (c := c) hline (P.route e) i
      exact ⟨j, a, b, ha, hab, hb, h⟩
  · intro v hv
    change F.symm (P.vertex v) = _
    exact F.injective ((F.apply_symm_apply _).trans ((hcenter v hv).trans (hFcenter v hv).symm))

end Cslib.Complexity.Graph.RotationRecognition
