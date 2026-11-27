/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceSpokes
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEmbedding
import CslibFrontier.Foundations.Geometry.Polygonal.Join
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import Mathlib.Tactic.FinCases

/-!
# Installing reference directions in the recognition subdivision

For a polygonal embedding realizing the prescribed word at each fixed vertex, sufficiently
small disjoint cut disks let us replace the end pieces at fixed vertices by reference spokes.
All subdivision vertices, middle pieces, and end pieces at free vertices are retained.
This is original geometry.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal

private abbrev SubEdge (I : FixedRotationInput) := Fin (subdivisionGraph I).edges.length

private def endDart (I : FixedRotationInput) (e : SubEdge I) : Dart I.graph :=
  ((subdivisionEdgeIndex I e).original, decide ((subdivisionEdgeIndex I e).piece = 2))

private theorem endDart_subdivisionDart (I : FixedRotationInput) (d : Dart I.graph) :
    endDart I (subdivisionDart I d).1 = d := by
  rcases d with ⟨e, b⟩
  rw [endDart, subdivisionEdgeIndex_subdivisionDart]
  cases b <;> rfl

private theorem subdivisionDart_endDart (I : FixedRotationInput) (e : SubEdge I)
    (h : (subdivisionEdgeIndex I e).piece ≠ 1) : (subdivisionDart I (endDart I e)).1 = e := by
  apply Fin.ext
  have he := subdivisionEdgeIndex_val I e
  change 3 * (subdivisionEdgeIndex I e).original.val +
    (if decide ((subdivisionEdgeIndex I e).piece = 2) then 2 else 0) = e.val
  rw [he]
  generalize hk : (subdivisionEdgeIndex I e).piece = k at h ⊢
  fin_cases k <;> first | rfl | exact (h rfl).elim

private def orientSpoke (p : Route) (b : Bool) : Route := if b then p.reverse else p

private theorem orientSpoke_ends (p : Route) (b : Bool) :
    (orientSpoke p b).endpoint b = p.start ∧
      (orientSpoke p b).endpoint (!b) = p.finish := by
  cases b <;> first | exact ⟨rfl, rfl⟩ | exact ⟨p.endpoint_reverse true, p.endpoint_reverse false⟩

private theorem atEnd_of_eval_eq {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish)
    (k : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (b : Bool)
    (h : p.eval k t = p.endpoint b) : p.AtEnd k t b := by
  have he := p.eval_near_end b 0
  simp only [zero_smul, add_zero] at he
  have hpos := hp.position_eq_of_eval_eq hne k (p.endSegment b) ht
    (Route.endTime_mem b ⟨le_rfl, zero_le_one⟩) (h.trans he.symm)
  simpa only [Route.AtEnd, p.position_near_end, sub_zero] using hpos

/-- Install the reference germs at every prescribed vertex of the actual twice subdivision.
The original directions at free vertices retain their old end pieces. The retained drawing
and the modified drawing have identical vertex points and middle routes. -/
theorem exists_subdivision_embedding_with_reference_spokes {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding)
    {r : RotationSystem I.graph} (hReal : D.Realizes r) (hfixed : Realizes I r) :
    ∃ ε > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 ε,
      ∃ E F : PolygonalDrawing (subdivisionGraph I), E.IsEmbedding ∧ F.IsEmbedding ∧
        F.vertex = E.vertex ∧
        (∀ v ∈ I.graph.vertices, F.vertex v = D.vertex v) ∧
        (∀ d : Dart I.graph, F.vertex (subdivisionDart I d).reverse.vertex = D.cutPort ρ d) ∧
        (∀ e, (subdivisionEdgeIndex I e).piece = 1 → F.route e = E.route e) ∧
        (∀ d : Dart I.graph, I.orders.getD d.vertex none = none →
          F.route (subdivisionDart I d).1 = E.route (subdivisionDart I d).1 ∧
            F.direction (subdivisionDart I d) = D.direction d) ∧
        ∀ d : Dart I.graph, (I.orders.getD d.vertex none).isSome →
          ∃ a > (0 : ℝ), F.germ (subdivisionDart I d) =
            a • (referenceDrawing I).germ (subdivisionDart I d) := by
  classical
  obtain ⟨ε, hε, hsub⟩ := exists_subdivision_embedding_in_disjoint_disks hI D hD
  refine ⟨ε, hε, fun ρ hρ => ?_⟩
  obtain ⟨hdisj, E, hE, hcenter, hdir, hport, hendSupport, hmiddle⟩ := hsub ρ hρ
  let fixed (v : ℕ) : Prop := (I.orders.getD v none).isSome
  have hf (v : ℕ) (hv : fixed v) :
      ∃ T : {d : Dart I.graph // d.vertex = v} → Route,
        (∀ d, (T d).start = D.vertex v ∧ (T d).finish = D.cutPort ρ d.val ∧
          (∃ a > (0 : ℝ), (T d).germ false =
            a • (referenceDrawing I).germ (subdivisionDart I d.val)) ∧
          (T d).IsSimple ∧ (T d).support \ Metric.ball (D.vertex v) ρ = {D.cutPort ρ d.val}) ∧
        Pairwise (fun d e => (T d).support ∩ (T e).support = {D.vertex v}) := by
    cases hw : I.orders.getD v none with
    | none => exact (Option.not_isSome_iff_eq_none.mpr hw hv).elim
    | some word => exact exists_reference_spokes_at_cutPorts hI hD hReal hfixed hρ.1 hw
  choose T hT hTpair using hf
  let spoke (d : Dart I.graph) (hd : fixed d.vertex) := T d.vertex hd ⟨d, rfl⟩
  have hspoke (d : Dart I.graph) (hd : fixed d.vertex) := hT d.vertex hd ⟨d, rfl⟩
  have horig (d : Dart I.graph) : d.vertex ∈ I.graph.vertices :=
    I.graph.edgeEndpoint_mem (fun _ he => by
      rw [hI.1]
      simpa only [List.mem_range] using hI.edge_endpoints_lt he) d.1.isLt d.2
  let changed (e : SubEdge I) : Prop :=
    (subdivisionEdgeIndex I e).piece ≠ 1 ∧ fixed (endDart I e).vertex
  have hchange (d : Dart I.graph) : changed (subdivisionDart I d).1 ↔ fixed d.vertex := by
    rcases d with ⟨e, _ | _⟩ <;>
      simp [changed, endDart_subdivisionDart, subdivisionEdgeIndex_subdivisionDart]
  let route (e : SubEdge I) := if he : changed e then
    orientSpoke (spoke (endDart I e) he.2) (endDart I e).2 else E.route e
  have hkeep (e : SubEdge I) (he : ¬ changed e) : route e = E.route e := dite_eq_right he
  have hreplace (d : Dart I.graph) (hd : fixed d.vertex) :
      route (subdivisionDart I d).1 = orientSpoke (spoke d hd) d.2 := by
    simp only [route, dite_eq_left ((hchange d).mpr hd)]
    have hcongr : ∀ d' (hd' : fixed d'.vertex), d' = d →
        orientSpoke (spoke d' hd') d'.2 = orientSpoke (spoke d hd) d.2
      | _, _, rfl => rfl
    exact hcongr _ _ (endDart_subdivisionDart I d)
  have hends (d : Dart I.graph) (hd : fixed d.vertex) (b : Bool) :
      (route (subdivisionDart I d).1).endpoint b =
        E.vertex (Dart.vertex ((subdivisionDart I d).1, b)) := by
    rw [hreplace d hd]
    obtain ⟨hs, ht, _, _, _⟩ := hspoke d hd
    by_cases hb : b = d.2
    · rw [hb, (orientSpoke_ends (spoke d hd) d.2).1, hs]
      exact (hcenter _ (horig d)).symm.trans
        (congrArg E.vertex (subdivisionDart_endpoints I d).1.symm)
    · rw [Bool.eq_not.mpr hb, (orientSpoke_ends (spoke d hd) d.2).2, ht]
      exact (hport d).symm
  let F : PolygonalDrawing (subdivisionGraph I) := {
    vertex := E.vertex
    route := route
    endpoint_eq := fun e b => by
      by_cases he : changed e
      · simpa only [subdivisionDart_endDart I e he.1] using hends (endDart I e) he.2 b
      · rw [hkeep e he, E.endpoint_eq] }
  have hdecl (e : SubEdge I) (b : Bool) :
      Dart.vertex (e, b) ∈ (subdivisionGraph I).vertices :=
    ((referenceOrder_enumerates hI).2 _).mp ((subdivision_endpoint_spec hI e).1 b)
  have hnames (v : ℕ) (hv : v ∈ (subdivisionGraph I).vertices) :
      v ∈ I.graph.vertices ∨ ∃ d, v = (subdivisionDart I d).reverse.vertex := by
    by_cases hsmall : v < I.graph.vertices.length
    · exact Or.inl (hI.1.symm ▸ List.mem_range.mpr hsmall)
    · have hbound : v < I.graph.vertices.length + 2 * I.graph.edges.length := by
        simpa only [subdivisionGraph, subdivisionSize, List.mem_range] using hv
      let d := (Dart.indexEquiv I.graph).symm ⟨v - I.graph.vertices.length, by omega⟩
      have hi : d.index = v - I.graph.vertices.length :=
        congrArg Fin.val ((Dart.indexEquiv I.graph).apply_symm_apply ⟨_, by omega⟩)
      exact Or.inr ⟨d, by rw [(subdivisionDart_endpoints I d).2, hi]; omega⟩
  have hcf (d : Dart I.graph) : ‖D.cutPort ρ d - D.vertex d.vertex‖ = ρ := by
    simpa only [dist_eq_norm] using hD.dist_cutPort hρ.1.le d
  have hsupp (d : Dart I.graph) (hd : fixed d.vertex) :
      (F.route (subdivisionDart I d).1).support = (spoke d hd).support := by
    change (route (subdivisionDart I d).1).support = _
    rw [hreplace d hd]
    cases d.2 <;> simp [orientSpoke]
  have hchanged_supp {e : SubEdge I} (he : changed e) :
      (F.route e).support = (spoke (endDart I e) he.2).support := by
    rw [← hsupp _ he.2, subdivisionDart_endDart I e he.1]
  have hbound (d : Dart I.graph) (hd : fixed d.vertex) {x : ℂ}
      (hx : x ∈ (spoke d hd).support) (ho : x ∉ Metric.ball (D.vertex d.vertex) ρ) :
      x = D.cutPort ρ d := by
    obtain ⟨_, _, _, _, hb⟩ := hspoke d hd
    exact Set.mem_singleton_iff.mp (hb ▸ (show x ∈ _ \ _ from ⟨hx, ho⟩))
  have hportClosed (d : Dart I.graph) : D.cutPort ρ d ∈ Metric.closedBall (D.vertex d.vertex) ρ :=
    Metric.mem_closedBall.mpr ((dist_eq_norm _ _).trans (hcf d)).le
  have hportOutside (d : Dart I.graph) :
      D.cutPort ρ d ∉ Metric.ball (D.vertex d.vertex) ρ := by
    simp [Metric.mem_ball, dist_eq_norm, hcf]
  have hclosed (d : Dart I.graph) (hd : fixed d.vertex) :
      (spoke d hd).support ⊆ Metric.closedBall (D.vertex d.vertex) ρ := fun x hx =>
    if he : x ∈ Metric.ball (D.vertex d.vertex) ρ then Metric.ball_subset_closedBall he
    else hbound d hd hx he ▸ hportClosed d
  have hsimple (e : SubEdge I) : (F.route e).IsSimple := by
    change (route e).IsSimple
    by_cases he : changed e
    · obtain ⟨_, _, _, hs, _⟩ := hspoke (endDart I e) he.2
      simp only [route, dite_eq_left he, orientSpoke]
      split <;> first | exact hs.reverse | exact hs
    · exact (hkeep e he).symm ▸ hE.simple e
  have hvertex_end (e : SubEdge I) {v : ℕ} (hv : v ∈ (subdivisionGraph I).vertices)
      (hx : E.vertex v ∈ (F.route e).support) : ∃ b, Dart.vertex (e, b) = v := by
    by_cases he : changed e
    · let d := endDart I e
      rw [hchanged_supp he] at hx
      have hxball := hclosed d he.2 hx
      rw [← subdivisionDart_endDart I e he.1]
      rcases hnames v hv with hvOld | ⟨a, ha⟩
      · have hsame : d.vertex = v := by_contra fun hne =>
          Set.disjoint_left.mp (hdisj _ (horig d) _ hvOld hne) hxball
            (hcenter v hvOld ▸ Metric.mem_closedBall_self hρ.1.le)
        exact ⟨d.2, (subdivisionDart_endpoints I d).1.trans hsame⟩
      · rw [ha, hport a] at hx hxball
        have hsame : a.vertex = d.vertex := by_contra fun hne =>
          Set.disjoint_left.mp (hdisj _ (horig a) _ (horig d) hne) (hportClosed a) hxball
        have had := hD.cutPort_injective hρ.1 a d hsame
          (hbound d he.2 hx (hsame ▸ hportOutside a))
        refine ⟨!d.2, ?_⟩
        exact (congrArg (fun x => (subdivisionDart I x).reverse.vertex) had.symm).trans ha.symm
    · obtain ⟨k, t, ht, hval⟩ := ((E.route e).mem_support_iff _).mp (by rwa [← hkeep e he])
      exact (hE.vertex_contacts e k t ht v hv hval).imp fun _ => And.right
  have hvertex : ∀ e (k : Fin (F.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      ∀ v ∈ (subdivisionGraph I).vertices, (F.route e).eval k t = F.vertex v →
      ∃ b, (F.route e).AtEnd k t b ∧ Dart.vertex (e, b) = v := by
    intro e k t ht v hv heq
    obtain ⟨b, hb⟩ := hvertex_end e hv (heq ▸ (F.route e).at_mem_support k ht)
    have hopen : (F.route e).start ≠ (F.route e).finish := by
      change (F.route e).endpoint false ≠ (F.route e).endpoint true
      rw [F.endpoint_eq, F.endpoint_eq]
      exact hE.vertex_ne (hdecl e false) (hdecl e true) (subdivision_endpoint_spec hI e).2
    exact ⟨b, atEnd_of_eval_eq (hsimple e) hopen k ht b
      (heq.trans (hb ▸ (F.endpoint_eq e b).symm)), hb⟩
  have hsameSpokes (d a : Dart I.graph) (hd : fixed d.vertex) (ha : fixed a.vertex)
      (hne : d ≠ a) {x : ℂ} (hx : x ∈ (spoke d hd).support) (hy : x ∈ (spoke a ha).support) :
      x = D.vertex d.vertex := by
    have hsame : a.vertex = d.vertex := by_contra fun hn =>
      Set.disjoint_left.mp (hdisj _ (horig a) _ (horig d) hn) (hclosed a ha hy) (hclosed d hd hx)
    have hcoh : ∀ v (hv : a.vertex = v) (h₂ : fixed v), spoke a ha = T v h₂ ⟨a, hv⟩
      | _, rfl, _ => rfl
    have he : (⟨d, rfl⟩ : {b : Dart I.graph // b.vertex = d.vertex}) ≠ ⟨a, hsame⟩ :=
      fun hh => hne (congrArg Subtype.val hh)
    exact Set.mem_singleton_iff.mp
      (hTpair _ hd he ▸ Set.mem_inter hx (hcoh _ hsame hd ▸ hy))
  have hmeetKept (d : Dart I.graph) (hd : fixed d.vertex) (e : SubEdge I)
      (he : ¬ changed e) {x : ℂ}
      (hx : x ∈ (spoke d hd).support) (hy : x ∈ (F.route e).support) :
      x = D.cutPort ρ d := by
    change x ∈ (route e).support at hy
    rw [hkeep e he] at hy
    by_cases hm : (subdivisionEdgeIndex I e).piece = 1
    · obtain ⟨b, hb, hval⟩ := hmiddle e hm _ (horig d) x hy (hclosed d hd hx)
      exact hbound d hd hx (by
        rw [hval, ← hb]
        exact hportOutside ((subdivisionEdgeIndex I e).original, b))
    · let a := endDart I e
      have heq : (subdivisionDart I a).1 = e := subdivisionDart_endDart I e hm
      have hfa : ¬ fixed a.vertex := fun h => he ⟨hm, h⟩
      have hdne : d.vertex ≠ a.vertex := fun h => hfa (h ▸ hd)
      rw [← heq] at hy
      exact (Set.disjoint_left.mp (hdisj _ (horig d) _ (horig a) hdne)
        (hclosed d hd hx) (hendSupport a hy)).elim
  have hmeet (e f : SubEdge I) (hne : e ≠ f) (x : ℂ)
      (hx : x ∈ (F.route e).support) (hy : x ∈ (F.route f).support) :
      ∃ v ∈ (subdivisionGraph I).vertices, x = F.vertex v := by
    by_cases he : changed e
    · let d := endDart I e
      rw [hchanged_supp he] at hx
      by_cases hf : changed f
      · let a := endDart I f
        rw [hchanged_supp hf] at hy
        have hda : d ≠ a := fun heq => hne <|
          (subdivisionDart_endDart I e he.1).symm.trans
            ((congrArg (fun x => (subdivisionDart I x).1) heq).trans
              (subdivisionDart_endDart I f hf.1))
        exact ⟨d.vertex, (subdivisionDart_endpoints I d).1 ▸ hdecl _ _,
          (hsameSpokes d a he.2 hf.2 hda hx hy).trans (hcenter _ (horig d)).symm⟩
      · exact ⟨(subdivisionDart I d).reverse.vertex, hdecl _ _,
          (hmeetKept d he.2 f hf hx hy).trans (hport d).symm⟩
    · by_cases hf : changed f
      · let a := endDart I f
        rw [hchanged_supp hf] at hy
        exact ⟨(subdivisionDart I a).reverse.vertex, hdecl _ _,
          (hmeetKept a hf.2 e he hy hx).trans (hport a).symm⟩
      · obtain ⟨i, s, hs, hxs⟩ := ((E.route e).mem_support_iff x).mp (by rwa [← hkeep e he])
        obtain ⟨j, t, ht, hxt⟩ := ((E.route f).mem_support_iff x).mp (by rwa [← hkeep f hf])
        obtain ⟨b, _, hb, _, _⟩ := hE.edge_contacts e f hne i j s t hs ht (hxs.trans hxt.symm)
        exact ⟨Dart.vertex (e, b), hdecl e b, hxs.symm.trans
          (((E.route e).at_eq_endpoint i hs b hb).trans (E.endpoint_eq e b))⟩
  have hEmbed : F.IsEmbedding := ⟨hE.vertices_injective, hsimple, hvertex,
    fun e f hne i j s t hs ht heq => by
      obtain ⟨v, hv, hvx⟩ := hmeet e f hne _ ((F.route e).at_mem_support i hs)
        (heq.symm ▸ (F.route f).at_mem_support j ht)
      obtain ⟨b, hb, hbv⟩ := hvertex e i s hs v hv hvx
      obtain ⟨c, hc, hcv⟩ := hvertex f j t ht v hv (heq.symm.trans hvx)
      exact ⟨b, c, hb, hc, hbv.trans hcv.symm⟩⟩
  refine ⟨E, F, hE, hEmbed, rfl, hcenter, hport, fun e he => hkeep e (fun h => h.1 he),
    fun d hd => ?_, fun d hd => ?_⟩
  · have hne : ¬ changed (subdivisionDart I d).1 :=
      fun he => Option.not_isSome_iff_eq_none.mpr hd ((hchange d).mp he)
    refine ⟨hkeep _ hne, ?_⟩
    simpa only [PolygonalDrawing.direction, PolygonalDrawing.germ, F, hkeep _ hne] using hdir d
  · obtain ⟨_, _, ⟨a, ha, hg⟩, _, _⟩ := hspoke d hd
    refine ⟨a, ha, ?_⟩
    change (route (subdivisionDart I d).1).germ d.2 = _
    rw [hreplace d hd]
    cases d.2 <;> simpa [orientSpoke] using hg

end Cslib.Complexity.Graph.RotationRecognition
