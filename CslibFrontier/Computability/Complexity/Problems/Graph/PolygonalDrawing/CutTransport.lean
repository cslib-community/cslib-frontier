/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.CutTransport
import Mathlib.Analysis.Convex.Basic

/-!
# Transporting polygonal drawings across coordinate cuts

Split every indexed route at a common finite set of affine coordinate levels, then map the
vertices and route samples by the same plane map. Injectivity and preservation of interpolation
between cuts ensure that the resulting polygonal drawing is an embedding whenever the original
was embedded.

The contact argument uses the source segment and parameter of each evaluation. In particular,
it preserves the two endpoint tags of a loop and the identities of parallel edge occurrences.
Repeated refinement at affine zero sets, including nonparallel lines, leaves the drawing's
vertex positions and route supports fixed.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- Preserve an embedding when an injective plane map acts on the vertices, every image route
is simple, and every image segment has a source subsegment with matching tagged endpoints. -/
theorem IsEmbedding.of_route_map {G : Graph} {D E : PolygonalDrawing G}
    (hD : D.IsEmbedding) {F : ℂ → ℂ} (hinj : Function.Injective F)
    (hvertex : ∀ v, E.vertex v = F (D.vertex v))
    (hsimple : ∀ e, (E.route e).IsSimple)
    (hsegment : ∀ e (i : Fin (E.route e).segments),
      ∃ (j : Fin (D.route e).segments) (a b : ℝ), 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (E.route e).eval i t = F ((D.route e).eval j (AffineMap.lineMap a b t)) ∧
          ∀ c : Bool, (E.route e).AtEnd i t c ↔
            (D.route e).AtEnd j (AffineMap.lineMap a b t) c) : E.IsEmbedding := by
  have hsample (e) (i : Fin (E.route e).segments) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ∃ (j : Fin (D.route e).segments) (u : ℝ), u ∈ Set.Icc 0 1 ∧
        (E.route e).eval i t = F ((D.route e).eval j u) ∧
        ∀ c : Bool, (E.route e).AtEnd i t c ↔ (D.route e).AtEnd j u c := by
    obtain ⟨j, a, b, ha, hab, hb, h⟩ := hsegment e i
    exact ⟨j, AffineMap.lineMap a b t, (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).lineMap_mem
      ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ ht, h t ht⟩
  refine ⟨fun u hu v hv he => hD.vertices_injective hu hv (hinj (by rwa [← hvertex, ← hvertex])),
    hsimple, fun e i t ht v hv he => ?_, fun e f hef i j s t hs ht he => ?_⟩
  · obtain ⟨j, u, hu, hj, hend⟩ := hsample e i t ht
    obtain ⟨b, hb, hbv⟩ := hD.vertex_contacts e j u hu v hv (hinj (by rwa [← hj, ← hvertex]))
    exact ⟨b, (hend b).mpr hb, hbv⟩
  · obtain ⟨k, u, hu, hk, hleft⟩ := hsample e i s hs
    obtain ⟨l, v, hv, hl, hright⟩ := hsample f j t ht
    obtain ⟨b, c, hb, hc, hbc⟩ :=
      hD.edge_contacts e f hef k l u v hu hv (hinj (by rwa [← hk, ← hl]))
    exact ⟨b, c, (hleft b).mpr hb, (hright c).mpr hc, hbc⟩

section Interpolation

variable {S : Finset ℝ} {c : ℂ →ᵃ[ℝ] ℝ} {F : ℂ → ℂ}
  (hF : ∀ a b : ℂ,
    (∀ y ∈ S, y ∉ Set.Ioo (min (c a) (c b)) (max (c a) (c b))) →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F (AffineMap.lineMap a b t) = AffineMap.lineMap (F a) (F b) t)

/-- Map all vertex coordinates and join the mapped samples of each indexed route.
The interpolation condition ensures the tagged endpoints agree with the mapped vertices. -/
@[expose] noncomputable def mapAtCuts {G : Graph} (D : PolygonalDrawing G) :
    PolygonalDrawing G where
  vertex := fun v => F (D.vertex v)
  route := fun e => (D.route e).mapAtCuts S c F
  endpoint_eq := fun e b => (Route.endpoint_mapAtCuts hF (D.route e) b).trans
    (congrArg F (D.endpoint_eq e b))

include hF in
/-- An injective map that preserves straight interpolation between cuts transports an entire
polygonal embedding, with the original indexed graph and endpoint tags. -/
protected theorem IsEmbedding.mapAtCuts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hinj : Function.Injective F) : (D.mapAtCuts hF).IsEmbedding := by
  refine hD.of_route_map hinj (fun _ => rfl) (fun e => (hD.simple e).mapAtCuts hF hinj)
    fun e i => ?_
  obtain ⟨j, a, b, ha, hab, hb, _, h⟩ := Route.eval_mapAtCuts hF (D.route e) i
  exact ⟨j, a, b, ha, hab, hb, h⟩

end Interpolation

private theorem subsegment_avoids_wall (p : Route) (i : Fin p.segments) (f : ℂ →ᵃ[ℝ] ℝ)
    {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hwall : 0 ∉ Set.Ioo (min (f (p.point i.castSucc)) (f (p.point i.succ)))
      (max (f (p.point i.castSucc)) (f (p.point i.succ)))) :
    0 ∉ Set.Ioo (min (f (p.eval i a)) (f (p.eval i b)))
      (max (f (p.eval i a)) (f (p.eval i b))) := by
  have hwithin {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
      f (p.eval i t) ∈ Set.uIcc (f (p.point i.castSucc)) (f (p.point i.succ)) := by
    rw [Route.eval, AffineMap.apply_lineMap, ← segment_eq_uIcc]
    exact lineMap_mem_segment ℝ _ _ ht
  exact fun h => hwall ⟨(le_min (hwithin ha).1 (hwithin hb).1).trans_lt h.1,
    h.2.trans_le (max_le (hwithin ha).2 (hwithin hb).2)⟩

/-- Refine an embedding at finitely many affine zero sets. All vertex positions and route
supports are preserved. No zero set of the given family strictly separates the endpoints of
an output segment, even when the lines are nonparallel or pass through existing nodes. -/
theorem IsEmbedding.exists_wall_refinement {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (walls : List (ℂ →ᵃ[ℝ] ℝ)) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.vertex = D.vertex ∧
      (∀ e, (E.route e).support = (D.route e).support) ∧
      ∀ e (i : Fin (E.route e).segments) f, f ∈ walls →
        0 ∉ Set.Ioo (min (f ((E.route e).point i.castSucc)) (f ((E.route e).point i.succ)))
          (max (f ((E.route e).point i.castSucc)) (f ((E.route e).point i.succ))) := by
  induction walls with
  | nil =>
    exact ⟨D, hD, rfl, fun _ => rfl, fun _ _ _ hf => (List.not_mem_nil hf).elim⟩
  | cons f walls ih =>
    obtain ⟨P, hP, hpoints, hsupport, hwall⟩ := ih
    have hline (z w : ℂ)
        (_ : ∀ y ∈ ({0} : Finset ℝ), y ∉ Set.Ioo (min (f z) (f w)) (max (f z) (f w)))
        (t : ℝ) (_ : t ∈ Set.Icc 0 1) :
        id (AffineMap.lineMap z w t) = AffineMap.lineMap (id z) (id w) t := rfl
    let E := P.mapAtCuts (S := {0}) (c := f) (F := id) hline
    refine ⟨E, hP.mapAtCuts (c := f) hline Function.injective_id, hpoints, ?_, ?_⟩
    · intro e
      have h := Route.support_mapAtCuts (c := f) hline (P.route e)
      change (E.route e).support = id '' (P.route e).support at h
      simpa only [Set.image_id, hsupport e] using h
    · intro e
      let q := (P.route e).mapAtCuts {0} f id
      change ∀ (i : Fin q.segments) g, g ∈ f :: walls →
        0 ∉ Set.Ioo (min (g (q.point i.castSucc)) (g (q.point i.succ)))
          (max (g (q.point i.castSucc)) (g (q.point i.succ)))
      intro i g hg
      obtain ⟨j, a, b, ha, hab, hb, hcut, h⟩ :=
        Route.eval_mapAtCuts (S := {0}) (c := f) (F := id) hline (P.route e) i
      have hleft : q.point i.castSucc = (P.route e).eval j a := calc
        _ = q.eval i 0 := (AffineMap.lineMap_apply_zero _ _).symm
        _ = (P.route e).eval j (AffineMap.lineMap a b 0) := (h 0 ⟨le_rfl, zero_le_one⟩).1
        _ = _ := congrArg ((P.route e).eval j) (AffineMap.lineMap_apply_zero a b)
      have hright : q.point i.succ = (P.route e).eval j b := calc
        _ = q.eval i 1 := (AffineMap.lineMap_apply_one _ _).symm
        _ = (P.route e).eval j (AffineMap.lineMap a b 1) := (h 1 ⟨zero_le_one, le_rfl⟩).1
        _ = _ := congrArg ((P.route e).eval j) (AffineMap.lineMap_apply_one a b)
      rw [hleft, hright]
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hcut 0 (Finset.mem_singleton_self 0)
      · exact subsegment_avoids_wall (P.route e) j g ⟨ha, hab.le.trans hb⟩
          ⟨ha.trans hab.le, hb⟩ (hwall e j g hg)

/-- An injective plane map that preserves straight interpolation between a finite family of
affine zero sets takes an embedded polygonal drawing to another one. In the output, each
vertex is the mapped source vertex and each route support is the image of its source support. -/
theorem IsEmbedding.exists_image_across_walls {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (walls : List (ℂ →ᵃ[ℝ] ℝ)) {F : ℂ → ℂ}
    (hinj : Function.Injective F)
    (hline : ∀ a b : ℂ, (∀ f ∈ walls, 0 ∉ Set.Ioo (min (f a) (f b)) (max (f a) (f b))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        F (AffineMap.lineMap a b t) = AffineMap.lineMap (F a) (F b) t) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.vertex = F ∘ D.vertex ∧
      ∀ e, (E.route e).support = F '' (D.route e).support := by
  obtain ⟨P, hP, hvertex, hsupport, hcuts⟩ := hD.exists_wall_refinement walls
  let E : PolygonalDrawing G :=
    { vertex := F ∘ P.vertex
      route := fun e => ⟨(P.route e).bends, F ∘ (P.route e).point⟩
      endpoint_eq := fun e =>
        Bool.rec (congrArg F (P.endpoint_eq e false)) (congrArg F (P.endpoint_eq e true)) }
  have heval (e : Fin G.edges.length) (i : Fin (P.route e).segments)
      (t : ℝ) (ht : t ∈ Set.Icc 0 1) : (E.route e).eval i t = F ((P.route e).eval i t) :=
    (hline _ _ (hcuts e i) t ht).symm
  have hsimple (e : Fin G.edges.length) : (E.route e).IsSimple := fun i j s t hs ht he =>
    hP.simple e i j s t hs ht (hinj ((heval e i s hs).symm.trans (he.trans (heval e j t ht))))
  refine ⟨E, hP.of_route_map hinj (fun _ => rfl) hsimple (fun e i =>
    ⟨i, 0, 1, le_rfl, zero_lt_one, le_rfl, fun t ht => by
      rw [show AffineMap.lineMap (0 : ℝ) 1 t = t by simp [AffineMap.lineMap_apply_ring]]
      exact ⟨heval e i t ht, fun _ => Iff.rfl⟩⟩),
    congrArg (F ∘ ·) hvertex, fun e => ?_⟩
  rw [← hsupport e]
  ext z
  simp only [Route.mem_support_iff, Set.mem_image]
  constructor
  · rintro ⟨i, t, ht, rfl⟩
    exact ⟨_, ⟨i, t, ht, rfl⟩, (heval e i t ht).symm⟩
  · rintro ⟨_, ⟨i, t, ht, rfl⟩, rfl⟩
    exact ⟨i, t, ht, heval e i t ht⟩

end Cslib.Complexity.Graph.PolygonalDrawing
