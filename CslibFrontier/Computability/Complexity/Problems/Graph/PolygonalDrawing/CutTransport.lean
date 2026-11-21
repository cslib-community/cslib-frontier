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
    refine ⟨j, AffineMap.lineMap a b t, ?_, h t ht⟩
    exact (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).lineMap_mem
      ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ ht
  refine ⟨?_, hsimple, ?_, ?_⟩
  · intro u hu v hv he
    rw [hvertex u, hvertex v] at he
    exact hD.vertices_injective hu hv (hinj he)
  · intro e i t ht v hv he
    obtain ⟨j, u, hu, hj, hend⟩ := hsample e i t ht
    rw [hj, hvertex v] at he
    obtain ⟨b, hb, hbv⟩ := hD.vertex_contacts e j u hu v hv (hinj he)
    exact ⟨b, (hend b).mpr hb, hbv⟩
  · intro e f hef i j s t hs ht he
    obtain ⟨k, u, hu, hk, hleft⟩ := hsample e i s hs
    obtain ⟨l, v, hv, hl, hright⟩ := hsample f j t ht
    rw [hk, hl] at he
    obtain ⟨b, c, hb, hc, hbc⟩ := hD.edge_contacts e f hef k l u v hu hv (hinj he)
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
  refine hD.of_route_map hinj (fun _ => rfl) (fun e => (hD.simple e).mapAtCuts hF hinj) ?_
  intro e i
  obtain ⟨j, a, b, ha, hab, hb, _, h⟩ := Route.eval_mapAtCuts hF (D.route e) i
  exact ⟨j, a, b, ha, hab, hb, h⟩

end Interpolation

end Cslib.Complexity.Graph.PolygonalDrawing
