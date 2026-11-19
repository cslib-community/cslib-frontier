/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary public-API single-vertex transport clients)

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexTransport
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Ordinary MODULE clients of actual single-vertex transport. The star target2+2I aligns with
an intervening leaf, obstructing a single directly aligned horizontal chart. Another client
places a leaf on an OLD nonincident edge interior; only the new route must avoid it. The
bouquet has two indexed loops and one declared name. Coheight isolates and an occupied-target
negative separate the input premises. No internally chosen intermediate point or width is
assigned numerical coordinates.
-/

public section

namespace CslibFrontierTests.PolygonalVertexTransport

open Cslib Polygonal Cslib.Complexity Graph RotationSystem
open Graph.PolygonalDrawing

/-- A public twenty-valent star moves to a genuinely obstructed direct direction. -/
theorem star_twenty_arbitrary_target : ∃ E : PolygonalDrawing (starGraph 20),
    E.IsEmbedding ∧ E.vertex 20 = (2 + 2 * Complex.I) ∧
    (∀ w < 20, E.vertex w = (PolygonalDrawing.star 20).vertex w) ∧
    E.Realizes (PolygonalDrawing.star_isEmbedding 20).rotation ∧
    (∀ e, (E.route e).segments ≤ 25) := by
  let D := PolygonalDrawing.star 20
  have hD := PolygonalDrawing.star_isEmbedding 20
  have htarget : ∀ w ∈ (starGraph 20).vertices, w ≠ 20 →
      (2 + 2 * Complex.I : ℂ) ≠ D.vertex w := by
    intro w _ hw he
    have hi := congrArg Complex.im he
    norm_num [D, PolygonalDrawing.star, starPoint, hw] at hi
  obtain ⟨E, hE, hv, _, ho, hc, _⟩ := hD.exists_single_vertex_transport
    (by decide) 20 (by decide) _ htarget
  refine ⟨E, hE, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_true] using hv 20 (by decide)
  · intro w hw
    have hw' : w ∈ (starGraph 20).vertices := by simp [starGraph]; omega
    simpa only [ite_eq_right (Nat.ne_of_lt hw)] using hv w hw'
  · refine ⟨hE.germ_ne_zero, hE.directions_injective, ?_⟩
    intro x y z hxy hyz hne hne' hne''
    exact (ho x y z hxy hyz hne hne' hne'').trans
      (hD.realizes_rotation.clockwise x y z hxy hyz hne hne' hne'')
  · intro e
    simpa only [D, PolygonalDrawing.star, Route.line, Route.segments] using hc e

-- If the direct target becomes horizontal, the intermediate leaf is coheight too.
example (u : ℂ) (hu : (u * (2 + 2 * Complex.I)).im = 0) :
    (u * (PolygonalDrawing.star 20).vertex 0).im =
      (u * (PolygonalDrawing.star 20).vertex 20).im := by
  norm_num [PolygonalDrawing.star, starPoint, Complex.mul_im] at hu ⊢
  linarith

-- A target on an OLD nonincident route is admitted; that route changes under ambient transport.
example : ∃ E : PolygonalDrawing (starGraph 3), E.IsEmbedding ∧
    E.vertex 0 = (⟨1, 1 / 2⟩ : ℂ) ∧
    (⟨1, 1 / 2⟩ : ℂ) ∈ ((PolygonalDrawing.star 3).route ⟨1, by decide⟩).support ∧
    (⟨1, 1 / 2⟩ : ℂ) ∉ (E.route ⟨1, by decide⟩).support := by
  have hq : ∀ w ∈ (starGraph 3).vertices, w ≠ 0 →
      (⟨1, 1 / 2⟩ : ℂ) ≠ (PolygonalDrawing.star 3).vertex w := by
    intro w _ _ he
    have hi := congrArg Complex.im he
    by_cases hw : w = 3 <;> norm_num [PolygonalDrawing.star, starPoint, hw] at hi
  obtain ⟨E, hE, hv, _, _, _, _⟩ :=
    (PolygonalDrawing.star_isEmbedding 3).exists_single_vertex_transport
      (by decide) 0 (by decide) _ hq
  have hv0 : E.vertex 0 = (⟨1, 1 / 2⟩ : ℂ) := by
    simpa only [ite_true] using hv 0 (by decide)
  refine ⟨E, hE, hv0, ?_, ?_⟩
  · change (⟨1, 1 / 2⟩ : ℂ) ∈
      (Route.line (⟨((1 : ℕ) : ℝ) + 1, 1⟩ : ℂ) 0).support
    apply (Route.mem_support_iff _ _).mpr
    refine ⟨0, 1 / 2, by constructor <;> norm_num, ?_⟩
    rw [Route.eval_line]
    apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module', Complex.smul_re,
      Complex.smul_im]
  · intro hz
    obtain ⟨i, t, ht, he⟩ := (Route.mem_support_iff _ _).mp hz
    obtain ⟨b, _, hb⟩ := hE.vertex_contacts ⟨1, by decide⟩ i t ht 0 (by decide)
      (he.trans hv0.symm)
    cases b <;> norm_num [Dart.vertex, Graph.edgeEndpoint, starGraph] at hb

private def loopGraph : Graph := ⟨[7], [(7, 7), (7, 7)]⟩
private def loopCertificate : RotationCertificate := ⟨[1, 2, 3, 0]⟩
private noncomputable def loopRotation : RotationSystem loopGraph :=
  RotationCertificate.decode loopGraph loopCertificate (by decide)

private noncomputable def loops : PolygonalDrawing loopGraph :=
  PolygonalDrawing.bouquet loopRotation (by decide)

private theorem loops_embedding : loops.IsEmbedding := by
  have hgenus : loopRotation.NumericalGenusZero :=
    (RotationCertificate.verifyEuler_eq_true_iff
      (G := loopGraph) (c := loopCertificate) (by decide)).mp (by decide)
  exact PolygonalDrawing.bouquet_isEmbedding loopRotation (by decide) hgenus (by decide)

-- A real finite certificate supplies the starting bouquet, not an assumed loop embedding.
example : ∃ (D E : PolygonalDrawing loopGraph), D.IsEmbedding ∧ E.IsEmbedding ∧
    E.vertex 7 = D.vertex 7 + Complex.I ∧
    (∀ a : Dart loopGraph, ∃ c : ℝ, 0 < c ∧ E.germ a = c • D.germ a) ∧
    E.Realizes loopRotation := by
  let D := loops
  have hD : D.IsEmbedding := loops_embedding
  have hR : D.Realizes loopRotation := PolygonalDrawing.bouquet_realizes loopRotation (by decide)
  have hq : ∀ w ∈ loopGraph.vertices, w ≠ 7 → D.vertex 7 + Complex.I ≠ D.vertex w := by
    intro w hw hn
    simp only [loopGraph, List.mem_singleton] at hw
    exact (hn hw).elim
  obtain ⟨E, hE, hv, hg, ho, _, _⟩ := hD.exists_single_vertex_transport
    (by decide) 7 (by decide) _ hq
  refine ⟨D, E, hD, hE, ?_, hg, ?_⟩
  · simpa only [ite_true] using hv 7 (by decide)
  · refine ⟨hE.germ_ne_zero, hE.directions_injective, ?_⟩
    intro x y z hxy hyz hne hne' hne''
    exact (ho x y z hxy hyz hne hne' hne'').trans
      (hR.clockwise x y z hxy hyz hne hne' hne'')

-- The actual closed bouquet selects the literal original when its target is unchanged.
example : ∃ E : PolygonalDrawing loopGraph, E.IsEmbedding ∧ E = loops := by
  have hq : ∀ w ∈ loopGraph.vertices, w ≠ 7 → loops.vertex 7 ≠ loops.vertex w := by
    intro w hw hne
    exact loops_embedding.vertex_ne (by decide) hw (Ne.symm hne)
  obtain ⟨E, hE, _, _, _, _, hid⟩ := loops_embedding.exists_single_vertex_transport
    (by decide) 7 (by decide) (loops.vertex 7) hq
  exact ⟨E, hE, hid rfl⟩

-- Two coheight isolates are admitted; no direction or width comes from the caller.
example : ∃ E : PolygonalDrawing ⟨[7, 8], []⟩, E.IsEmbedding ∧
    E.vertex 7 = (8 + Complex.I) ∧ E.vertex 8 = (8 : ℂ) := by
  have hq : ∀ w ∈ ([7, 8] : List ℕ), w ≠ 7 →
      (8 + Complex.I : ℂ) ≠ (PolygonalDrawing.points [7, 8]).vertex w := by
    intro w _ _ he
    have hi := congrArg Complex.im he
    norm_num [PolygonalDrawing.points] at hi
  obtain ⟨E, hE, hv, _, _, _, _⟩ :=
    (PolygonalDrawing.points_isEmbedding [7, 8]).exists_single_vertex_transport
      (by simp [Graph.incidenceVertices]) 7 (by simp) _ hq
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [ite_true] using hv 7 (by simp)
  · have h := hv 8 (by simp)
    norm_num [PolygonalDrawing.points] at h
    exact h

-- Occupying the other CURRENT declared vertex is mathematically impossible while fixing it.
example : ¬∃ E : PolygonalDrawing ⟨[7, 8], []⟩,
    E.IsEmbedding ∧ E.vertex 7 = (8 : ℂ) ∧ E.vertex 8 = (8 : ℂ) := by
  rintro ⟨E, hE, h7, h8⟩
  have hn : (7 : ℕ) = 8 := hE.vertices_injective (by simp) (by simp) (h7.trans h8.symm)
  norm_num at hn

private def triangle : Route := ((Route.line 0 1).append Complex.I).append 0

-- A closed route retains both outgoing tags; the linear chart law is genuinely ALL-real.
example (u : ℂ) :
    (Route.mulComplex u triangle).germ false = u ∧
    (Route.mulComplex u triangle).germ true = u * Complex.I ∧
    ∀ (i : Fin triangle.segments) (t : ℝ),
      (Route.mulComplex u triangle).eval i t = u * triangle.eval i t := by
  refine ⟨?_, ?_, fun i t => Route.eval_mulComplex u triangle i t⟩
  · rw [Route.germ_mulComplex]
    simp only [triangle,Route.germ_append,Bool.false_eq_true,↓reduceIte]
    have h : (Route.line 0 1).germ false = 1 := by
      change (1 : ℂ) - 0 = 1
      exact sub_zero 1
    rw [h,mul_one]
  · rw [Route.germ_mulComplex]
    simp only [triangle,Route.germ_append,↓reduceIte]
    have h : ((Route.line 0 1).append Complex.I).finish = Complex.I :=
      Route.endpoint_append _ _ true
    rw [h,sub_zero]

-- The nonzero factor is necessary for simplicity, not for the total constructor/support law.
example : ¬(Route.mulComplex 0 (Route.line 0 1)).IsSimple := by
  intro hp
  exact hp.segment_ne 0 (by simp [Route.mulComplex, Route.line])

-- Conjugation is not the inverse of a similarity of nonunit norm.
example : starRingEnd ℂ (2 : ℂ) * ((2 : ℂ) * 1) ≠ (1 : ℂ) := by
  rw [map_ofNat]
  norm_num

end CslibFrontierTests.PolygonalVertexTransport
