/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary clients of actual local vertex relocation)

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Relocation
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.EmbeddingNecessity
import CslibFrontier.Foundations.Geometry.Polygonal.NoncrossingOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Ordinary MODULE clients use only public APIs. The off-center star and loop tests really
move a named point. No numerical value of the internally selected radius is assumed.
These examples check the actual relocation through ordinary public imports.
-/

public section

namespace CslibFrontierTests.PolygonalVertexRelocation

open Cslib Polygonal Cslib.Complexity Graph RotationSystem
open Graph.PolygonalDrawing

private theorem offset_mem {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    z + (ρ / 4 : ℝ) ∈ Metric.ball z ρ := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ρ / 4)]
  linarith

private theorem offset_ne {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) : z + (ρ / 4 : ℝ) ≠ z := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  linarith

private theorem realizes_transport {G : Graph} {D D' : PolygonalDrawing G}
    (hD' : D'.IsEmbedding) {r : RotationSystem G} (hR : D.Realizes r)
    (horder : ∀ x y z : Dart G, x.vertex = y.vertex → y.vertex = z.vertex →
      x ≠ y → y ≠ z → x ≠ z →
      (sbtw (D'.direction z) (D'.direction y) (D'.direction x) ↔
        sbtw (D.direction z) (D.direction y) (D.direction x))) : D'.Realizes r where
  nonzero := hD'.germ_ne_zero
  directions_injective := hD'.directions_injective
  clockwise := fun x y z hxy hyz hne hne' hne'' =>
    (horder x y z hxy hyz hne hne' hne'').trans
      (hR.clockwise x y z hxy hyz hne hne' hne'')

-- Twenty incident routes, without a degree bound or a caller-selected cut radius.
/-- A twenty-valent embedded vertex admits actual nontrivial local movement. -/
theorem star_twenty_relocation : ∃ ρ > 0,
    let D := PolygonalDrawing.star 20
    let a := D.vertex 20 + (ρ / 4 : ℝ)
    (D.relocateVertex 20 ρ a).vertex 20 ≠ D.vertex 20 ∧
    (D.relocateVertex 20 ρ a).IsEmbedding ∧
    (D.relocateVertex 20 ρ a).Realizes (PolygonalDrawing.star_isEmbedding 20).rotation := by
  let D := PolygonalDrawing.star 20
  have hD := PolygonalDrawing.star_isEmbedding 20
  obtain ⟨ρ, hρ, hmove⟩ := hD.exists_vertex_relocation_radius 20 (by decide)
  let a := D.vertex 20 + (ρ / 4 : ℝ)
  obtain ⟨hD', _, _, horder⟩ := hmove a (offset_mem hρ)
  refine ⟨ρ, hρ, ?_, hD', realizes_transport hD' hD.realizes_rotation horder⟩
  simpa only [relocateVertex, Function.update_self] using offset_ne (z := D.vertex 20) hρ

-- A literal clockwise triple remains clockwise, and its reversed order fails.
example : ∃ ρ > 0,
    let D := PolygonalDrawing.star 5
    let D' := D.relocateVertex 5 ρ (D.vertex 5 + (ρ / 4 : ℝ))
    let x := (starDartEquiv 5 (⟨0, by decide⟩, true))
    let y := (starDartEquiv 5 (1, true))
    let z := (starDartEquiv 5 (2, true))
    sbtw (D'.direction z) (D'.direction y) (D'.direction x) ∧
      ¬sbtw (D'.direction x) (D'.direction y) (D'.direction z) := by
  let D := PolygonalDrawing.star 5
  obtain ⟨ρ, hρ, hmove⟩ := (PolygonalDrawing.star_isEmbedding 5).exists_vertex_relocation_radius
    5 (by decide)
  obtain ⟨_, _, _, horder⟩ := hmove _ (offset_mem (z := D.vertex 5) hρ)
  have hold : sbtw
      (D.direction (starDartEquiv 5 (2, true)))
      (D.direction (starDartEquiv 5 (1, true)))
      (D.direction (starDartEquiv 5 (⟨0, by decide⟩, true))) := by
    dsimp only [D, direction, PolygonalDrawing.germ, PolygonalDrawing.star,
      starDartEquiv, Route.germ, Route.line, Route.start, Route.finish, Route.segments]
    convert clockwise_ports (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3) using 1 <;>
      norm_num [D, direction, PolygonalDrawing.germ, PolygonalDrawing.star,
        starDartEquiv, Route.germ, Route.line, Route.start, Route.finish, Route.segments]
  have hnew := (horder (starDartEquiv 5 (⟨0, by decide⟩, true)) (starDartEquiv 5 (1, true))
    (starDartEquiv 5 (2, true)) (by decide) (by decide) (by decide) (by decide)
    (by decide)).mpr hold
  exact ⟨ρ, hρ, hnew, hnew.not_sbtw⟩

-- Two actual parallel loop records plus a disconnected isolate, with a finite genus check.
private def loopGraph : Graph := ⟨[17, 42], [(17, 17), (17, 17)]⟩
private def loopCertificate : RotationCertificate := ⟨[1, 2, 3, 0]⟩
private noncomputable def loopRotation : RotationSystem loopGraph :=
  RotationCertificate.decode loopGraph loopCertificate (by decide)
private theorem loop_genus : loopRotation.NumericalGenusZero :=
  (RotationCertificate.verifyEuler_eq_true_iff
    (G := loopGraph) (c := loopCertificate) (by decide)).mp (by decide)
private noncomputable def loops : PolygonalDrawing loopGraph :=
  PolygonalDrawing.bouquet loopRotation (by decide)
private theorem loops_embedding : loops.IsEmbedding :=
  PolygonalDrawing.bouquet_isEmbedding loopRotation (by decide) loop_genus (by decide)

example : ∃ ρ > 0,
    let a := loops.vertex 17 + (ρ / 4 : ℝ)
    let D' := loops.relocateVertex 17 ρ a
    D'.IsEmbedding ∧ D'.vertex 17 ≠ loops.vertex 17 ∧
    D'.germ (⟨0, by decide⟩, false) =
      loops.cutPort ρ (⟨0, by decide⟩, false) - a ∧
    D'.germ (⟨0, by decide⟩, true) = loops.cutPort ρ (⟨0, by decide⟩, true) - a ∧
    loops.cutPort ρ (⟨0, by decide⟩, false) ≠ loops.cutPort ρ (⟨0, by decide⟩, true) := by
  obtain ⟨ρ, hρ, hmove⟩ := loops_embedding.exists_vertex_relocation_radius 17 (by decide)
  obtain ⟨hD', hg, _, _⟩ := hmove _ (offset_mem (z := loops.vertex 17) hρ)
  refine ⟨ρ, hρ, hD', ?_, hg (⟨0, by decide⟩, false) (by decide),
    hg (⟨0, by decide⟩, true) (by decide), ?_⟩
  · simpa only [relocateVertex, Function.update_self] using
      offset_ne (z := loops.vertex 17) hρ
  · intro h
    have hd := loops_embedding.cutPort_injective hρ (⟨0, by decide⟩, false)
      (⟨0, by decide⟩, true) (by decide) h
    exact Bool.false_ne_true (congrArg Prod.snd hd)

-- Moving the isolate leaves the entire unrelated loop component LITERALLY unchanged.
example : ∃ ρ > 0,
    let a := loops.vertex 42 + (ρ / 4 : ℝ)
    (loops.relocateVertex 42 ρ a).IsEmbedding ∧
      ∀ e, (loops.relocateVertex 42 ρ a).route e = loops.route e := by
  obtain ⟨ρ, hρ, hmove⟩ := loops_embedding.exists_vertex_relocation_radius 42 (by decide)
  refine ⟨ρ, hρ, (hmove _ (offset_mem hρ)).1, ?_⟩
  intro e
  have hends : Dart.vertex (e, false) ≠ 42 ∧ Dart.vertex (e, true) ≠ 42 := by
    fin_cases e <;> decide
  simp only [relocateVertex, ite_eq_left hends]

-- A separate genuine nonloop parallel example obtains its embedding from a checked
-- numerical certificate, before any geometric relocation is invoked.
private def parallelGraph : Graph := ⟨[4, 9], [(4, 9), (4, 9)]⟩
private def parallelCertificate : RotationCertificate := ⟨[2, 3, 0, 1]⟩
private noncomputable def parallelRotation : RotationSystem parallelGraph :=
  RotationCertificate.decode parallelGraph parallelCertificate (by decide)

example : ∃ (D : PolygonalDrawing parallelGraph) (ρ : ℝ), 0 < ρ ∧
    D.IsEmbedding ∧
    (D.relocateVertex 4 ρ (D.vertex 4 + (ρ / 4 : ℝ))).IsEmbedding ∧
    (D.relocateVertex 4 ρ (D.vertex 4 + (ρ / 4 : ℝ))).Realizes parallelRotation := by
  have hr : parallelRotation.NumericalGenusZero :=
    (RotationCertificate.verifyEuler_eq_true_iff
      (G := parallelGraph) (c := parallelCertificate) (by decide)).mp (by decide)
  obtain ⟨D, hD, hR⟩ := parallelRotation.exists_polygonalDrawing (by decide) hr
  obtain ⟨ρ, hρ, hmove⟩ := hD.exists_vertex_relocation_radius 4 (by decide)
  obtain ⟨hD', _, _, horder⟩ := hmove _ (offset_mem hρ)
  exact ⟨D, ρ, hρ, hD, hD', realizes_transport hD' hR horder⟩

-- The inactive leaf end of a single straight edge really shortens. No literal-vector
-- preservation is asserted merely because the name of that endpoint stays fixed.
example :
    let D := PolygonalDrawing.star 1
    (D.relocateVertex 1 (1 / 8) 0).germ (⟨0, by decide⟩, false) ≠
      D.germ (⟨0, by decide⟩, false) := by
  dsimp only
  let D := PolygonalDrawing.star 1
  let t : ℝ := (1 / 8) / ‖D.germ (⟨0, by decide⟩, true)‖
  have ht : 0 < t := div_pos (by norm_num)
    (norm_pos_iff.mpr ((PolygonalDrawing.star_isEmbedding 1).germ_ne_zero (⟨0, by decide⟩, true)))
  have hg : (D.relocateVertex 1 (1 / 8) 0).germ (⟨0, by decide⟩, false) =
      (1 - t) • D.germ (⟨0, by decide⟩, false) := by
    change (((D.outsideRoute 1 (1 / 8) ⟨0, by decide⟩).append 0).germ false) = _
    rw [Route.germ_append]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [outsideRoute, Route.germ_cutEnds]
    simp only [restrictionTime, Route.cutUpper, Route.cutLower, Route.endSegment]
    norm_num [D, PolygonalDrawing.star, PolygonalDrawing.germ, Route.line,
      Route.segments, Dart.vertex, Graph.edgeEndpoint, starGraph, t]
  intro h
  rw [hg] at h
  have him := congrArg Complex.im h
  dsimp only [D, PolygonalDrawing.germ, PolygonalDrawing.star, Route.germ, Route.line,
    Route.start, Route.finish, Route.segments] at him
  norm_num [Complex.smul_im, smul_eq_mul] at him
  linarith

-- A boundary target equal to its own cut port gives a ZERO actual outgoing spoke.
-- Thus the open-ball conclusion cannot be changed to a closed-ball conclusion.
example (ρ : ℝ) (hρ : 0 < ρ) :
    let D := PolygonalDrawing.star 1
    let a := D.cutPort ρ (⟨0, by decide⟩, true)
    a ∈ Metric.sphere (D.vertex 1) ρ ∧ ¬(D.relocateVertex 1 ρ a).IsEmbedding := by
  let D := PolygonalDrawing.star 1
  let a := D.cutPort ρ (⟨0, by decide⟩, true)
  have hg : (D.relocateVertex 1 ρ a).germ (⟨0, by decide⟩, true) = 0 := by
    change ((D.outsideRoute 1 ρ ⟨0, by decide⟩).append a).germ true = 0
    rw [Route.germ_append]
    simp only [↓reduceIte]
    have hp := D.endpoint_outsideRoute 1 ρ ⟨0, by decide⟩ true
    change (D.outsideRoute 1 ρ ⟨0, by decide⟩).finish = _ at hp
    norm_num [Dart.vertex, Graph.edgeEndpoint, starGraph] at hp
    rw [hp, sub_self]
  refine ⟨?_, fun hD' => hD'.germ_ne_zero (⟨0, by decide⟩, true) hg⟩
  rw [Metric.mem_sphere]
  exact (PolygonalDrawing.star_isEmbedding 1).dist_cutPort hρ.le (⟨0, by decide⟩, true)

open Graph.RotationRecognition

-- This is an ordinary consumer, not a new public recognition wrapper. The target
-- must lie in the internally chosen local ball and no frozen edge may be incident.
private theorem local_query {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing (subdivisionGraph I)) (hD : D.IsEmbedding)
    (v : ℕ) (hv : v ∈ (subdivisionGraph I).vertices)
    (hother : ∀ w ∈ (subdivisionGraph I).vertices, w ≠ v →
      D.vertex w = (referenceDrawing I).vertex w)
    (haway : ∀ e : Fin (subdivisionGraph I).edges.length,
      ((subdivide I)[e.val]'(by
        simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
        Dart.vertex (e, false) ≠ v ∧ Dart.vertex (e, true) ≠ v)
    (hkeep : ∀ e : Fin (subdivisionGraph I).edges.length,
      ((subdivide I)[e.val]'(by
        simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
        D.route e = (referenceDrawing I).route e)
    (r : RotationSystem (subdivisionGraph I)) (hR : D.Realizes r) :
    ∃ ρ > 0, (referenceDrawing I).vertex v ∈ Metric.ball (D.vertex v) ρ →
      query I = true ∧ ∃ D' : PolygonalDrawing (subdivisionGraph I),
        D'.IsEmbedding ∧ D'.Realizes r ∧ ∀ w ∈ (subdivisionGraph I).vertices,
          D'.vertex w = (referenceDrawing I).vertex w := by
  obtain ⟨ρ, hρ, hmove⟩ := hD.exists_vertex_relocation_radius v hv
  refine ⟨ρ, hρ, fun htarget => ?_⟩
  let D' := D.relocateVertex v ρ ((referenceDrawing I).vertex v)
  obtain ⟨hD', _, _, horder⟩ := hmove _ htarget
  have hV : ∀ w ∈ (subdivisionGraph I).vertices,
      D'.vertex w = (referenceDrawing I).vertex w := by
    intro w hwmem
    by_cases hw : w = v
    · subst w
      simp only [D', relocateVertex, Function.update_self]
    · simpa only [D', relocateVertex, Function.update_of_ne hw] using hother w hwmem hw
  have hF (e : Fin (subdivisionGraph I).edges.length)
      (he : ((subdivide I)[e.val]'(by
        simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true) :
      D'.route e = (referenceDrawing I).route e := by
    simp only [D', relocateVertex, ite_eq_left (haway e he)]
    exact hkeep e he
  have hquery := query_eq_true_of_positioned_frozen_embedding hI D' hD'
    hV hF
  exact ⟨hquery, D', hD', realizes_transport hD' hR horder, hV⟩

-- A satisfying degenerate local-necessity application: the target equals the old point,
-- hence lies in EVERY internally selected positive ball. Its premise is not impossible.
private def pointInput : FixedRotationInput := ⟨⟨[0], []⟩, [none]⟩

example : query pointInput = true := by
  have hI : Valid pointInput := (validate_eq_true_iff _).mp (by decide)
  let D : PolygonalDrawing (subdivisionGraph pointInput) := PolygonalDrawing.points [0]
  have hD : D.IsEmbedding := PolygonalDrawing.points_isEmbedding [0]
  obtain ⟨ρ, hρ, hcall⟩ := local_query hI D hD 0 (by decide)
    (by
      intro w hw hne
      have hw0 : w = 0 := by simpa [subdivisionGraph, subdivisionSize, pointInput] using hw
      exact False.elim (hne hw0))
    (by intro e; exact Fin.elim0 e) (by intro e; exact Fin.elim0 e)
    hD.rotation hD.realizes_rotation
  apply (hcall ?_).1
  have hmem : D.vertex 0 ∈ Metric.ball (D.vertex 0) ρ := Metric.mem_ball_self hρ
  convert hmem using 1
  norm_num [D, pointInput, referenceDrawing, referencePoint, referenceOrder, centerBlocks,
      PolygonalDrawing.points, parabolaPoint, Complex.norm_def, Complex.ext_iff]

end CslibFrontierTests.PolygonalVertexRelocation
