/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary plateau-shear and horizontal-transport clients)

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.HorizontalTransport
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Ordinary MODULE/public-import clients of the joint construction. The star has twenty
incident edges and coheight leaves. The chosen width precedes every displacement; no numeric
value of that width is assumed. The two-loop bouquet has only one declared vertex, avoiding
the false claim that a coheight isolate stays fixed. Scalar counterexamples distinguish the
plateau from a triangular tent, closed-parameter from all-real identities, and whole-node
half-spaces from endpoint-only conditions.

-/

public section

namespace CslibFrontierTests.PolygonalHorizontalTransport

open Cslib Polygonal Cslib.Complexity Graph RotationSystem
open Graph.PolygonalDrawing

-- The public star already has center height zero and every leaf at height one.
/-- One width supports arbitrarily large displacements of a twenty-valent center. -/
theorem star_twenty_horizontal : ∃ r > 0, ∀ d : ℝ,
    let D := PolygonalDrawing.star 20
    let D' := D.plateauShear 0 r d
    D'.IsEmbedding ∧ D'.vertex 20 = (d : ℂ) ∧
      (∀ w < 20, D'.vertex w = D.vertex w) ∧
      D'.Realizes (PolygonalDrawing.star_isEmbedding 20).rotation ∧
      ∀ e, (D'.route e).segments ≤ 5 := by
  let D := PolygonalDrawing.star 20
  have hD := PolygonalDrawing.star_isEmbedding 20
  have hG : (starGraph 20).incidenceVertices ⊆ (starGraph 20).vertices := by decide
  have hsep : ∀ w ∈ (starGraph 20).vertices, w ≠ 20 →
      (D.vertex w).im ≠ (D.vertex 20).im := by
    intro w _ hw
    simp [D, PolygonalDrawing.star, starPoint, hw]
  obtain ⟨r, hr, hmove⟩ := hD.exists_horizontal_vertex_transport hG 20 (by decide) hsep
  refine ⟨r, hr, fun d => ?_⟩
  obtain ⟨hemb, hv, hg, horder, hcount, _⟩ := hmove d
  have hzero : (D.vertex 20).im = 0 := by simp [D, PolygonalDrawing.star, starPoint]
  rw [hzero] at hemb hv hg horder hcount
  refine ⟨hemb, ?_, ?_, ?_, ?_⟩
  · simpa [D, PolygonalDrawing.star, starPoint] using hv 20 (by decide)
  · intro w hw
    have hwdecl : w ∈ (starGraph 20).vertices := by simp [starGraph]; omega
    simpa only [ite_eq_right (Nat.ne_of_lt hw)] using hv w hwdecl
  · refine ⟨hemb.germ_ne_zero, hemb.directions_injective, ?_⟩
    intro x y z hxy hyz hne hne' hne''
    exact (horder x y z hxy hyz hne hne' hne'').trans
      (hD.realizes_rotation.clockwise x y z hxy hyz hne hne' hne'')
  · intro e
    simpa only [D, PolygonalDrawing.star, Route.line, Route.segments] using hcount e

-- The same chosen width covers displacement ten, rather than a shrinking local move.
example : ∃ r > 0, ((PolygonalDrawing.star 20).plateauShear 0 r 10).IsEmbedding ∧
    ((PolygonalDrawing.star 20).plateauShear 0 r 10).vertex 20 = (10 : ℂ) := by
  obtain ⟨r, hr, hm⟩ := star_twenty_horizontal
  exact ⟨r, hr, (hm 10).1, (hm 10).2.1⟩

private def loopGraph : Graph := ⟨[0], [(0, 0), (0, 0)]⟩
private def loopCertificate : RotationCertificate := ⟨[1, 2, 3, 0]⟩
private noncomputable def loopRotation : RotationSystem loopGraph :=
  RotationCertificate.decode loopGraph loopCertificate (by decide)

-- A finite genus check supplies a genuine embedding before transport is invoked.
example : ∃ (D : PolygonalDrawing loopGraph) (r : ℝ), 0 < r ∧ D.IsEmbedding ∧
    ∀ d : ℝ, (D.plateauShear (D.vertex 0).im r d).IsEmbedding ∧
      (∀ b : Bool, ∃ c : ℝ, 0 < c ∧
        (D.plateauShear (D.vertex 0).im r d).germ (⟨0, by decide⟩, b) =
          c • D.germ (⟨0, by decide⟩, b)) ∧
      (D.plateauShear (D.vertex 0).im r d).Realizes loopRotation := by
  have hgenus : loopRotation.NumericalGenusZero :=
    (RotationCertificate.verifyEuler_eq_true_iff
      (G := loopGraph) (c := loopCertificate) (by decide)).mp (by decide)
  let D := PolygonalDrawing.bouquet loopRotation (by decide)
  have hD : D.IsEmbedding :=
    PolygonalDrawing.bouquet_isEmbedding loopRotation (by decide) hgenus (by decide)
  have hR : D.Realizes loopRotation := PolygonalDrawing.bouquet_realizes loopRotation (by decide)
  obtain ⟨r, hr, hm⟩ := hD.exists_horizontal_vertex_transport (by decide) 0 (by decide)
    (by intro w hw hne; simp only [loopGraph, List.mem_singleton] at hw; exact (hne hw).elim)
  refine ⟨D, r, hr, hD, fun d => ?_⟩
  obtain ⟨hemb, _, hg, horder, _, _⟩ := hm d
  refine ⟨hemb, fun b => hg (⟨0, by decide⟩, b), ?_⟩
  refine ⟨hemb.germ_ne_zero, hemb.directions_injective, ?_⟩
  intro x y z hxy hyz hne hne' hne''
  exact (horder x y z hxy hyz hne hne' hne'').trans
    (hR.clockwise x y z hxy hyz hne hne' hne'')

-- A singleton isolate has no incidence or route premise to hide.
example : ∃ r > 0, ∀ d : ℝ,
    ((PolygonalDrawing.points [7]).plateauShear 0 r d).IsEmbedding ∧
      ((PolygonalDrawing.points [7]).plateauShear 0 r d).vertex 7 = (7 + d : ℝ) := by
  obtain ⟨r, hr, hm⟩ := (PolygonalDrawing.points_isEmbedding [7]).exists_horizontal_vertex_transport
    (by simp [Graph.incidenceVertices]) 7 (by simp)
    (by intro w hw hne; simp only [List.mem_singleton] at hw; exact (hne hw).elim)
  refine ⟨r, hr, fun d => ?_⟩
  have hz : ((PolygonalDrawing.points [7]).vertex 7).im = 0 := by simp [PolygonalDrawing.points]
  have hemb := (hm d).1
  have hv := (hm d).2.1 7 (by simp)
  simp only [hz] at hemb hv
  exact ⟨hemb, by simpa [PolygonalDrawing.points] using hv⟩

-- Empty graphs have no selected declared vertex; the total constructor is still meaningful.
example : ((PolygonalDrawing.points []).plateauShear 0 1 10).IsEmbedding := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    simp at hu
  · intro e
    exact Fin.elim0 e
  · intro e
    exact Fin.elim0 e
  · intro e
    exact Fin.elim0 e

private def sharp : Route := Route.line (-2 * Complex.I) (2 * Complex.I)

-- Four strict interior level cuts, checked through the public exact-count law.
example : (sharp.plateauShear 0 1 10).segments = 5 := by
  rw [Route.segments_plateauShear_eq (by norm_num : (0 : ℝ) < 1) sharp
    (by norm_num : (10 : ℝ) ≠ 0)]
  change (Finset.univ.sum (fun i : Fin 1 => _)) = 5
  rw [Fin.sum_univ_one]
  dsimp only [sharp, Route.line]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example : (sharp.plateauShear 0 1 10).start = sharp.start ∧
    (sharp.plateauShear 0 1 10).finish = sharp.finish ∧
    (10 : ℂ) ∈ (sharp.plateauShear 0 1 10).support := by
  have he : ∀ b, (sharp.plateauShear 0 1 10).endpoint b = sharp.endpoint b := by
    intro b
    rw [Route.endpoint_plateauShear]
    apply Polygonal.plateauShear_apply_outer (by norm_num : (0 : ℝ) < 1) 10
    cases b <;>
      dsimp only [sharp, Route.endpoint, Route.start, Route.finish, Route.line] <;> norm_num
  refine ⟨he false, he true, ?_⟩
  rw [Route.support_plateauShear]
  refine ⟨0, ?_, ?_⟩
  · apply (sharp.mem_support_iff 0).mpr
    refine ⟨0, 1 / 2, by constructor <;> norm_num, ?_⟩
    apply Complex.ext <;> dsimp only [sharp, Route.eval, Route.line] <;>
      norm_num [AffineMap.lineMap_apply_module',
      Complex.smul_re, Complex.smul_im]
  · simpa using Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10
      (z := 0) (by norm_num)

-- Decreasing height and both endpoint tags, through public APIs.
example : (sharp.reverse.plateauShear 0 1 10).IsSimple ∧
    (sharp.reverse.plateauShear 0 1 10).endpoint false = sharp.finish ∧
    (sharp.reverse.plateauShear 0 1 10).endpoint true = sharp.start := by
  have hs : sharp.IsSimple := Route.isSimple_line (by
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi)
  refine ⟨hs.reverse.plateauShear 0 1 10, ?_, ?_⟩ <;>
    rw [Route.endpoint_plateauShear, Route.endpoint_reverse] <;>
    apply Polygonal.plateauShear_apply_outer (by norm_num : (0 : ℝ) < 1) 10 <;>
    dsimp only [sharp, Route.endpoint, Route.start, Route.finish, Route.line] <;>
    norm_num

-- Boundary-height knots, horizontal and degenerate pieces remain admitted data.
example : ((Route.line (-Complex.I) (-Complex.I)).append (-Complex.I)).plateauShear 0 1 10 =
    (Route.line (-Complex.I) (-Complex.I)).append (-Complex.I) := by
  apply Route.plateauShear_eq_self (by norm_num : (0 : ℝ) < 1)
  left
  intro i
  have hline : (Route.line (-Complex.I) (-Complex.I)).point =
      (fun _ : Fin 2 => -Complex.I) := by
    funext j
    simp only [Route.line, ite_self]
  have h : ∀ j : Fin 3,
      (Fin.lastCases (motive := fun _ : Fin 3 => ℂ) (-Complex.I)
        (fun _ : Fin 2 => -Complex.I) j).im ≤ -1 := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.lastCases_last]
      norm_num
    · simp only [Fin.lastCases_castSucc]
      norm_num
  norm_num only [zero_sub]
  change (Fin.lastCases (motive := fun _ : Fin 3 => ℂ) (-Complex.I)
    ((Route.line (-Complex.I) (-Complex.I)).point) i).im ≤ -1
  rw [hline]
  exact h i

example (p : Route) : p.plateauShear 0 1 0 = p := Route.plateauShear_zero p 0 1

-- Coheight undeclared or other declared names are moved too: no global Function.update law.
example : Polygonal.plateauShear 0 1 10 (1 : ℂ) ≠ (1 : ℂ) := by
  rw [Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10 (by norm_num)]
  norm_num

-- The nonlinear identity is false when extrapolated outside a selected affine strip.
example : Polygonal.plateauShear 0 1 10
      (AffineMap.lineMap (0 : ℂ) (Complex.I / 2) (3 : ℝ)) ≠
    AffineMap.lineMap (Polygonal.plateauShear 0 1 10 (0 : ℂ))
      (Polygonal.plateauShear 0 1 10 (Complex.I / 2)) (3 : ℝ) := by
  have hzero := Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10
    (z := 0) (by norm_num)
  have hhalf := Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10
    (z := Complex.I / 2) (by norm_num)
  rw [hzero, hhalf]
  have hout : Polygonal.plateauShear 0 1 10
      (AffineMap.lineMap (0 : ℂ) (Complex.I / 2) (3 : ℝ)) =
      AffineMap.lineMap (0 : ℂ) (Complex.I / 2) (3 : ℝ) := by
    apply Polygonal.plateauShear_apply_outer (by norm_num : (0 : ℝ) < 1) 10
    norm_num [AffineMap.lineMap_apply_module', Complex.smul_im]
  rw [hout]
  intro he
  have hr := congrArg Complex.re he
  norm_num [AffineMap.lineMap_apply_module', Complex.smul_re] at hr

-- A triangular tent changes a central vertical germ's direction; the flat plateau is needed.
example : ¬∃ c : ℝ, 0 < c ∧ ((-10 : ℂ) + Complex.I) = c • Complex.I := by
  rintro ⟨c, _, he⟩
  have hr := congrArg Complex.re he
  norm_num [Complex.smul_re] at hr

-- Merely fixing both ends does not make an entire bent route literal.
private def bent : Route := (Route.line (-2 * Complex.I) 0).append (2 * Complex.I)
example : (bent.plateauShear 0 1 10).endpoint false = bent.endpoint false ∧
    (bent.plateauShear 0 1 10).endpoint true = bent.endpoint true ∧
    bent.plateauShear 0 1 10 ≠ bent := by
  have he (b : Bool) : (bent.plateauShear 0 1 10).endpoint b = bent.endpoint b := by
    rw [Route.endpoint_plateauShear]
    apply Polygonal.plateauShear_apply_outer (by norm_num : (0 : ℝ) < 1) 10
    cases b <;>
      simp only [bent, Route.endpoint_append, Bool.false_eq_true, ↓reduceIte, Route.start_line] <;>
      norm_num
  refine ⟨he false, he true, ?_⟩
  have hmid : (10 : ℂ) ∈ (bent.plateauShear 0 1 10).support := by
    rw [Route.support_plateauShear]
    refine ⟨0, ?_, ?_⟩
    · rw [bent, Route.support_append, Route.support_line]
      exact Or.inl (right_mem_segment ℝ _ _)
    · simpa using Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10
        (z := 0) (by norm_num)
  intro hsame
  rw [hsame, bent, Route.support_append, Route.support_line] at hmid
  rcases hmid with hmid | hmid <;> rw [segment_eq_image_lineMap] at hmid <;>
    obtain ⟨t, _, heq⟩ := hmid <;>
    have hr := congrArg Complex.re heq <;>
    norm_num [AffineMap.lineMap_apply_module', Route.finish_line, Complex.smul_re] at hr

-- The four source parameters hit the actual four height levels in source order.
example :
    Polygonal.plateauShear 0 1 10 (sharp.eval 0 (1 / 4)) = -Complex.I ∧
    Polygonal.plateauShear 0 1 10 (sharp.eval 0 (3 / 8)) = 10 - Complex.I / 2 ∧
    Polygonal.plateauShear 0 1 10 (sharp.eval 0 (5 / 8)) = 10 + Complex.I / 2 ∧
    Polygonal.plateauShear 0 1 10 (sharp.eval 0 (3 / 4)) = Complex.I := by
  dsimp only [sharp, Route.eval, Route.line]
  norm_num [ AffineMap.lineMap_apply_module',
    Polygonal.plateauShear_apply, Complex.ext_iff, Complex.smul_re, Complex.smul_im]

-- A coheight OTHER DECLARED isolate makes the graph theorem's height premise false.
example : ¬(∀ w ∈ ([0, 1] : List ℕ), w ≠ 0 →
    ((PolygonalDrawing.points [0, 1]).vertex w).im ≠
      ((PolygonalDrawing.points [0, 1]).vertex 0).im) := by
  intro hh
  exact hh 1 (by simp) (by decide) (by simp [PolygonalDrawing.points])

-- A genuine inactive end retains its direction but cannot retain its full old vector.
example : ∃ r > 0,
    let D := PolygonalDrawing.star 1
    let D' := D.plateauShear 0 r 10
    D'.IsEmbedding ∧
      (∃ c : ℝ, 0 < c ∧ D'.germ (⟨0, by decide⟩, false) =
        c • D.germ (⟨0, by decide⟩, false)) ∧
      D'.germ (⟨0, by decide⟩, false) ≠ D.germ (⟨0, by decide⟩, false) := by
  let D := PolygonalDrawing.star 1
  have hD := PolygonalDrawing.star_isEmbedding 1
  have hsep : ∀ w ∈ (starGraph 1).vertices, w ≠ 1 →
      (D.vertex w).im ≠ (D.vertex 1).im := by
    intro w _ hw
    simp [D, PolygonalDrawing.star, starPoint, hw]
  obtain ⟨r, hr, hm⟩ := hD.exists_horizontal_vertex_transport (by decide) 1 (by decide) hsep
  obtain ⟨hemb, hv, hg, _, _, _⟩ := hm 10
  have hcenter : (D.vertex 1).im = 0 := by simp [D, PolygonalDrawing.star, starPoint]
  rw [hcenter] at hemb hv hg
  let D' := D.plateauShear 0 r 10
  have hstart : (D'.route ⟨0, by decide⟩).start = (D.route ⟨0, by decide⟩).start := by
    change (D'.route ⟨0,by decide⟩).endpoint false = (D.route ⟨0,by decide⟩).endpoint false
    rw [D'.endpoint_eq, D.endpoint_eq]
    have hv0 := hv 0 (by decide)
    exact hv0
  have hnozero : (0 : ℂ) ∉ (D'.route ⟨0, by decide⟩).support := by
    change (0 : ℂ) ∉ ((D.route ⟨0,by decide⟩).plateauShear 0 r 10).support
    rw [Route.support_plateauShear]
    rintro ⟨z, hz, he⟩
    dsimp only [D, PolygonalDrawing.star] at hz
    norm_num only [Fin.val_mk, Nat.cast_zero, zero_add] at hz
    change z ∈ (Route.line (⟨1, 1⟩ : ℂ) 0).support at hz
    rw [Route.support_line, segment_eq_image_lineMap] at hz
    obtain ⟨t, _, rfl⟩ := hz
    have hi := congrArg Complex.im he
    rw [Polygonal.plateauShear_apply] at hi
    have ht : t = 1 := by
      norm_num [AffineMap.lineMap_apply_module', Complex.smul_im] at hi
      linarith
    rw [ht, AffineMap.lineMap_apply_one,
      Polygonal.plateauShear_apply_inner (h := 0) hr 10 (by
        simp only [Complex.zero_im, sub_self, abs_zero]
        positivity)] at he
    norm_num at he
  refine ⟨r, hr, hemb, hg (⟨0, by decide⟩, false), ?_⟩
  intro heq
  have hz := (D'.route ⟨0, by decide⟩).at_mem_support 0
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have he : (D'.route ⟨0, by decide⟩).eval 0 1 = 0 := by
    have hnear := (D'.route ⟨0, by decide⟩).eval_near_end false 1
    simp only [Route.endSegment, Route.endTime, Bool.false_eq_true, ↓reduceIte,
      Route.endpoint, one_smul] at hnear
    rw [hnear, hstart]
    change (D.route ⟨0, by decide⟩).start + D'.germ (⟨0, by decide⟩, false) = 0
    rw [heq]
    dsimp only [D, PolygonalDrawing.star, PolygonalDrawing.germ, Route.germ, Route.start,
      Route.line]
    norm_num
  exact hnozero (he ▸ hz)

-- Five-valent declared stars retain the literal clockwise order, not only incidence planarity.
example : ∃ r > 0, ∀ d : ℝ, ∀ x y z : Dart (starGraph 5),
    x.vertex = y.vertex → y.vertex = z.vertex → x ≠ y → y ≠ z → x ≠ z →
      (sbtw (((PolygonalDrawing.star 5).plateauShear 0 r d).direction z)
        (((PolygonalDrawing.star 5).plateauShear 0 r d).direction y)
        (((PolygonalDrawing.star 5).plateauShear 0 r d).direction x) ↔
      sbtw ((PolygonalDrawing.star 5).direction z) ((PolygonalDrawing.star 5).direction y)
        ((PolygonalDrawing.star 5).direction x)) := by
  have hsep : ∀ w ∈ (starGraph 5).vertices, w ≠ 5 →
      ((PolygonalDrawing.star 5).vertex w).im ≠ ((PolygonalDrawing.star 5).vertex 5).im := by
    intro w _ hw
    simp [PolygonalDrawing.star, starPoint, hw]
  obtain ⟨r, hr, hm⟩ := (PolygonalDrawing.star_isEmbedding 5).exists_horizontal_vertex_transport
    (by decide) 5 (by decide) hsep
  refine ⟨r, hr, fun d => ?_⟩
  obtain ⟨_, _, _, horder, _, _⟩ := hm d
  have hz : ((PolygonalDrawing.star 5).vertex 5).im = 0 := by
    norm_num [PolygonalDrawing.star, starPoint]
  rw [hz] at horder
  exact horder

-- No simplicity claim is made about a degenerate piece, but its continuum image is correct.
example : ((Route.line 0 0).plateauShear 0 1 10).support = {(10 : ℂ)} := by
  rw [Route.support_plateauShear, Route.support_line]
  have he : Polygonal.plateauShear 0 1 10 (0 : ℂ) = (10 : ℂ) := by
    simpa using Polygonal.plateauShear_apply_inner (h := 0) (by norm_num : (0 : ℝ) < 1) 10
      (z := 0) (by norm_num)
  simp only [segment_same, Set.image_singleton, he]

end CslibFrontierTests.PolygonalHorizontalTransport
