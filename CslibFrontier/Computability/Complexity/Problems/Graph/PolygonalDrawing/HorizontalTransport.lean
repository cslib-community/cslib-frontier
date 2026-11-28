/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
public import CslibFrontier.Foundations.Geometry.Polygonal.PlateauShear
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.CutTransport
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity

/-!
# Horizontal transport of a vertex at a separate declared height

One internally selected positive band width works for EVERY real horizontal displacement.
The whole drawing is sheared, preserving continuum contacts; nonincident routes can change.
Only declared names satisfy the stated single-vertex update. Undeclared points are mapped by
the same concrete shear and need not be fixed. Loops retain their two outgoing end tags.

The finite PL construction is original mathematics towards
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
It does not straighten a frozen forest, construct arbitrary point placement, realize parity
moves or establish HT, query sufficiency or the source criterion.

## Interface

* `plateauShear`: actual route subdivision and the mapped vertex function on the same graph.
* `IsEmbedding.exists_horizontal_vertex_transport`: one width for unbounded displacement,
  positive end-germ factors and literal clockwise order.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Apply the concrete plateau shear to every named point and every indexed route.
The route constructor is total at all widths and its endpoint equations are actual map equations. -/
@[expose] noncomputable def plateauShear {G : Graph} (D : PolygonalDrawing G)
    (h r d : ℝ) : PolygonalDrawing G where
  vertex := fun v => Polygonal.plateauShear h r d (D.vertex v)
  route := fun e => (D.route e).plateauShear h r d
  endpoint_eq := fun e b => by rw [Route.endpoint_plateauShear, D.endpoint_eq]

private theorem shear_embedding {G : Graph} {D : PolygonalDrawing G} (hD : D.IsEmbedding)
    (h : ℝ) {r : ℝ} (hr : 0 < r) (d : ℝ) : (D.plateauShear h r d).IsEmbedding := by
  refine hD.of_route_map (Polygonal.plateauShear h r d).injective (fun _ => rfl)
    (fun e => (hD.simple e).plateauShear h r d) ?_
  exact fun e i => Route.eval_plateauShear hr (D.route e) d i

private theorem declared_dart {G : Graph} (hG : G.incidenceVertices ⊆ G.vertices)
    (d : Dart G) : d.vertex ∈ G.vertices := by
  exact Graph.edgeEndpoint_mem G (fun edge he =>
    ⟨hG (List.mem_flatMap.mpr ⟨edge, he, by simp⟩),
      hG (List.mem_flatMap.mpr ⟨edge, he, by simp⟩)⟩) d.1.isLt d.2

private theorem separate_width {G : Graph} (D : PolygonalDrawing G) (v : ℕ)
    (hsep : ∀ w ∈ G.vertices, w ≠ v → (D.vertex w).im ≠ (D.vertex v).im) :
    ∃ r > 0, ∀ w ∈ G.vertices, w ≠ v → r < |(D.vertex w).im - (D.vertex v).im| := by
  classical
  let gaps := insert 1 ((G.vertices.toFinset.erase v).image
    fun w => |(D.vertex w).im - (D.vertex v).im|)
  have hne : gaps.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let m := gaps.min' hne
  have hm : 0 < m := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have hw' := Finset.mem_erase.mp hw
      exact abs_pos.mpr (sub_ne_zero.mpr (hsep w (List.mem_toFinset.mp hw'.2) hw'.1))
  refine ⟨m / 2, by positivity, fun w hw hne => ?_⟩
  have hmle : m ≤ |(D.vertex w).im - (D.vertex v).im| :=
    gaps.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨w, Finset.mem_erase.mpr ⟨hne, List.mem_toFinset.mpr hw⟩, rfl⟩))
  linarith

/-- A vertex at a height different from every OTHER declared name can be transported by
ANY real horizontal displacement using one internally chosen width. The actual whole drawing
remains embedded, all outgoing germs are positively proportional and literal clockwise order
is unchanged. This is a horizontal transport component, not arbitrary frozen placement. -/
theorem IsEmbedding.exists_horizontal_vertex_transport {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : G.incidenceVertices ⊆ G.vertices)
    (v : ℕ) (hv : v ∈ G.vertices)
    (hsep : ∀ w ∈ G.vertices, w ≠ v → (D.vertex w).im ≠ (D.vertex v).im) :
    ∃ r > 0, ∀ d : ℝ,
      let D' := D.plateauShear (D.vertex v).im r d
      D'.IsEmbedding ∧
      (∀ w ∈ G.vertices, D'.vertex w =
        if w = v then D.vertex v + (d : ℂ) else D.vertex w) ∧
      (∀ x : Dart G, ∃ c : ℝ, 0 < c ∧ D'.germ x = c • D.germ x) ∧
      (∀ x y z : Dart G, x.vertex = y.vertex → y.vertex = z.vertex →
        x ≠ y → y ≠ z → x ≠ z →
        (sbtw (D'.direction z) (D'.direction y) (D'.direction x) ↔
          sbtw (D.direction z) (D.direction y) (D.direction x))) ∧
      (∀ e, (D'.route e).segments ≤ 5 * (D.route e).segments) ∧
      (∀ e, ((∀ i, ((D.route e).point i).im ≤ (D.vertex v).im - r) ∨
          (∀ i, (D.vertex v).im + r ≤ ((D.route e).point i).im)) →
        D'.route e = D.route e) := by
  obtain ⟨r, hr, hgap⟩ := separate_width D v hsep
  have hflat (w : ℕ) (hw : w ∈ G.vertices) :
      |(D.vertex w).im - (D.vertex v).im| < r / 2 ∨
        r < |(D.vertex w).im - (D.vertex v).im| := by
    by_cases he : w = v
    · subst w
      exact Or.inl (by simp [div_pos hr zero_lt_two])
    · exact Or.inr (hgap w hw he)
  refine ⟨r, hr, fun d => ?_⟩
  have hg (x : Dart G) : ∃ c : ℝ, 0 < c ∧
      (D.plateauShear (D.vertex v).im r d).germ x = c • D.germ x := by
    apply Route.germ_plateauShear hr (D.route x.1) d x.2
    rw [D.endpoint_eq]
    exact hflat x.vertex (declared_dart hG x)
  have hd (x : Dart G) : (D.plateauShear (D.vertex v).im r d).direction x = D.direction x := by
    obtain ⟨c, hc, heq⟩ := hg x
    simp only [direction, heq, Complex.real_smul, Complex.arg_ofReal_mul hc _]
  refine ⟨shear_embedding hD _ hr d, fun w hw => ?_, hg,
    fun x y z _ _ _ _ _ => by rw [hd x, hd y, hd z],
    fun e => (Route.segments_plateauShear (D.route e) _ r d).2,
    fun _ => Route.plateauShear_eq_self hr d⟩
  change Polygonal.plateauShear (D.vertex v).im r d (D.vertex w) = _
  by_cases he : w = v
  · subst w
    let _ := hv
    rw [ite_eq_left rfl]
    exact Polygonal.plateauShear_apply_inner hr d (by simpa using (div_pos hr zero_lt_two).le)
  · rw [ite_eq_right he]
    exact Polygonal.plateauShear_apply_outer hr d (hgap w hw he).le

end Cslib.Complexity.Graph.PolygonalDrawing
