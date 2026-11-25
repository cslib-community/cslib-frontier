/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Neighborhood
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction
import CslibFrontier.Tactic.FinIndex
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Closed neighborhoods and cut ports of polygonal drawings

A declared vertex has a positive closed neighborhood avoiding every other declared point
and every nonincident segment. Its radius is smaller than one third of every incident end
segment. This includes both separate ends of a loop and imposes no shape on the drawing.

The cut ports are actual real affine points on those end segments, at a common distance
from the vertex. A uniform radius works at all declared vertices when the coordinates
are injective, the incident germs are nonzero, and all vertex contacts occur at the
corresponding endpoints. Disjoint disks and distinct outgoing directions within each disk
make all indexed ports distinct. A discarded stub stays in its own disk, and it can meet
another stub or another original route only at a common original endpoint. These facts
support local replacement and subdivision.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- If routes reach a vertex only at their incident endpoints, a small closed ball
isolates its straight star and cuts each incident end before its first third. The
radius is less than half the distance to each other declared vertex. -/
private theorem exists_restriction_radius_of_vertex_contacts {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ)
    (hcontacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (hvertices : ∀ w ∈ G.1, D.vertex w = D.vertex v → w = v)
    (hgerm : ∀ d : Dart G, d.vertex = v → D.germ d ≠ 0) :
    ∃ ρ > 0,
      (∀ w ∈ G.1, w ≠ v → 2 * ρ < dist (D.vertex w) (D.vertex v)) ∧
      (∀ e (i : Fin (D.route e).segments) z,
        z ∈ Metric.closedBall (D.vertex v) ρ →
        z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
          (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v)) ∧
      (∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) := by
  classical
  obtain ⟨ε, hε, hseg⟩ := D.exists_vertex_ball_of_vertex_contacts v hcontacts
  let K : Set ℂ := D.vertex '' {w | w ∈ G.1 ∧ w ≠ v}
  have hfinite : Set.Finite {w | w ∈ G.1 ∧ w ≠ v} :=
    G.1.finite_toSet.subset (fun _ h => h.1)
  have hK : IsClosed K := (hfinite.image D.vertex).isClosed
  have hvK : D.vertex v ∈ Kᶜ := by
    rintro ⟨w, ⟨hw, hne⟩, heq⟩
    exact hne (hvertices w hw heq)
  obtain ⟨δ, hδ, hpoint⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hvK
  let lengths : Finset ℝ := insert 1
    (Finset.univ.image fun d : Dart G => if d.vertex = v then ‖D.germ d‖ else 1)
  have hnonempty : lengths.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let m := lengths.min' hnonempty
  have hm : 0 < m := (Finset.lt_min'_iff _ _).mpr fun y hy => by
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hy
      split_ifs with hv
      exacts [norm_pos_iff.mpr (hgerm d hv), one_pos]
  have hmd (d : Dart G) (hd : d.vertex = v) : m ≤ ‖D.germ d‖ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, by rw [ite_eq_left hd]⟩))
  let ρ := min ε (min (δ / 2) (m / 3)) / 2
  have hρ : 0 < ρ := div_pos (lt_min hε (lt_min (by positivity) (by positivity))) (by norm_num)
  have hρε : ρ < ε := by
    have h := min_le_left ε (min (δ / 2) (m / 3))
    dsimp [ρ]
    linarith
  have hρδ : 2 * ρ < δ := by
    have h := (min_le_right ε (min (δ / 2) (m / 3))).trans (min_le_left (δ / 2) (m / 3))
    dsimp [ρ]
    linarith
  have hρm : 3 * ρ < m := by
    have h := (min_le_right ε (min (δ / 2) (m / 3))).trans (min_le_right (δ / 2) (m / 3))
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ, fun w hw hne => ?_, fun e i z hz => hseg e i z
    (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hρε)),
    fun d hd => hρm.trans_le (hmd d hd)⟩
  refine hρδ.trans_le (le_of_not_gt fun hdist => ?_)
  exact hpoint (Metric.mem_ball.mpr hdist) ⟨w, ⟨hw, hne⟩, rfl⟩

/-- A sufficiently small closed ball isolates the straight star of a declared vertex,
avoids the other declared points, and cuts every incident segment before its first third.
Repeated vertex declarations and arbitrary natural vertex names are allowed. -/
theorem IsEmbedding.exists_restriction_radius {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) :
    ∃ ρ > 0,
      (∀ w ∈ G.1, D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v) ∧
      (∀ e (i : Fin (D.route e).segments) z,
        z ∈ Metric.closedBall (D.vertex v) ρ →
        z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
          (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v)) ∧
      (∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) := by
  obtain ⟨ρ, hρ, hdist, hseg, hlen⟩ := D.exists_restriction_radius_of_vertex_contacts v
    (fun e i t ht => hD.vertex_contacts e i t ht v hv)
    (fun _ hw => hD.vertices_injective hw hv) (fun d _ => hD.germ_ne_zero d)
  refine ⟨ρ, hρ, fun w hw hz => ?_, hseg, hlen⟩
  by_contra hne
  linarith [hdist w hw hne, Metric.mem_closedBall.mp hz]

/-- A common sufficiently small positive radius gives pairwise disjoint closed
vertex balls, restricts route contacts with each ball to the incident end segments,
and cuts every declared incident end before its first third. -/
private theorem exists_uniform_restriction_radius {G : Graph} (D : PolygonalDrawing G)
    (hcontacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      ∀ v ∈ G.vertices, (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (hvertices : Set.InjOn D.vertex {v | v ∈ G.vertices})
    (hgerm : ∀ d : Dart G, d.vertex ∈ G.vertices → D.germ d ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      (∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
        Disjoint (Metric.closedBall (D.vertex v) ρ) (Metric.closedBall (D.vertex w) ρ)) ∧
      (∀ v ∈ G.vertices, ∀ e (i : Fin (D.route e).segments) z,
        z ∈ Metric.closedBall (D.vertex v) ρ →
        z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
          (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v)) ∧
      ∀ d : Dart G, d.vertex ∈ G.vertices → 3 * ρ < ‖D.germ d‖ := by
  classical
  choose radius hpos hdist hlocal hlen using fun v (hv : v ∈ G.vertices) =>
    D.exists_restriction_radius_of_vertex_contacts v
      (fun e i t ht => hcontacts e i t ht v hv)
      (fun _ hw => hvertices hw hv) (fun d hd => hgerm d (hd ▸ hv))
  let radii := G.vertices.toFinset.attach.image
    (fun v => radius v.val (List.mem_toFinset.mp v.property))
  obtain ⟨ε, hε, hbound⟩ := Finset.exists_between' ({0} : Finset ℝ) radii (by
    intro x hx y hy
    rw [Finset.mem_singleton.mp hx]
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hy
    exact hpos v.val (List.mem_toFinset.mp v.property))
  have hsmall (v : ℕ) (hv : v ∈ G.vertices) : ε < radius v hv :=
    hbound _ (Finset.mem_image.mpr ⟨⟨v, List.mem_toFinset.mpr hv⟩, Finset.mem_attach _ _, rfl⟩)
  refine ⟨ε, hε _ (Finset.mem_singleton_self _), fun ρ hρ => ⟨?_, ?_, ?_⟩⟩
  · intro v hv w hw hne
    apply Metric.closedBall_disjoint_closedBall
    have h := hdist w hw v hv hne
    linarith [hρ.2, hsmall w hw]
  · intro v hv e i z hz hs
    exact hlocal v hv e i z
      (Metric.closedBall_subset_closedBall (hρ.2.trans (hsmall v hv)).le hz) hs
  · intro d hd
    linarith [hlen d.vertex hd d rfl, hρ.2, hsmall d.vertex hd]

/-- The cut port on an actual outgoing end segment, with no chosen angular coordinates. -/
@[expose] noncomputable def cutPort {G : Graph} (D : PolygonalDrawing G)
    (ρ : ℝ) (d : Dart G) : ℂ :=
  D.vertex d.vertex + (ρ / ‖D.germ d‖) • D.germ d

/-- For a nonzero outgoing germ the port lies at the cut radius from its vertex. -/
theorem dist_cutPort {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G) (hd : D.germ d ≠ 0) :
    dist (D.cutPort ρ d) (D.vertex d.vertex) = ρ := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr hd
  rw [cutPort, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hρ hn.le), div_mul_cancel₀ _ (ne_of_gt hn)]

/-- The common-radius cut port lies at precisely that distance from its own vertex. -/
theorem IsEmbedding.dist_cutPort {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G) :
    dist (D.cutPort ρ d) (D.vertex d.vertex) = ρ :=
  D.dist_cutPort hρ d (hD.germ_ne_zero d)

/-- Cutting before the end of the first outgoing segment is an actual segment parameter,
including the reversed final segment at the second end of an edge or loop. -/
theorem cutPort_eq_eval {G : Graph} (D : PolygonalDrawing G) (ρ : ℝ) (d : Dart G) :
    D.cutPort ρ d = (D.route d.1).eval ((D.route d.1).endSegment d.2)
      (Route.endTime d.2 (ρ / ‖D.germ d‖)) := by
  rw [Route.eval_near_end, D.endpoint_eq]
  rfl

/-- A cut strictly shorter than its outgoing segment is on that original route. -/
theorem IsEmbedding.cutPort_mem_support {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G)
    (hd : ρ ≤ ‖D.germ d‖) : D.cutPort ρ d ∈ (D.route d.1).support := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  rw [D.cutPort_eq_eval]
  apply Route.at_mem_support
  exact Route.endTime_mem _ ⟨div_nonneg hρ hn.le, (div_le_one hn).mpr hd⟩

/-- The cut operation preserves the outgoing ray of a nondegenerate end segment. -/
theorem arg_cutPort_sub {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 < ρ) (d : Dart G) (hd : D.germ d ≠ 0) :
    (D.cutPort ρ d - D.vertex d.vertex).arg = (D.germ d).arg := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr hd
  rw [cutPort, add_sub_cancel_left, Complex.real_smul, Complex.arg_real_mul _ (div_pos hρ hn)]

/-- At one vertex, coincident ports of nonzero germs have the same outgoing direction. -/
theorem direction_eq_of_cutPort_eq {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 < ρ) (a b : Dart G) (ha : D.germ a ≠ 0) (hb : D.germ b ≠ 0)
    (hv : a.vertex = b.vertex) (heq : D.cutPort ρ a = D.cutPort ρ b) :
    D.direction a = D.direction b := by
  have heq' : D.cutPort ρ a - D.vertex a.vertex =
      D.cutPort ρ b - D.vertex b.vertex := by rw [heq, hv]
  have harg := congrArg Complex.arg heq'
  rw [D.arg_cutPort_sub hρ a ha, D.arg_cutPort_sub hρ b hb] at harg
  exact congrArg (fun x : ℝ => (x : Real.Angle)) harg

/-- Distinct actual darts at one vertex yield distinct common-radius boundary ports.
The two ends of the same loop are included. -/
theorem IsEmbedding.cutPort_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 < ρ) (a b : Dart G)
    (hv : a.vertex = b.vertex) (heq : D.cutPort ρ a = D.cutPort ρ b) : a = b :=
  hD.directions_injective a b hv
    (D.direction_eq_of_cutPort_eq hρ a b (hD.germ_ne_zero a) (hD.germ_ne_zero b) hv heq)

/-- Disjoint closed vertex balls and distinct outgoing directions within each ball
make all indexed cut ports distinct, even when routes cross outside the balls. -/
theorem cutPort_injective_of_disjoint_balls {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 < ρ) (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hgerm : ∀ d : Dart G, D.germ d ≠ 0)
    (hdirections : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b)
    (hdisjoint : ∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
      Disjoint (Metric.closedBall (D.vertex v) ρ) (Metric.closedBall (D.vertex w) ρ)) :
    Function.Injective (D.cutPort ρ) := by
  intro a b heq
  have hmem (d : Dart G) : D.cutPort ρ d ∈ Metric.closedBall (D.vertex d.vertex) ρ := by
    rw [Metric.mem_closedBall, D.dist_cutPort hρ.le d (hgerm d)]
  have hv : a.vertex = b.vertex := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint _ (hdeclared a) _ (hdeclared b) hne)
      (hmem a) (heq.symm ▸ hmem b)
  exact hdirections a b hv (D.direction_eq_of_cutPort_eq hρ a b (hgerm a) (hgerm b) hv heq)

/-- The straight piece from an original endpoint to its cut port lies inside
the closed ball at that endpoint. -/
theorem cutPort_segment_subset_closedBall {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G) (hd : D.germ d ≠ 0) :
    segment ℝ (D.vertex d.vertex) (D.cutPort ρ d) ⊆
      Metric.closedBall (D.vertex d.vertex) ρ := by
  apply (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self hρ)
  rw [Metric.mem_closedBall, D.dist_cutPort hρ d hd]

private theorem arg_sub_of_mem_segment {a b z : ℂ} (hz : z ∈ segment ℝ a b) (hne : z ≠ a) :
    (z - a).arg = (b - a).arg := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := le_antisymm (le_of_not_gt h) hr.1
    exact hne (by rw [hr0, AffineMap.lineMap_apply_zero])
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, Complex.real_smul,
    Complex.arg_real_mul _ hpos]

/-- Distinct cut stubs can meet only at their common declared endpoint. The
original drawing may have crossings away from the vertex disks. -/
theorem eq_vertex_of_mem_cutPort_segments {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 < ρ) (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hgerm : ∀ d : Dart G, D.germ d ≠ 0)
    (hdirections : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b)
    (hdisjoint : ∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
      Disjoint (Metric.closedBall (D.vertex v) ρ) (Metric.closedBall (D.vertex w) ρ))
    {a b : Dart G} (hne : a ≠ b) {z : ℂ}
    (ha : z ∈ segment ℝ (D.vertex a.vertex) (D.cutPort ρ a))
    (hb : z ∈ segment ℝ (D.vertex b.vertex) (D.cutPort ρ b)) :
    a.vertex = b.vertex ∧ z = D.vertex a.vertex := by
  have hv : a.vertex = b.vertex := by
    by_contra hdiff
    exact Set.disjoint_left.mp (hdisjoint _ (hdeclared a) _ (hdeclared b) hdiff)
      (D.cutPort_segment_subset_closedBall hρ.le a (hgerm a) ha)
      (D.cutPort_segment_subset_closedBall hρ.le b (hgerm b) hb)
  refine ⟨hv, ?_⟩
  by_contra hz
  have hza := (arg_sub_of_mem_segment ha hz).trans (D.arg_cutPort_sub hρ a (hgerm a))
  have hzb := (arg_sub_of_mem_segment hb (hv ▸ hz)).trans (D.arg_cutPort_sub hρ b (hgerm b))
  apply hne (hdirections a b hv ?_)
  exact congrArg (fun x : ℝ => (x : Real.Angle))
    (hza.symm.trans ((by rw [hv] : (z - D.vertex a.vertex).arg =
      (z - D.vertex b.vertex).arg).trans hzb))

/-- A cut stub can meet a different original route only at their common vertex,
provided the closed ball at the stub's center isolates its incident segments. -/
theorem eq_vertex_of_mem_cutPort_segment_and_route {G : Graph} (D : PolygonalDrawing G)
    {ρ : ℝ} (hρ : 0 < ρ) (a : Dart G) (hgerm : D.germ a ≠ 0)
    (hdirections : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b)
    (e : Fin G.edges.length) (hne : a.1 ≠ e)
    (hlocal : ∀ (i : Fin (D.route e).segments) z,
      z ∈ Metric.closedBall (D.vertex a.vertex) ρ →
      z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = a.vertex) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = a.vertex))
    {z : ℂ} (ha : z ∈ segment ℝ (D.vertex a.vertex) (D.cutPort ρ a))
    (he : z ∈ (D.route e).support) :
    ∃ b, Dart.vertex (e, b) = a.vertex ∧ z = D.vertex a.vertex := by
  obtain ⟨i, t, ht, hzt⟩ := ((D.route e).mem_support_iff z).mp he
  have hzball := D.cutPort_segment_subset_closedBall hρ.le a hgerm ha
  have hzseg : z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) :=
    hzt ▸ lineMap_mem_segment ℝ _ _ ht
  obtain ⟨b, hi, hv⟩ : ∃ b, i = (D.route e).endSegment b ∧ Dart.vertex (e, b) = a.vertex := by
    rcases hlocal i z hzball hzseg with ⟨hi, hv⟩ | ⟨hi, hv⟩
    · exact ⟨false, Fin.ext hi, hv⟩
    · have hilast : i = Fin.last (D.route e).bends := by fin_index [Route.segments]
      exact ⟨true, hilast, hv⟩
  refine ⟨b, hv, ?_⟩
  by_contra hz
  let u := Route.endTime b t
  have htime : Route.endTime b u = t := by cases b <;> simp [u, Route.endTime]
  have hpoint : z - D.vertex a.vertex = u • D.germ (e, b) := by
    rw [← hzt, hi, ← htime, Route.eval_near_end, D.endpoint_eq, hv, add_sub_cancel_left]
    rfl
  have hpos : 0 < u := lt_of_le_of_ne (Route.endTime_mem b ht).1 (fun hu => hz (by
    rwa [← hu, zero_smul, sub_eq_zero] at hpoint))
  have harg := (arg_sub_of_mem_segment ha hz).trans (D.arg_cutPort_sub hρ a hgerm)
  rw [hpoint, Complex.real_smul, Complex.arg_real_mul _ hpos] at harg
  exact hne (congrArg Prod.fst (hdirections a (e, b) hv.symm
    (congrArg (fun x : ℝ => (x : Real.Angle)) harg.symm)))

/-- Cut an end precisely when it belongs to the vertex being replaced. The other end
of an edge stays unchanged; the two ends of a loop are cut separately. -/
@[expose] noncomputable def restrictionTime {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (d : Dart G) : ℝ :=
  if d.vertex = v then ρ / ‖D.germ d‖ else 0

/-- The exterior part of an edge after cutting at a named vertex. This is route data,
not a drawing of a graph with invented port vertices. -/
@[expose] noncomputable def outsideRoute {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (e : Fin G.2.length) : Route :=
  (D.route e).cutEnds (D.restrictionTime v ρ (e, false))
    (D.restrictionTime v ρ (e, true))

/-- A restriction radius gives independent small nonnegative cuts at every edge end. -/
theorem IsEmbedding.restrictionTime_mem {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (d : Dart G) :
    D.restrictionTime v ρ d ∈ Set.Ico 0 (1 / 3 : ℝ) := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  dsimp [restrictionTime]
  split_ifs with hd
  · refine ⟨div_nonneg hρ.le hn.le, ?_⟩
    rw [div_lt_iff₀ hn]
    linarith [hlen d hd]
  · constructor <;> norm_num

/-- The two independent end cuts leave a nonempty parameter interval on every route. -/
theorem IsEmbedding.restrictionTime_bounds {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (e : Fin G.2.length) :
    0 ≤ D.restrictionTime v ρ (e, false) ∧ 0 ≤ D.restrictionTime v ρ (e, true) ∧
      D.restrictionTime v ρ (e, false) + D.restrictionTime v ρ (e, true) < 1 := by
  have hs := hD.restrictionTime_mem v hρ hlen (e, false)
  have ht := hD.restrictionTime_mem v hρ hlen (e, true)
  exact ⟨hs.1, ht.1, by linarith [hs.2, ht.2]⟩

/-- The two ends of the exterior piece are their respective cut ports or unchanged
original endpoints, according to actual incidence with the named vertex. -/
theorem endpoint_outsideRoute {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (e : Fin G.2.length) (b : Bool) :
    (D.outsideRoute v ρ e).endpoint b =
      if Dart.vertex (e, b) = v then D.cutPort ρ (e, b) else D.vertex (Dart.vertex (e, b)) := by
  rw [outsideRoute, Route.endpoint_cutEnds]
  cases b <;> rw [Route.eval_near_end, D.endpoint_eq] <;>
    dsimp [restrictionTime] <;> split_ifs <;> simp [cutPort, germ]

/-- Exterior pieces retain continuous simplicity, with no assumptions on their slopes,
number of bends, loop status or the incidence of their other end. -/
theorem IsEmbedding.outsideRoute_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (e : Fin G.2.length) :
    (D.outsideRoute v ρ e).IsSimple := by
  obtain ⟨hs, ht, hst⟩ := hD.restrictionTime_bounds v hρ hlen e
  exact (hD.simple e).cutEnds hs ht hst

/-- Cutting the star does not create any point outside an old edge's continuous support. -/
theorem IsEmbedding.support_outsideRoute_subset {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (e : Fin G.2.length) :
    (D.outsideRoute v ρ e).support ⊆ (D.route e).support := by
  obtain ⟨hs, ht, hst⟩ := hD.restrictionTime_bounds v hρ hlen e
  exact (D.route e).support_cutEnds_subset hs ht hst

/-- A trim that cuts every end incident to the center at its boundary port meets the
closed ball only at those ports. A cut at an end not incident to the center can be chosen
independently, provided the two cuts leave a nonempty interval. -/
private theorem cutEnds_ball_contact {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) {ρ : ℝ}
    (hlocal : ∀ e (i : Fin (D.route e).segments) z,
      z ∈ Metric.closedBall (D.vertex v) ρ →
      z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v))
    (e : Fin G.2.length) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (hcuts : ∀ b, Dart.vertex (e, b) = v → (if b then t else s) = ρ / ‖D.germ (e, b)‖)
    (hgerm : ∀ b, Dart.vertex (e, b) = v → D.germ (e, b) ≠ 0)
    (i : Fin ((D.route e).cutEnds s t).segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hz : ((D.route e).cutEnds s t).eval i u ∈ Metric.closedBall (D.vertex v) ρ) :
    ∃ b, ((D.route e).cutEnds s t).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
      ((D.route e).cutEnds s t).eval i u = D.cutPort ρ (e, b) := by
  change Fin (D.route e).segments at i
  let τ := (D.route e).cutTime s t i u
  have hτ := (D.route e).cutTime_mem hs ht hst i hu
  have hbounds := (D.route e).cutTime_bounds hs ht hst i hu
  have heval : ((D.route e).cutEnds s t).eval i u = (D.route e).eval i τ :=
    (D.route e).eval_cutEnds s t i u
  have hτball : (D.route e).eval i τ ∈ Metric.closedBall (D.vertex v) ρ := heval ▸ hz
  have hseg : (D.route e).eval i τ ∈
      segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) :=
    lineMap_mem_segment ℝ _ _ hτ
  rcases hlocal e i _ hτball hseg with ⟨hi, hv⟩ | ⟨hi, hv⟩
  · have hi0 : i = 0 := Fin.ext hi
    have hsval : s = ρ / ‖D.germ (e, false)‖ := hcuts false hv
    have hlo : (D.route e).cutLower s i = s := by simp [Route.cutLower, hi]
    have hn : 0 < ‖D.germ (e, false)‖ := norm_pos_iff.mpr (hgerm false hv)
    have hpoint : (D.route e).eval i τ = D.vertex v + τ • D.germ (e, false) := by
      rw [hi0, show (0 : Fin (D.route e).segments) = (D.route e).endSegment false from rfl,
        ← show Route.endTime false τ = τ from rfl, Route.eval_near_end, D.endpoint_eq, hv]
      rfl
    have hdist : τ * ‖D.germ (e, false)‖ ≤ ρ := by
      rwa [Metric.mem_closedBall, hpoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hτ.1] at hτball
    have hτs : τ = s := by
      have hle : τ ≤ ρ / ‖D.germ (e, false)‖ := (le_div_iff₀ hn).mpr hdist
      rw [hlo] at hbounds
      exact le_antisymm (hle.trans_eq hsval.symm) hbounds.1
    have hu0 : u = 0 := ((D.route e).cutTime_eq_lower_iff hs ht hst i u).mp
      (hτs.trans hlo.symm)
    refine ⟨false, ?_, hv, ?_⟩
    · simp [Route.AtEnd, Route.position, hi, hu0]
    · rw [heval, hpoint, hτs, hsval, cutPort, hv]
  · have hilast : i = Fin.last (D.route e).bends := by
      fin_index [Route.segments]
    have htval : t = ρ / ‖D.germ (e, true)‖ := hcuts true hv
    have hhi : (D.route e).cutUpper t i = 1 - t := by simp [Route.cutUpper, hi]
    have hn : 0 < ‖D.germ (e, true)‖ := norm_pos_iff.mpr (hgerm true hv)
    have hpoint : (D.route e).eval i τ = D.vertex v + (1 - τ) • D.germ (e, true) := by
      calc
        _ = (D.route e).eval ((D.route e).endSegment true)
            (Route.endTime true (1 - τ)) := by
          rw [show Route.endTime true (1 - τ) = τ by dsimp [Route.endTime]; ring]
          rw [hilast]
          rfl
        _ = _ := by rw [Route.eval_near_end, D.endpoint_eq, hv]; rfl
    have hdist : (1 - τ) * ‖D.germ (e, true)‖ ≤ ρ := by
      rwa [Metric.mem_closedBall, hpoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr hτ.2)] at hτball
    have hτt : τ = 1 - t := by
      have hle : 1 - τ ≤ ρ / ‖D.germ (e, true)‖ := (le_div_iff₀ hn).mpr hdist
      rw [hhi] at hbounds
      rw [← htval] at hle
      linarith [hbounds.2]
    have hu1 : u = 1 := ((D.route e).cutTime_eq_upper_iff hs ht hst i u).mp
      (hτt.trans hhi.symm)
    refine ⟨true, ?_, hv, ?_⟩
    · simp only [Route.AtEnd, Route.position, hu1, ↓reduceIte]
      change (i.val : ℝ) + 1 = (D.route e).segments
      exact_mod_cast hi
    · rw [heval, hpoint, hτt, show 1 - (1 - t) = t by ring, htval, cutPort, hv]

/-- In an embedding, trimming the incident ends to the boundary makes the corresponding
ports the only contacts of the trimmed route with the closed ball. -/
theorem IsEmbedding.cutEnds_ball_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ}
    (hlocal : ∀ e (i : Fin (D.route e).segments) z,
      z ∈ Metric.closedBall (D.vertex v) ρ →
      z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v))
    (e : Fin G.2.length) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (hcuts : ∀ b, Dart.vertex (e, b) = v → (if b then t else s) = ρ / ‖D.germ (e, b)‖)
    (i : Fin ((D.route e).cutEnds s t).segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hz : ((D.route e).cutEnds s t).eval i u ∈ Metric.closedBall (D.vertex v) ρ) :
    ∃ b, ((D.route e).cutEnds s t).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
      ((D.route e).cutEnds s t).eval i u = D.cutPort ρ (e, b) :=
  D.cutEnds_ball_contact v hlocal e hs ht hst hcuts (fun b _ => hD.germ_ne_zero (e, b)) i hu hz

/-- For every sufficiently small positive common radius, the closed vertex balls are
pairwise disjoint and meet original routes only in incident end segments.
Trimming both ends of each route at its boundary ports removes
every contact with the balls except the corresponding end parameters of the trimmed
route. Routes may cross or retrace away from the vertex balls. -/
theorem exists_uniform_restriction {G : Graph} (D : PolygonalDrawing G)
    (hcontacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      ∀ v ∈ G.vertices, (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (hvertices : Set.InjOn D.vertex {v | v ∈ G.vertices})
    (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hgerm : ∀ d : Dart G, D.germ d ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      let time := fun d : Dart G => ρ / ‖D.germ d‖
      (∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
        Disjoint (Metric.closedBall (D.vertex v) ρ) (Metric.closedBall (D.vertex w) ρ)) ∧
      (∀ d, time d ∈ Set.Ioo (0 : ℝ) (1 / 3)) ∧
      (∀ v ∈ G.vertices, ∀ e (i : Fin (D.route e).segments) z,
        z ∈ Metric.closedBall (D.vertex v) ρ →
        z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
          (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v)) ∧
      ∀ e, let p := (D.route e).cutEnds (time (e, false)) (time (e, true))
        ∀ v ∈ G.vertices, ∀ (i : Fin p.segments) (t : ℝ), t ∈ Set.Icc 0 1 →
          p.eval i t ∈ Metric.closedBall (D.vertex v) ρ →
            ∃ b, p.AtEnd i t b ∧ Dart.vertex (e, b) = v ∧ p.eval i t = D.cutPort ρ (e, b) := by
  obtain ⟨ε, hε, hball⟩ := D.exists_uniform_restriction_radius
    hcontacts hvertices (fun d _ => hgerm d)
  refine ⟨ε, hε, fun ρ hρ => ?_⟩
  obtain ⟨hdisjoint, hlocal, hlen⟩ := hball ρ hρ
  let time := fun d : Dart G => ρ / ‖D.germ d‖
  have htime (d : Dart G) : time d ∈ Set.Ioo (0 : ℝ) (1 / 3) := by
    have hn := norm_pos_iff.mpr (hgerm d)
    exact ⟨div_pos hρ.1 hn, (div_lt_iff₀ hn).mpr (by linarith [hlen d (hdeclared d)])⟩
  refine ⟨hdisjoint, htime, hlocal, fun e v hv i t ht hz => ?_⟩
  have hs := htime (e, false)
  have ht' := htime (e, true)
  exact D.cutEnds_ball_contact v (hlocal v hv) e hs.1.le ht'.1.le
    (by linarith [hs.2, ht'.2]) (fun b _ => by cases b <;> rfl)
    (fun b _ => hgerm (e, b)) i ht hz

/-- Every point where an exterior piece meets the closed replacement ball is its own
boundary port at an original end incident to the replaced vertex. Thus an interior patch
cannot meet an exterior route interior. Both loop ends remain separate cases. -/
theorem IsEmbedding.outsideRoute_ball_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (hlocal : ∀ e (i : Fin (D.route e).segments) z,
      z ∈ Metric.closedBall (D.vertex v) ρ →
      z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v))
    (e : Fin G.2.length) (i : Fin (D.outsideRoute v ρ e).segments)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hz : (D.outsideRoute v ρ e).eval i u ∈ Metric.closedBall (D.vertex v) ρ) :
    ∃ b, (D.outsideRoute v ρ e).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
      (D.outsideRoute v ρ e).eval i u = D.cutPort ρ (e, b) := by
  obtain ⟨hs, ht, hst⟩ := hD.restrictionTime_bounds v hρ hlen e
  refine hD.cutEnds_ball_contact v hlocal e hs ht hst ?_ i hu hz
  intro b hb
  cases b <;> simp only [restrictionTime, hb, ↓reduceIte, Bool.false_eq_true]

/-- An actual embedding supplies its own common-radius cut and all exterior contact
conditions. No local disk, prescribed slopes, port coordinates or patch is a premise.
This stops at the exterior pieces: constructing and attaching a split patch is separate. -/
theorem IsEmbedding.exists_restriction {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) :
    ∃ ρ > 0,
      (∀ w ∈ G.1, D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v) ∧
      (∀ e, (D.outsideRoute v ρ e).IsSimple) ∧
      (∀ e, (D.outsideRoute v ρ e).support ⊆ (D.route e).support) ∧
      (∀ e (i : Fin (D.outsideRoute v ρ e).segments) (u : ℝ), u ∈ Set.Icc 0 1 →
        (D.outsideRoute v ρ e).eval i u ∈ Metric.closedBall (D.vertex v) ρ →
          ∃ b, (D.outsideRoute v ρ e).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
            (D.outsideRoute v ρ e).eval i u = D.cutPort ρ (e, b)) := by
  obtain ⟨ρ, hρ, hvertices, hlocal, hlen⟩ := hD.exists_restriction_radius v hv
  exact ⟨ρ, hρ, hvertices, hD.outsideRoute_simple v hρ hlen,
    hD.support_outsideRoute_subset v hρ hlen,
    fun e i _ hu hz => hD.outsideRoute_ball_contact v hρ hlen hlocal e i hu hz⟩

end Cslib.Complexity.Graph.PolygonalDrawing
