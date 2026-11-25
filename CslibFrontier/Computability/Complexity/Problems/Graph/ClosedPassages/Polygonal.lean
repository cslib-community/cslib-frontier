/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RegularContacts
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionCutEnds
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic.Linarith

/-!
# Intersection parity of polygonal closed passages

Cut the incident edge ends in disjoint vertex balls and join each paired set of ports by a
chord of its vertex circle. Endpoint incidences cancel because every supported dart
occurs once. Crossings of the chords count local rotation alternation.

Regular contacts require distinct listed points on each route, including its two ends.
The drawing therefore uses open routes and has no loop edges. Parallel edges with bends,
multiple visits to a vertex by a passage system, and transverse open-segment crossings
are allowed.

## Main results

* `ClosedPassages.intersectionParity_eq_sum_route_intersectionParity` identifies the parity of
  alternating passage pairs with the indexed crossing parity between their edge supports.
* `ClosedPassages.not_alternates_of_unique_shared_passages` rules out alternation when only one
  pair of passages shares a vertex and all crossing counts across the supports are even.
-/

public section

namespace Cslib.Complexity.Graph.ClosedPassages

open Cslib.Polygonal

section

variable {G : Graph} {x : Fin G.edges.length → Bool} (P : ClosedPassages G x)

private noncomputable def trimmedRoute (D : PolygonalDrawing G) (ρ : ℝ)
    (e : Fin G.edges.length) : Route :=
  (D.route e).cutEnds (ρ / ‖D.germ (e, false)‖) (ρ / ‖D.germ (e, true)‖)

private theorem trimmedRoute_endpoint (D : PolygonalDrawing G) (ρ : ℝ)
    (e : Fin G.edges.length) (b : Bool) :
    (trimmedRoute D ρ e).endpoint b = D.cutPort ρ (e, b) := by
  rw [trimmedRoute, Route.endpoint_cutEnds, D.cutPort_eq_eval]
  cases b <;> rfl

private noncomputable def passageRoute (D : PolygonalDrawing G) (ρ : ℝ) :
    Fin G.edges.length ⊕ Fin P.count → Route :=
  Sum.elim (trimmedRoute D ρ) (fun i =>
    Route.line (D.cutPort ρ (P.dart i false)) (D.cutPort ρ (P.dart i true)))

private def passageWeight : Fin G.edges.length ⊕ Fin P.count → Bool :=
  Sum.elim x (fun _ => true)

open Classical in
private theorem sum_passageRoute_endpoints_eq_false (D : PolygonalDrawing G) (ρ : ℝ) (z : ℂ) :
    let R := P.passageRoute D ρ
    let w := P.passageWeight
    (∑ i, ((if (R i).start = z then w i else 0) +
      (if (R i).finish = z then w i else 0))) = false := by
  classical
  let f (d : Dart G) : Bool := if D.cutPort ρ d = z then true else 0
  dsimp only
  rw [Fintype.sum_sum_type]
  change (∑ e, ((if (trimmedRoute D ρ e).start = z then x e else 0) +
      (if (trimmedRoute D ρ e).finish = z then x e else 0))) +
    (∑ i : Fin P.count, (f (P.dart i false) + f (P.dart i true))) = false
  have hs (e : Fin G.edges.length) : (trimmedRoute D ρ e).start =
      D.cutPort ρ (e, false) := trimmedRoute_endpoint D ρ e false
  have ht (e : Fin G.edges.length) : (trimmedRoute D ρ e).finish =
      D.cutPort ρ (e, true) := trimmedRoute_endpoint D ρ e true
  simp only [hs, ht]
  have he : (∑ e, ((if D.cutPort ρ (e, false) = z then x e else 0) +
      (if D.cutPort ρ (e, true) = z then x e else 0))) =
      ∑ d : Dart G, if x d.1 = true then f d else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    rw [Fintype.sum_bool]
    cases hx : x e <;> simp [f, add_comm, Bool.zero_eq_false]
  rw [he, P.sum_ports f]
  exact BooleanRing.add_self _

end

private theorem chord_inter_iff_alternates {G : Graph} {x y : Fin G.edges.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y)
    {D : PolygonalDrawing G} {r : RotationSystem G} (hR : D.Realizes r)
    {ρ : ℝ} (hρ : 0 < ρ) (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hdisks : ∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
      Disjoint (Metric.closedBall (D.vertex v) ρ) (Metric.closedBall (D.vertex w) ρ))
    (hedges : ∀ e, x e = true → y e = true → False)
    (i : Fin P.count) (j : Fin Q.count) :
    (openSegment ℝ (D.cutPort ρ (P.dart i false)) (D.cutPort ρ (P.dart i true)) ∩
      openSegment ℝ (D.cutPort ρ (Q.dart j false)) (D.cutPort ρ (Q.dart j true))).Nonempty ↔
      r.Alternates (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true) := by
  have hne (b c : Bool) : P.dart i b ≠ Q.dart j c := by
    intro he
    exact hedges _ (P.supported i b) (by rw [he]; exact Q.supported j c)
  have hP : (P.dart i false).vertex = (P.dart i true).vertex := P.vertex_eq i
  have hQ : (Q.dart j false).vertex = (Q.dart j true).vertex := Q.vertex_eq j
  by_cases hv : (P.dart i false).vertex = (Q.dart j false).vertex
  · exact hR.cutPort_chords_inter_iff_alternates hρ _ _ _ _
      (P.dart_ne i) (Q.dart_ne j) (hne false false) (hne false true)
      (hne true false) (hne true true) hP hQ hv
  · have hport (d : Dart G) : D.cutPort ρ d ∈ Metric.closedBall (D.vertex d.vertex) ρ := by
      rw [Metric.mem_closedBall, D.dist_cutPort hρ.le d (hR.nonzero d)]
    have hsub (d e : Dart G) (hde : d.vertex = e.vertex) :
        openSegment ℝ (D.cutPort ρ d) (D.cutPort ρ e) ⊆
          Metric.closedBall (D.vertex d.vertex) ρ := by
      apply (openSegment_subset_segment ℝ _ _).trans
      exact (convex_closedBall _ _).segment_subset (hport d) (hde.symm ▸ hport e)
    have hdisj := hdisks _ (hdeclared (P.dart i false)) _ (hdeclared (Q.dart j false)) hv
    constructor
    · rintro ⟨z, hzp, hzq⟩
      exact (Set.disjoint_left.mp hdisj (hsub _ _ hP hzp) (hsub _ _ hQ hzq)).elim
    · rintro ⟨_, _, _, _, _, _, _, _, h, _⟩
      exact (hv h).elim


open Classical in
/-- The total indexed intersection parity of edge-disjoint closed passages is their
local alternation parity in the drawing's rotation. Each edge is drawn by a simple route
with regular contacts, and the declared vertices occupy distinct points. -/
theorem intersectionParity_eq_sum_route_intersectionParity {G : Graph}
    {x y : Fin G.edges.length → Bool} (P : ClosedPassages G x) (Q : ClosedPassages G y)
    {D : PolygonalDrawing G} {r : RotationSystem G}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {v | v ∈ G.vertices})
    (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hedges : ∀ e, x e = true → y e = true → False) :
    r.intersectionParity P Q =
      ∑ f, y f * ∑ e, x e * (D.route e).intersectionParity (D.route f) := by
  classical
  obtain ⟨ε, hε, hball⟩ :=
    D.exists_uniform_restriction hreg.vertex_contacts hvertices hdeclared hR.nonzero
  obtain ⟨ρ, hρ⟩ := exists_between hε
  obtain ⟨hdisks, htime, hlocal, hcut⟩ := hball ρ hρ
  let E := Fin G.edges.length
  let t (d : Dart G) := ρ / ‖D.germ d‖
  let M := trimmedRoute D ρ
  let chord (a b : Dart G) := Route.line (D.cutPort ρ a) (D.cutPort ρ b)
  have hsum (e : E) : t (e, false) + t (e, true) < 1 := by
    linarith [(htime (e, false)).2, (htime (e, true)).2]
  have hcut' (e : E) (v : ℕ) (hv : v ∈ G.vertices) {z : ℂ}
      (hz : z ∈ (M e).support) (hball : z ∈ Metric.closedBall (D.vertex v) ρ) :
      ∃ b, Dart.vertex (e, b) = v ∧ z = D.cutPort ρ (e, b) := by
    obtain ⟨i, u, hu, he⟩ := ((M e).mem_support_iff z).mp hz
    obtain ⟨b, _, hvb, hp⟩ := hcut e v hv i u hu (he.symm ▸ hball)
    exact ⟨b, hvb, he.symm.trans hp⟩
  have hinj := D.cutPort_injective_of_disjoint_balls hρ.1 hdeclared hR.nonzero
    hR.directions_injective hdisks
  have portBall (d : Dart G) : D.cutPort ρ d ∈ Metric.closedBall (D.vertex d.vertex) ρ := by
    rw [Metric.mem_closedBall, D.dist_cutPort hρ.1.le d (hR.nonzero d)]
  have portSphere (d : Dart G) : D.cutPort ρ d ∈ Metric.sphere (D.vertex d.vertex) ρ := by
    rw [Metric.mem_sphere, D.dist_cutPort hρ.1.le d (hR.nonzero d)]
  have portAvoid (d : Dart G) (e : E) (hne : d.1 ≠ e) :
      D.cutPort ρ d ∉ (M e).support := by
    intro hz
    obtain ⟨b, _, h⟩ := hcut' e d.vertex (hdeclared d) hz (portBall d)
    exact hne (congrArg Prod.fst (hinj h))
  have middleAvoid (e f : E) (hne : e ≠ f) (k : Fin ((M e).segments + 1)) :
      (M e).point k ∉ (M f).support := by
    by_cases hlo : k.val = 0
    · have hk : k = 0 := Fin.ext hlo
      subst k
      change (M e).endpoint false ∉ (M f).support
      rw [trimmedRoute_endpoint]
      exact portAvoid (e, false) f hne
    by_cases hhi : k.val = (D.route e).segments
    · have hk : k = Fin.last (D.route e).segments := Fin.ext hhi
      subst k
      change (M e).endpoint true ∉ (M f).support
      rw [trimmedRoute_endpoint]
      exact portAvoid (e, true) f hne
    intro hz
    have hkbound : k.val < (D.route e).segments + 1 := k.isLt
    have hj : k.val < (D.route e).segments := by omega
    let i : Fin (D.route e).segments := ⟨k.val, hj⟩
    have hk : i.castSucc = k := Fin.ext rfl
    have he : (D.route e).eval i 0 = (M e).point k := by
      simp only [Route.eval, AffineMap.lineMap_apply_zero, hk]
      exact (show (M e).point k = (D.route e).point k by
        simp only [M, trimmedRoute, Route.cutEnds, ite_eq_right hlo, ite_eq_right hhi]).symm
    have hzOld : (M e).point k ∈ (D.route f).support :=
      (D.route f).support_cutEnds_subset (htime (f, false)).1.le (htime (f, true)).1.le
        (hsum f) hz
    obtain ⟨j, u, hu, hu_eq⟩ := ((D.route f).mem_support_iff _).mp hzOld
    rcases hreg.edge_contact_cases ⟨e, i⟩ ⟨f, j⟩ hne
        (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) hu (he.trans hu_eq.symm) with
      ⟨hopen, _⟩ | ⟨b, _, hb, _, _⟩
    · exact (lt_irrefl _ hopen.1).elim
    have hcast : (k.val : ℝ) < (D.route e).segments := by exact_mod_cast hj
    have hnz : (k.val : ℝ) ≠ 0 := by exact_mod_cast hlo
    cases b
    · change (k.val : ℝ) + 0 = 0 at hb
      exact hnz (by simpa only [add_zero] using hb)
    · change (k.val : ℝ) + 0 = (D.route e).segments at hb
      exact (ne_of_lt hcast) (by simpa only [add_zero] using hb)
  have chordBall (a b : Dart G) (hv : a.vertex = b.vertex) :
      (chord a b).support ⊆ Metric.closedBall (D.vertex a.vertex) ρ := by
    rw [Route.support_line]
    exact (convex_closedBall _ _).segment_subset (portBall a) (hv.symm ▸ portBall b)
  have chordOpen (a b : Dart G) (hv : a.vertex = b.vertex) (hne : a ≠ b) :
      openSegment ℝ (D.cutPort ρ a) (D.cutPort ρ b) ⊆ Metric.ball (D.vertex a.vertex) ρ :=
    openSegment_subset_ball_of_ne (portBall a) (hv.symm ▸ portBall b) (hinj.ne hne)
  have chordEnd (a b : Dart G) (hv : a.vertex = b.vertex) (hne : a ≠ b) {z : ℂ}
      (hz : z ∈ (chord a b).support) (hs : z ∈ Metric.sphere (D.vertex a.vertex) ρ) :
      z = D.cutPort ρ a ∨ z = D.cutPort ρ b := by
    rw [Route.support_line, segment_eq_image_lineMap] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · left
      rw [← hu0, AffineMap.lineMap_apply_zero]
    rcases eq_or_lt_of_le hu.2 with hu1 | hu1
    · right
      rw [hu1, AffineMap.lineMap_apply_one]
    exact (Set.disjoint_left.mp Metric.sphere_disjoint_ball hs
      (chordOpen a b hv hne (lineMap_mem_openSegment ℝ _ _ ⟨hu0, hu1⟩))).elim
  have mixedDisjoint (e : E) (a b : Dart G) (hv : a.vertex = b.vertex) (hne : a ≠ b)
      (ha : a.1 ≠ e) (hb : b.1 ≠ e) : Disjoint (M e).support (chord a b).support := by
    rw [Set.disjoint_left]
    intro z hm hc
    obtain ⟨c, hcv, hcz⟩ := hcut' e a.vertex (hdeclared a) hm (chordBall a b hv hc)
    rcases chordEnd a b hv hne hc (hcz.symm ▸ hcv ▸ portSphere (e, c)) with he | he
    · exact ha (congrArg Prod.fst (hinj (he.symm.trans hcz)))
    · exact hb (congrArg Prod.fst (hinj (he.symm.trans hcz)))
  have portAvoidChord (a b c : Dart G) (hbc : b.vertex = c.vertex) (hne : b ≠ c)
      (hab : a ≠ b) (hac : a ≠ c) : D.cutPort ρ a ∉ (chord b c).support := by
    intro hz
    by_cases hv : a.vertex = b.vertex
    · rcases chordEnd b c hbc hne hz (hv ▸ portSphere a) with he | he
      · exact hab (hinj he)
      · exact hac (hinj he)
    exact Set.disjoint_left.mp (hdisks _ (hdeclared a) _ (hdeclared b) hv) (portBall a)
      (chordBall b c hbc hz)
  have ne (e f : E) (he : x e = true) (hf : y f = true) : e ≠ f := by
    intro h
    exact hedges f (h ▸ he) hf
  have piecesNe {w : E → Bool} (R : ClosedPassages G w) (i : E ⊕ Fin R.count)
      (k : Fin (R.passageRoute D ρ i).segments) :
      (R.passageRoute D ρ i).point k.castSucc ≠ (R.passageRoute D ρ i).point k.succ := by
    cases i with
    | inl e =>
        exact ((hsimple e).cutEnds (htime (e, false)).1.le (htime (e, true)).1.le
          (hsum e)).segment_ne k
    | inr j => exact (Route.isSimple_line (hinj.ne (R.dart_ne j))).segment_ne k
  have avoid {w w' : E → Bool} (R : ClosedPassages G w) (S : ClosedPassages G w')
      (hsep : ∀ e f, w e = true → w' f = true → e ≠ f)
      (i : E ⊕ Fin R.count) (j : E ⊕ Fin S.count)
      (hi : R.passageWeight i = true) (hj : S.passageWeight j = true)
      (k : Fin ((R.passageRoute D ρ i).segments + 1)) :
      (R.passageRoute D ρ i).point k ∉ (S.passageRoute D ρ j).support := by
    rcases i with e | i <;> rcases j with f | j
    · exact middleAvoid e f (hsep e f hi hj) k
    · exact fun hz => Set.disjoint_left.mp
        (mixedDisjoint e (S.dart j false) (S.dart j true) (S.vertex_eq j) (S.dart_ne j)
          (hsep _ _ hi (S.supported j false)).symm (hsep _ _ hi (S.supported j true)).symm)
        ((M e).point_mem_support k) hz
    · exact fun hz => Set.disjoint_left.mp
        (mixedDisjoint f (R.dart i false) (R.dart i true) (R.vertex_eq i) (R.dart_ne i)
          (hsep _ _ (R.supported i false) hj) (hsep _ _ (R.supported i true) hj))
        hz (Route.point_mem_support _ k)
    · have hport (b : Bool) :
          D.cutPort ρ (R.dart i b) ∉ (S.passageRoute D ρ (.inr j)).support :=
        portAvoidChord (R.dart i b) (S.dart j false) (S.dart j true)
          (S.vertex_eq j) (S.dart_ne j)
          (fun h => hsep _ _ (R.supported i b) (S.supported j false) (congrArg Prod.fst h))
          (fun h => hsep _ _ (R.supported i b) (S.supported j true) (congrArg Prod.fst h))
      refine Fin.lastCases (hport true) (fun l => ?_) k
      have hl : l = 0 := Subsingleton.elim (α := Fin 1) _ _
      subst l
      exact hport false
  have outsideParity (e f : E) (hne : e ≠ f) :
      (M e).intersectionParity (M f) = (D.route e).intersectionParity (D.route f) := by
    have outer (e f : E) (hne : e ≠ f) (b : Bool) {z : ℂ}
        (hz : z ∈ segment ℝ ((D.route e).endpoint b) ((M e).endpoint b))
        (hw : z ∈ (D.route f).support) : z = (D.route e).endpoint b := by
      rw [D.endpoint_eq, trimmedRoute_endpoint] at hz
      rw [D.endpoint_eq]
      obtain ⟨_, _, he⟩ := D.eq_vertex_of_mem_cutPort_segment_and_route hρ.1 (e, b)
        (hR.nonzero (e, b)) hR.directions_injective f hne (hlocal _ (hdeclared (e, b)) f) hz hw
      exact he
    have cut (e f : E) (hne : e ≠ f) {q : Route} (hq : q.support ⊆ (D.route f).support) :
        (M e).intersectionParity q = (D.route e).intersectionParity q := by
      apply Route.intersectionParity_cutEnds_left (htime (e, false)).1.le
        (htime (e, true)).1.le (hsum e)
      · exact fun z hz hqz => outer e f hne false hz (hq hqz)
      · intro z hz hqz
        change z ∈ segment ℝ (M e).finish (D.route e).finish at hz
        rw [segment_symm ℝ (M e).finish (D.route e).finish] at hz
        exact outer e f hne true hz (hq hqz)
    calc
      _ = (D.route e).intersectionParity (M f) :=
        cut e f hne (q := M f) ((D.route f).support_cutEnds_subset (htime (f, false)).1.le
          (htime (f, true)).1.le (hsum f))
      _ = (M f).intersectionParity (D.route e) := Route.intersectionParity_symm _ _
      _ = (D.route f).intersectionParity (D.route e) := cut f e hne.symm (fun _ hz => hz)
      _ = _ := Route.intersectionParity_symm _ _
  have zeroParity {p q : Route} (h : Disjoint p.support q.support) :
      p.intersectionParity q = false := by
    unfold Route.intersectionParity
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    apply decide_eq_false
    rintro ⟨z, hp, hq⟩
    exact Set.disjoint_left.mp h
      (Set.mem_iUnion.mpr ⟨i, openSegment_subset_segment ℝ _ _ hp⟩)
      (Set.mem_iUnion.mpr ⟨j, openSegment_subset_segment ℝ _ _ hq⟩)
  have cancel := Route.sum_intersectionParity_eq_false_of_even
    (P.passageRoute D ρ) (Q.passageRoute D ρ) P.passageWeight Q.passageWeight
    (piecesNe P) (piecesNe Q) (avoid P Q ne) (fun i j hi hj => avoid Q P
      (fun f e hf he => (ne e f he hf).symm) j i hj hi)
    (P.sum_passageRoute_endpoints_eq_false D ρ) (Q.sum_passageRoute_endpoints_eq_false D ρ)
  let edgeParity := ∑ f, y f * ∑ e, x e * (D.route e).intersectionParity (D.route f)
  have hsumParity : (∑ j, Q.passageWeight j * ∑ i, P.passageWeight i *
      (P.passageRoute D ρ i).intersectionParity (Q.passageRoute D ρ j)) =
      edgeParity + r.intersectionParity P Q := by
    rw [Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro f _
      change y f * (∑ i, P.passageWeight i *
        (P.passageRoute D ρ i).intersectionParity (M f)) = _
      cases hf : y f
      · simp [← Bool.zero_eq_false]
      rw [Fintype.sum_sum_type]
      have hz : (∑ i : Fin P.count, (chord (P.dart i false) (P.dart i true)).intersectionParity
          (M f)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact zeroParity (mixedDisjoint f _ _ (P.vertex_eq i) (P.dart_ne i)
          (ne _ _ (P.supported i false) hf) (ne _ _ (P.supported i true) hf)).symm
      simp only [passageWeight, passageRoute, Sum.elim_inl, Sum.elim_inr,
        ← Bool.one_eq_true, one_mul]
      change (∑ e, x e * (M e).intersectionParity (M f)) +
        (∑ i : Fin P.count, (chord (P.dart i false) (P.dart i true)).intersectionParity
          (M f)) = _
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro e _
      cases he : x e
      · simp [← Bool.zero_eq_false]
      · rw [outsideParity e f (ne e f he hf)]
    · apply Finset.sum_congr rfl
      intro j _
      let q := chord (Q.dart j false) (Q.dart j true)
      change (1 : Bool) * (∑ i, P.passageWeight i *
        (P.passageRoute D ρ i).intersectionParity q) = _
      rw [one_mul, Fintype.sum_sum_type]
      have hz : (∑ e, x e * (M e).intersectionParity q) = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        cases he : x e
        · simp [← Bool.zero_eq_false]
        change (1 : Bool) * (M e).intersectionParity q = 0
        rw [one_mul]
        exact zeroParity (mixedDisjoint e _ _ (Q.vertex_eq j) (Q.dart_ne j)
          (ne _ _ he (Q.supported j false)).symm (ne _ _ he (Q.supported j true)).symm)
      simp only [passageWeight, passageRoute, Sum.elim_inl, Sum.elim_inr,
        ← Bool.one_eq_true, one_mul]
      change (∑ e, x e * (M e).intersectionParity q) +
        (∑ i : Fin P.count, (chord (P.dart i false) (P.dart i true)).intersectionParity q) = _
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      change Route.intersectionParity
        (Route.line (D.cutPort ρ (P.dart i false)) (D.cutPort ρ (P.dart i true)))
        (Route.line (D.cutPort ρ (Q.dart j false)) (D.cutPort ρ (Q.dart j true))) = _
      rw [Route.intersectionParity_line_line]
      exact decide_eq_decide.mpr
        (chord_inter_iff_alternates P Q hR hρ.1 hdeclared hdisks hedges i j)
  rw [hsumParity] at cancel
  simpa only [← Bool.zero_eq_false, ← add_assoc, BooleanRing.add_self, zero_add, add_zero] using
    congrArg (edgeParity + ·) cancel

/-- If two edge-disjoint closed passage systems meet at just one pair of passages,
that pair cannot alternate when every crossing count between the two edge supports is even. -/
theorem not_alternates_of_unique_shared_passages {G : Graph}
    {x y : Fin G.edges.length → Bool} (P : ClosedPassages G x) (Q : ClosedPassages G y)
    {D : PolygonalDrawing G} {r : RotationSystem G}
    (hR : D.Realizes r) (hreg : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hvertices : Set.InjOn D.vertex {v | v ∈ G.vertices})
    (hdeclared : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hedges : ∀ e, x e = true → y e = true → False)
    (heven : ∀ e f, x e = true → y f = true →
      (D.route e).intersectionParity (D.route f) = false)
    (i₀ : Fin P.count) (j₀ : Fin Q.count)
    (hunique : ∀ i j, (P.dart i false).vertex = (Q.dart j false).vertex → i = i₀ ∧ j = j₀) :
    ¬ r.Alternates (P.dart i₀ false) (P.dart i₀ true) (Q.dart j₀ false) (Q.dart j₀ true) := by
  classical
  have hzero : r.intersectionParity P Q = false := by
    rw [P.intersectionParity_eq_sum_route_intersectionParity Q hR hreg hsimple
      hvertices hdeclared hedges, ← Bool.zero_eq_false]
    apply Finset.sum_eq_zero
    intro f _
    cases hf : y f
    · rw [← Bool.zero_eq_false, zero_mul]
    · apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro e _
      cases he : x e
      · rw [← Bool.zero_eq_false, zero_mul]
      · rw [heven e f he hf, ← Bool.zero_eq_false, mul_zero]
  intro halt
  have hpair (i : Fin P.count) (j : Fin Q.count)
      (h : r.Alternates (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true)) :
      i = i₀ ∧ j = j₀ := by
    obtain ⟨_, _, _, _, _, _, _, _, hv, _⟩ := h
    exact hunique i j hv
  unfold RotationSystem.intersectionParity at hzero
  rw [Finset.sum_eq_single j₀, Finset.sum_eq_single i₀, decide_eq_true halt] at hzero
  · cases hzero
  · intro i _ hi
    apply decide_eq_false
    intro h
    exact hi (hpair i j₀ h).1
  · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    apply decide_eq_false
    intro h
    exact hj (hpair i j h).2
  · simp

end Cslib.Complexity.Graph.ClosedPassages
