/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Concatenate
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityIntersections
public import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Connected.PathConnected
import CslibFrontier.Foundations.Geometry.Polygonal.ComplexMul
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import CslibFrontier.Foundations.Geometry.Polygonal.SampledRoute
import CslibFrontier.Foundations.Geometry.PuncturedPaths
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Indexed endpoint and observation parity of polygonal routes

`Route.sum_segment_endpoint_incidence` keeps both ends and every internal bend occurrence.
`Route.rayParity_endpoints_add_eq_sum_intersections` applies the straight observation law
on every actual segment, with explicit reciprocal closed endpoint exclusions. Route ray
parity also adds under concatenation and is invariant under reversal, so a closed excursion
retains the loop's parity when the connector is retraced. A sufficiently small triangular
loop isolates any one ray-parity observation from a finite set. In an open path-connected
region a polygonal connector bases this excursion at any unmarked point. Concatenating
such excursions realizes a prescribed subset of odd observations.

A closed route has zero parity outside a convex region containing it. Local replacements
inside such a region preserve parity. The same principle gives a positive radius for
simultaneous perturbations of the interior listed points at any observation off the route.
-/

public section

namespace Cslib.Polygonal.Route

private theorem sum_adjacent_bool {n : ℕ} (f : Fin (n + 1) → Bool) :
    (∑ i : Fin n, (f i.castSucc + f i.succ)) = f 0 + f (Fin.last n) := by
  induction n with
  | zero => simp [BooleanRing.add_self]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, ← Fin.succ_last]
    simp only [Fin.succ_castSucc, ih (fun i => f i.castSucc), Fin.castSucc_zero]
    rw [add_assoc, ← add_assoc (f (Fin.last n).castSucc), BooleanRing.add_self, zero_add]

private theorem sum_segment_endpoints (p : Route) (observe : ℂ → Bool) :
    (∑ i : Fin p.segments, (observe (p.point i.castSucc) + observe (p.point i.succ))) =
      observe p.start + observe p.finish :=
  sum_adjacent_bool (fun i => observe (p.point i))

/-- The weighted endpoint incidence of all actual route segments is the incidence of
its two parameter ends. Internal bends cancel, including repeated geometric points. -/
theorem sum_segment_endpoint_incidence (p : Route) (weight : Bool) (u z : ℂ) :
    (∑ i : Fin p.segments,
      ((if u * p.point i.castSucc = z then weight else 0) +
        (if u * p.point i.succ = z then weight else 0))) =
      (if u * p.start = z then weight else 0) +
        (if u * p.finish = z then weight else 0) := by
  classical
  exact sum_segment_endpoints p (fun w => if u * w = z then weight else 0)

open Classical in
/-- Observation along an actual route counts indexed open segment-pair events. Its nodes
avoid the selected arrangement supports, and selected arrangement ends avoid its whole
support. Even incidence cancels endpoint-height jumps; remote equal heights are allowed.
No simplicity, no-triple or event enumeration is assumed. -/
theorem rayParity_endpoints_add_eq_sum_intersections {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (p : Route)
    (hheight : ∀ i, (a i).im ≠ (b i).im)
    (hpheight : ∀ j : Fin p.segments, (p.point j.castSucc).im ≠ (p.point j.succ).im)
    (hnodes : ∀ j : Fin (p.segments + 1), ∀ i, x i = true →
      p.point j ∉ segment ℝ (a i) (b i))
    (hends : ∀ i, x i = true → a i ∉ p.support ∧ b i ∉ p.support)
    (heven : ∀ z : ℂ, (∑ i, ((if a i = z then x i else 0) +
      (if b i = z then x i else 0))) = false) :
    rayParity a b x p.finish + rayParity a b x p.start =
      ∑ j : Fin p.segments, ∑ i, x i * decide
        ((openSegment ℝ (a i) (b i) ∩
          openSegment ℝ (p.point j.castSucc) (p.point j.succ)).Nonempty) := by
  classical
  have hpiece (j : Fin p.segments) :
      rayParity a b x (p.point j.succ) + rayParity a b x (p.point j.castSucc) =
        ∑ i, x i * decide ((openSegment ℝ (a i) (b i) ∩
          openSegment ℝ (p.point j.castSucc) (p.point j.succ)).Nonempty) := by
    apply rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
      a b x _ _ hheight (hpheight j) (hnodes j.castSucc) (hnodes j.succ)
    · exact fun i hx hz => (hends i hx).1 (Set.mem_iUnion.mpr ⟨j, hz⟩)
    · exact fun i hx hz => (hends i hx).2 (Set.mem_iUnion.mpr ⟨j, hz⟩)
    · exact fun z _ => sum_rayParity_endpoint_jumps_eq_zero a b x heven z
  calc
    _ = ∑ j : Fin p.segments,
        (rayParity a b x (p.point j.castSucc) + rayParity a b x (p.point j.succ)) := by
      rw [sum_segment_endpoints, add_comm]
    _ = _ := Finset.sum_congr rfl fun j _ => (add_comm _ _).trans (hpiece j)

/-- Ray parity of the actual route segments after multiplication by a common complex
coordinate factor. Every occurrence contributes, including coincident or retraced pieces. -/
@[expose] noncomputable def rayParity (p : Route) (u z : ℂ) : Bool :=
  Cslib.Polygonal.rayParity (fun i : Fin p.segments => u * p.point i.castSucc)
    (fun i => u * p.point i.succ) (fun _ => true) (u * z)

/-- When the ends match, each piece of a concatenation contributes its original bit. -/
theorem rayParity_concat (p q : Route) (h : p.finish = q.start) (u z : ℂ) :
    (p.concat q).rayParity u z = p.rayParity u z + q.rayParity u z := by
  classical
  unfold Route.rayParity Cslib.Polygonal.rayParity
  exact sum_segments_concat p q h (fun a b =>
    if RayCrosses (u * a) (u * b) (u * z) then true else 0)

open Classical in
/-- The sole segment of a straight route contributes its crossing bit. -/
theorem rayParity_line (a b u z : ℂ) :
    (line a b).rayParity u z = decide (RayCrosses (u * a) (u * b) (u * z)) := by
  simp only [Route.rayParity, Cslib.Polygonal.rayParity]
  exact (Fin.sum_univ_one _).trans (by simp [line, Bool.zero_eq_false])

/-- Cutting a straight route into two at an interior point preserves the ray parity of
the concatenation, including at observations on the cut height. -/
theorem rayParity_line_split (a b u z : ℂ) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    let m := AffineMap.lineMap a b t
    ((line a m).concat (line m b)).rayParity u z = (line a b).rayParity u z := by
  intro m
  have hm : u * m = AffineMap.lineMap (u * a) (u * b) t :=
    ((LinearMap.mulLeft ℂ u).restrictScalars ℝ).toAffineMap.apply_lineMap a b t
  rw [rayParity_concat _ _ rfl, rayParity_line, rayParity_line, rayParity_line, hm]
  exact decide_rayCrosses_split _ _ _ ht

/-- Reversing a route leaves its ray parity unchanged at every point. -/
theorem rayParity_reverse (p : Route) (u z : ℂ) :
    p.reverse.rayParity u z = p.rayParity u z := by
  classical
  unfold Route.rayParity Cslib.Polygonal.rayParity
  let e : Fin p.segments ≃ Fin p.segments := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  change (∑ i : Fin p.segments,
    if RayCrosses (u * p.point i.castSucc.rev) (u * p.point i.succ.rev) (u * z)
      then (true : Bool) else 0) = _
  calc
    _ = ∑ i : Fin p.segments,
        if RayCrosses (u * p.point i.rev.castSucc) (u * p.point i.rev.succ) (u * z)
          then (true : Bool) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.rev_castSucc, Fin.rev_succ,
        rayCrosses_reverse (u * p.point i.rev.castSucc) (u * p.point i.rev.succ) (u * z)]
    _ = _ := Equiv.sum_comp e (fun i =>
      if RayCrosses (u * p.point i.castSucc) (u * p.point i.succ) (u * z) then true else 0)

private theorem start_concat {p q : Route} (h : p.finish = q.start) :
    (p.concat q).start = p.start :=
  endpoint_concat p q h false

private theorem finish_concat {p q : Route} (h : p.finish = q.start) :
    (p.concat q).finish = q.finish :=
  endpoint_concat p q h true

private theorem closed_excursion_return_join (p q : Route)
    (hjoin : p.finish = q.start) (hclosed : q.finish = q.start) :
    (p.concat q).finish = p.reverse.start :=
  (finish_concat hjoin).trans ((hclosed.trans hjoin.symm).trans (p.endpoint_reverse false).symm)

/-- Following a connector to a closed route and retracing the connector contributes
exactly the parity of the closed route. -/
theorem rayParity_closed_excursion (c p : Route) (hjoin : c.finish = p.start)
    (hclosed : p.finish = p.start) (u z : ℂ) :
    ((c.concat p).concat c.reverse).rayParity u z = p.rayParity u z := by
  have hreturn := closed_excursion_return_join c p hjoin hclosed
  rw [rayParity_concat (c.concat p) c.reverse hreturn, rayParity_concat c p hjoin,
    rayParity_reverse]
  calc
    _ = (c.rayParity u z + c.rayParity u z) + p.rayParity u z := by ac_rfl
    _ = _ := by rw [BooleanRing.add_self, zero_add]

private theorem right_slice_iff {K : Set ℂ} (hK : Convex ℝ K) {z w : ℂ}
    (hz : z ∉ K) (hw : w ∈ K) (hh : w.im = z.im) :
    z.re < w.re ↔ ∃ y ∈ K, y.im = z.im ∧ z.re < y.re := by
  refine ⟨fun h => ⟨w, hw, hh, h⟩, ?_⟩
  rintro ⟨y, hy, hyim, hyre⟩
  by_contra! hzw
  have hx : z.re ∈ segment ℝ w.re y.re :=
    segment_eq_Icc (hzw.trans hyre.le) ▸ ⟨hzw, hyre.le⟩
  obtain ⟨t, ht, he⟩ := segment_eq_image_lineMap ℝ w.re y.re ▸ hx
  have heq : AffineMap.lineMap w y t = z := Complex.ext
    ((Complex.reLm.toAffineMap.apply_lineMap w y t).trans he)
    (by rw [lineMap_im, hh, hyim, sub_self, mul_zero, add_zero])
  exact hz (heq ▸ hK.segment_subset hw hy (lineMap_mem_segment ℝ w y ht))

private theorem decide_height_between (a b h : ℝ) :
    decide (h ∈ Set.Ico (min a b) (max a b)) =
      decide (a ≤ h) + decide (b ≤ h) := by
  simp only [Set.mem_Ico, min_le_iff, lt_iff_not_ge]
  by_cases ha : a ≤ h <;> by_cases hb : b ≤ h <;>
    simp [ha, hb, Bool.add_eq_xor]

/-- A closed route supported in a convex set has zero ray parity outside the set.
Horizontal segments and repeated nodes are allowed. -/
theorem rayParity_eq_false_of_support_subset_convex (p : Route) {K : Set ℂ}
    (hclosed : p.finish = p.start) (hK : Convex ℝ K) (hp : p.support ⊆ K)
    {z : ℂ} (hz : z ∉ K) {u : ℂ} : p.rayParity u z = false := by
  classical
  by_cases hu : u = 0
  · simp only [Route.rayParity, Cslib.Polygonal.rayParity, hu, zero_mul,
      not_rayCrosses_of_im_eq rfl, ite_false, Finset.sum_const_zero, ← Bool.zero_eq_false]
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  let K' := f '' K
  let z' := u * z
  have hK' : Convex ℝ K' := hK.linear_image f
  have hz' : z' ∉ K' := fun ⟨w, hw, heq⟩ => hz (mul_left_cancel₀ hu heq ▸ hw)
  let right := decide (∃ y ∈ K', y.im = z'.im ∧ z'.re < y.re)
  let observe (w : ℂ) := right * decide ((u * w).im ≤ z'.im)
  have hsegment (i : Fin p.segments) :
      segment ℝ (u * p.point i.castSucc) (u * p.point i.succ) ⊆ K' := by
    change segment ℝ (f.toAffineMap (p.point i.castSucc)) (f.toAffineMap (p.point i.succ)) ⊆
      f.toAffineMap '' K
    rw [← image_segment ℝ f.toAffineMap]
    exact Set.image_mono fun w hw => hp (Set.mem_iUnion.mpr ⟨i, hw⟩)
  have hpiece (i : Fin p.segments) :
      (if RayCrosses (u * p.point i.castSucc) (u * p.point i.succ) z' then (true : Bool) else 0) =
        observe (p.point i.castSucc) + observe (p.point i.succ) := by
    let a := u * p.point i.castSucc
    let b := u * p.point i.succ
    change (if RayCrosses a b z' then (true : Bool) else 0) =
      right * decide (a.im ≤ z'.im) + right * decide (b.im ≤ z'.im)
    rw [← mul_add, ← decide_height_between]
    by_cases hh : z'.im ∈ Set.Ico (min a.im b.im) (max a.im b.im)
    · have hc : RayCrosses a b z' ↔ ∃ y ∈ K', y.im = z'.im ∧ z'.re < y.re :=
        (and_iff_right hh.1).trans ((and_iff_right hh.2).trans
          (right_slice_iff hK' hz' (hsegment i (horizontalIntercept_mem_segment hh)) rfl))
      simp only [right, Bool.decide_congr hc.symm]
      by_cases h : RayCrosses a b z' <;> simp [h, hh, Bool.mul_eq_and, Bool.zero_eq_false]
    · have hnot : ¬RayCrosses a b z' := fun h => hh ⟨h.1, h.2.1⟩
      simp [hh, hnot, ← Bool.zero_eq_false]
  unfold Route.rayParity Cslib.Polygonal.rayParity
  calc
    _ = ∑ i : Fin p.segments, (observe (p.point i.castSucc) + observe (p.point i.succ)) :=
      Finset.sum_congr rfl fun i _ => hpiece i
    _ = _ := by rw [sum_segment_endpoints, hclosed, BooleanRing.add_self]; rfl

/-- Either of two routes inside a convex neighborhood may replace the other at their
common endpoints without changing the ray parity at an observation outside the neighborhood. -/
theorem rayParity_eq_of_support_subset_convex (p q : Route) {K : Set ℂ}
    (hs : p.start = q.start) (hf : p.finish = q.finish)
    (hK : Convex ℝ K) (hp : p.support ⊆ K) (hq : q.support ⊆ K)
    {z : ℂ} (hz : z ∉ K) {u : ℂ} : p.rayParity u z = q.rayParity u z := by
  have hjoin : p.finish = q.reverse.start := hf
  have hclose : (p.concat q.reverse).finish = (p.concat q.reverse).start := by
    rw [finish_concat hjoin, start_concat hjoin]
    exact (q.endpoint_reverse true).trans hs.symm
  have hsupport : (p.concat q.reverse).support ⊆ K := by
    rw [support_concat _ _ hjoin, support_reverse]
    exact Set.union_subset hp hq
  have h := (p.concat q.reverse).rayParity_eq_false_of_support_subset_convex
    (u := u) hclose hK hsupport hz
  rw [rayParity_concat _ _ hjoin, rayParity_reverse, ← Bool.zero_eq_false] at h
  exact (BooleanRing.add_eq_zero' _ _).mp h

private theorem rayParity_sum_lines (p : Route) (u z : ℂ) :
    p.rayParity u z =
      ∑ i : Fin p.segments, (line (p.point i.castSucc) (p.point i.succ)).rayParity u z := by
  simp only [rayParity_line]
  simp [Route.rayParity, Cslib.Polygonal.rayParity, Bool.zero_eq_false]

open Pointwise in
private theorem exists_pos_rayParity_eq_of_fixed_incident_segments (p : Route) (z : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) →
      (∀ i : Fin p.segments, z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ) →
        q i.castSucc = p.point i.castSucc ∧ q i.succ = p.point i.succ) →
      (∀ i : Fin p.segments,
        z ∈ segment ℝ (q i.castSucc) (q i.succ) ↔
          z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ)) ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  classical
  let avoids (i : Fin p.segments) := z ∉ segment ℝ (p.point i.castSucc) (p.point i.succ)
  let S := ⋃ i : {i // avoids i}, segment ℝ (p.point i.val.castSucc) (p.point i.val.succ)
  have hcompact : IsCompact S := isCompact_iUnion fun i =>
    segment_eq_image_lineMap ℝ (p.point i.val.castSucc) (p.point i.val.succ) ▸
      isCompact_Icc.image AffineMap.lineMap_continuous
  have hz : z ∉ S := fun h => (Set.mem_iUnion.mp h).elim fun i hi => i.property hi
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl z hz
  refine ⟨ε, hε, fun q hs hf hdist hfixed => ?_⟩
  let r : Route := ⟨p.bends, q⟩
  let link (u : ℂ) (i : Fin (p.segments + 1)) := (line (p.point i) (q i)).rayParity u z
  have hpieces (i : Fin p.segments) :
      (z ∈ segment ℝ (q i.castSucc) (q i.succ) ↔
        z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ)) ∧
      ∀ u : ℂ, (line (p.point i.castSucc) (p.point i.succ)).rayParity u z =
        (line (q i.castSucc) (q i.succ)).rayParity u z + (link u i.castSucc + link u i.succ) := by
    by_cases hi : z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ)
    · obtain ⟨hc, hd⟩ := hfixed i hi
      refine ⟨by rw [hc, hd], fun u => ?_⟩
      simp only [link, hc, hd, rayParity_line, not_rayCrosses_of_im_eq rfl, decide_false,
        ← Bool.zero_eq_false, add_zero]
    let a := p.point i.castSucc
    let b := p.point i.succ
    let c := q i.castSucc
    let d := q i.succ
    let K := segment ℝ a b + Metric.ball (0 : ℂ) ε
    have hK : Convex ℝ K := (convex_segment _ _).add (convex_ball _ _)
    have hzK : z ∉ K := fun ⟨x, hx, w, hw, heq⟩ =>
      hball (by simpa [← heq, dist_eq_norm] using hw) (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)
    have old {x : ℂ} (hx : x ∈ segment ℝ a b) : x ∈ K :=
      ⟨x, hx, 0, Metric.mem_ball_self hε, add_zero x⟩
    have moved {x y : ℂ} (hx : x ∈ segment ℝ a b) (hy : dist y x < ε) : y ∈ K :=
      ⟨x, hx, y - x, by simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy,
        add_sub_cancel x y⟩
    have ha := old (left_mem_segment ℝ a b)
    have hb := old (right_mem_segment ℝ a b)
    have hc := moved (left_mem_segment ℝ a b) (hdist i.castSucc)
    have hd := moved (right_mem_segment ℝ a b) (hdist i.succ)
    have hline {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) : (line x y).support ⊆ K :=
      support_line x y ▸ hK.segment_subset hx hy
    let s := (line a c).concat (line c d)
    have hjoin : s.finish = (line d b).start := finish_concat rfl
    have hs : (line a b).start = (s.concat (line d b)).start :=
      ((start_concat hjoin).trans (start_concat rfl)).symm
    have hsupport : (s.concat (line d b)).support ⊆ K := by
      rw [support_concat _ _ hjoin, support_concat (line a c) (line c d) rfl]
      exact Set.union_subset (Set.union_subset (hline ha hc) (hline hc hd)) (hline hd hb)
    refine ⟨iff_of_false (fun hz => hzK (hK.segment_subset hc hd hz)) hi, fun u => ?_⟩
    have h := rayParity_eq_of_support_subset_convex (line a b) (s.concat (line d b))
      (u := u) hs (finish_concat hjoin).symm hK (hline ha hb) hsupport hzK
    rw [rayParity_concat _ _ hjoin, rayParity_concat (line a c) (line c d) rfl,
      ← reverse_line b d, rayParity_reverse] at h
    dsimp only [link, a, b, c, d] at h ⊢
    exact h.trans (by ac_rfl)
  refine ⟨fun i => (hpieces i).1, fun u => ?_⟩
  have hlinks : (∑ i : Fin p.segments, (link u i.castSucc + link u i.succ)) = 0 := by
    rw [sum_adjacent_bool]
    change (line p.start (q 0)).rayParity u z +
      (line p.finish (q (Fin.last p.segments))).rayParity u z = 0
    simp [hs, hf, rayParity_line, not_rayCrosses_of_im_eq rfl, ← Bool.zero_eq_false]
  symm
  calc
    _ = ∑ i : Fin p.segments, (line (p.point i.castSucc) (p.point i.succ)).rayParity u z :=
      rayParity_sum_lines p u z
    _ = ∑ i : Fin p.segments,
        ((line (q i.castSucc) (q i.succ)).rayParity u z + (link u i.castSucc + link u i.succ)) :=
      Finset.sum_congr rfl fun i _ => (hpieces i).2 u
    _ = _ := by
      rw [Finset.sum_add_distrib, hlinks, add_zero]
      exact (rayParity_sum_lines r u z).symm

/-- If the route endpoints and all segments incident to an observation stay fixed, a single
positive radius preserves each segment's incidence with that observation and the route's ray
parity in every direction. A single radius works for all observations in the given finite set. -/
theorem exists_pos_rayParity_eq_of_fixed_observation_segments (p : Route) (points : Finset ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) →
      (∀ i : Fin p.segments, (∃ z ∈ points, z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ)) →
        q i.castSucc = p.point i.castSucc ∧ q i.succ = p.point i.succ) →
      ∀ z ∈ points,
        (∀ i : Fin p.segments,
          z ∈ segment ℝ (q i.castSucc) (q i.succ) ↔
            z ∈ segment ℝ (p.point i.castSucc) (p.point i.succ)) ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  classical
  induction points using Finset.induction_on with
  | empty =>
    exact ⟨1, one_pos, fun _ _ _ _ _ _ hz => (Finset.notMem_empty _ hz).elim⟩
  | @insert z points hz ih =>
    obtain ⟨r, hr, hlocal⟩ := exists_pos_rayParity_eq_of_fixed_incident_segments p z
    obtain ⟨s, hs, hrest⟩ := ih
    refine ⟨min r s, lt_min hr hs, fun q hfirst hlast hdist hfixed w hw => ?_⟩
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hlocal q hfirst hlast (fun i => (hdist i).trans_le (min_le_left _ _))
        (fun i hi => hfixed i ⟨w, Finset.mem_insert_self _ _, hi⟩)
    · exact hrest q hfirst hlast (fun i => (hdist i).trans_le (min_le_right _ _))
        (fun i ⟨v, hv, hi⟩ => hfixed i ⟨v, Finset.mem_insert_of_mem hv, hi⟩) w hw

/-- An observation off a route's support admits one radius for simultaneous small changes
to all its listed points. If the endpoints stay fixed, the new support avoids the observation
and preserves ray parity there in every direction, even at an old bend height. -/
theorem exists_pos_rayParity_eq_of_point_dist_lt (p : Route) {z : ℂ} (hz : z ∉ p.support) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) →
      z ∉ (⟨p.bends, q⟩ : Route).support ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  obtain ⟨ε, hε, h⟩ := exists_pos_rayParity_eq_of_fixed_incident_segments p z
  refine ⟨ε, hε, fun q hs hf hdist => ?_⟩
  obtain ⟨hseg, hpar⟩ := h q hs hf hdist
    (fun i hi => (hz (Set.mem_iUnion.mpr ⟨i, hi⟩)).elim)
  exact ⟨by simpa only [Route.support, Set.mem_iUnion, hseg] using hz, hpar⟩

/-- One positive perturbation radius works simultaneously at all finitely many
observations disjoint from the original route and for every ray direction. -/
theorem exists_pos_rayParity_eq_of_point_dist_lt_finset (p : Route) (points : Finset ℂ)
    (havoid : ∀ z ∈ points, z ∉ p.support) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) → ∀ z ∈ points,
        z ∉ (⟨p.bends, q⟩ : Route).support ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  obtain ⟨ε, hε, h⟩ := p.exists_pos_rayParity_eq_of_fixed_observation_segments points
  refine ⟨ε, hε, fun q hs hf hdist z hz => ?_⟩
  obtain ⟨hseg, hpar⟩ := h q hs hf hdist
    (fun i ⟨w, hw, hi⟩ => (havoid w hw (Set.mem_iUnion.mpr ⟨i, hi⟩)).elim) z hz
  exact ⟨by simpa only [Route.support, Set.mem_iUnion, hseg] using havoid z hz, hpar⟩

private noncomputable def parityTriangle (c : ℂ) (r : ℝ) : Route where
  bends := 2
  point i :=
    if i.val = 1 then ⟨c.re + r, c.im⟩
    else if i.val = 2 then ⟨c.re - r, c.im + r⟩
    else ⟨c.re - r, c.im - r⟩

private theorem parityTriangle_point (c : ℂ) (r : ℝ) (i : Fin 4) :
    (parityTriangle c r).point i =
      if i.val = 1 then ⟨c.re + r, c.im⟩
      else if i.val = 2 then ⟨c.re - r, c.im + r⟩
      else ⟨c.re - r, c.im - r⟩ := rfl

open Classical in
private theorem parityTriangle_bits (c z : ℂ) {r : ℝ} (hr : 0 < r) :
    (parityTriangle c r).rayParity 1 z =
      (if c.im - r ≤ z.im ∧ z.im < c.im ∧
        z.re < c.re + r + 2 * (z.im - c.im) then true else 0) +
      (if c.im ≤ z.im ∧ z.im < c.im + r ∧
        z.re < c.re + r - 2 * (z.im - c.im) then true else 0) +
      (if c.im - r ≤ z.im ∧ z.im < c.im + r ∧ z.re < c.re - r then true else 0) := by
  let a : ℂ := ⟨c.re - r, c.im - r⟩
  let b : ℂ := ⟨c.re + r, c.im⟩
  let d : ℂ := ⟨c.re - r, c.im + r⟩
  have hab : horizontalIntercept a b z.im = c.re + r + 2 * (z.im - c.im) := by
    simp only [horizontalIntercept, a, b, sub_sub_cancel]
    field_simp [hr.ne']; ring
  have hbd : horizontalIntercept b d z.im = c.re + r - 2 * (z.im - c.im) := by
    simp only [horizontalIntercept, b, d, add_sub_cancel_left]
    field_simp [hr.ne']; ring
  have hda : horizontalIntercept d a z.im = c.re - r := by simp [horizontalIntercept, d, a]
  have ha : a.im ≤ b.im := by dsimp only [a, b]; linarith
  have hb : b.im ≤ d.im := by dsimp only [b, d]; linarith
  change (∑ i : Fin 3, if RayCrosses (1 * (parityTriangle c r).point i.castSucc)
    (1 * (parityTriangle c r).point i.succ) (1 * z) then (true : Bool) else 0) = _
  simp only [Fin.sum_univ_three, one_mul]
  change (if RayCrosses a b z then true else 0) + (if RayCrosses b d z then true else 0) +
    (if RayCrosses d a z then true else 0) = _
  simp only [RayCrosses, min_eq_left ha, max_eq_right ha, min_eq_left hb, max_eq_right hb,
    min_eq_right (ha.trans hb), max_eq_left (ha.trans hb), hab, hbd, hda]
  rfl

private theorem parityTriangle_center (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (parityTriangle c r).rayParity 1 c = true := by
  rw [parityTriangle_bits c c hr]
  simp only [Bool.zero_eq_false, Bool.add_eq_xor]
  split_ifs <;> first | decide | grind

private theorem parityTriangle_outside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hout : r < max |z.re - c.re| |z.im - c.im|) :
    (parityTriangle c r).rayParity 1 z = false := by
  rw [parityTriangle_bits c z hr]
  rcases lt_max_iff.mp hout with h | h <;> rcases lt_abs.mp h with h | h <;>
    split_ifs <;> first | rfl | grind

private theorem parityTriangle_support (c : ℂ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ (parityTriangle c r).support) :
    z ≠ c ∧ max |z.re - c.re| |z.im - c.im| ≤ r := by
  obtain ⟨i, t, ht, rfl⟩ := ((parityTriangle c r).mem_support_iff z).mp hz
  have h₀ : 0 ≤ t * r := mul_nonneg ht.1 hr.le
  have h₁ : t * r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hr.le
  have hre := congrArg Complex.re
    (AffineMap.lineMap_apply_module' ((parityTriangle c r).point i.castSucc)
      ((parityTriangle c r).point i.succ) t)
  have him := lineMap_im ((parityTriangle c r).point i.castSucc)
    ((parityTriangle c r).point i.succ) t
  change Fin 3 at i
  fin_cases i <;>
    norm_num [parityTriangle_point, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im] at hre him
  all_goals
    refine ⟨?_, max_le (abs_le.mpr ⟨?_, ?_⟩) (abs_le.mpr ⟨?_, ?_⟩)⟩
    · intro heq
      rw [Complex.ext_iff] at heq
      norm_num [Route.eval, parityTriangle_point] at heq
      nlinarith
    all_goals
      norm_num [Route.eval, parityTriangle_point]
      nlinarith

/-- An arbitrarily small three-segment closed route can toggle horizontal ray parity
at exactly one point of a finite set. Its support avoids the center and every observation
point, and all three segments are nonhorizontal. -/
theorem exists_rayParity_isolating_loop (points : Finset ℂ) (c : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Route, p.segments = 3 ∧ p.finish = p.start ∧
      (∀ i : Fin p.segments, (p.point i.castSucc).im ≠ (p.point i.succ).im) ∧
      c ∉ p.support ∧ (∀ z ∈ points, z ∉ p.support) ∧
      (∀ z ∈ p.support, max |z.re - c.re| |z.im - c.im| < ε) ∧
      p.rayParity 1 c = true ∧ ∀ z ∈ points, z ≠ c → p.rayParity 1 z = false := by
  classical
  have chooseRadius (s : Finset ℂ) : ∃ r : ℝ, 0 < r ∧ r < ε ∧
      ∀ z ∈ s, z ≠ c → r < max |z.re - c.re| |z.im - c.im| := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨ε / 2, by linarith, by linarith, by simp⟩
    | @insert z s _ ih =>
      obtain ⟨r, hr, hrε, hs⟩ := ih
      by_cases hzc : z = c
      · exact ⟨r, hr, hrε, Finset.forall_mem_insert _ _ _ |>.mpr ⟨fun h => (h hzc).elim, hs⟩⟩
      let d := max |z.re - c.re| |z.im - c.im|
      have hd : 0 < d := by
        by_contra! h
        simp only [d, max_le_iff, abs_nonpos_iff, sub_eq_zero] at h
        exact hzc (Complex.ext h.1 h.2)
      refine ⟨min r (d / 2), lt_min hr (by linarith), (min_le_left _ _).trans_lt hrε, ?_⟩
      intro w hw hwc
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (min_le_right _ _).trans_lt (half_lt_self hd)
      · exact (min_le_left _ _).trans_lt (hs w hw hwc)
  obtain ⟨r, hr, hrε, hpoints⟩ := chooseRadius points
  refine ⟨parityTriangle c r, rfl, rfl, ?_, ?_, ?_, ?_, parityTriangle_center c hr, ?_⟩
  · intro i
    change Fin 3 at i
    fin_cases i <;> intro heq <;> norm_num [parityTriangle_point] at heq <;> linarith
  · exact fun h => (parityTriangle_support c hr h).1 rfl
  · exact fun z hz hs =>
      (parityTriangle_support c hr hs).2.not_gt (hpoints z hz (parityTriangle_support c hr hs).1)
  · exact fun z hz => (parityTriangle_support c hr hz).2.trans_lt hrε
  · exact fun z hz hne => parityTriangle_outside hr (hpoints z hz hne)

/-- In an open path-connected region, start at an unmarked point and make a closed
polygonal excursion around one chosen point of the region. The route stays in the region,
avoids the finite observation set and the chosen point, and has odd ray parity exactly at
the chosen point among these observations. Connector segments may be retraced. -/
theorem exists_rayParity_isolating_excursion {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPathConnected U) (points : Finset ℂ) {a c : ℂ} (ha : a ∈ U)
    (hc : c ∈ U) (haPoints : a ∉ points) (hac : a ≠ c) :
    ∃ p : Route, p.start = a ∧ p.finish = a ∧
      p.support ⊆ U \ (↑(insert c points) : Set ℂ) ∧
      p.rayParity 1 c = true ∧ ∀ z ∈ points, z ≠ c → p.rayParity 1 z = false := by
  classical
  let V := U \ (↑(insert c points) : Set ℂ)
  have hfinite : ((↑(insert c points) : Set ℂ)).Finite := Finset.finite_toSet _
  have hV : IsOpen V := hU.sdiff hfinite.isClosed
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  have hVconn : IsPathConnected V :=
    isPathConnected_sdiff_finite_of_isOpen hrank hU hconn hfinite
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨q, -, hclosed, -, hcenter, hpoints, hbound, hodd, heven⟩ :=
    exists_rayParity_isolating_loop points c (half_pos hε)
  have hq : q.support ⊆ V := by
    intro z hz
    obtain ⟨hx, hy⟩ := max_lt_iff.mp (hbound z hz)
    have hnorm : dist z c ≤ |z.re - c.re| + |z.im - c.im| := by
      simpa only [dist_eq_norm, Complex.sub_re, Complex.sub_im] using
        Complex.norm_le_abs_re_add_abs_im (z - c)
    refine ⟨hball (Metric.mem_ball.mpr (by linarith)), fun hz' => ?_⟩
    rcases Finset.mem_insert.mp hz' with rfl | hz'
    · exact hcenter hz
    · exact hpoints z hz' hz
  have hqstart : q.start ∈ q.support := q.point_mem_support 0
  have haV : a ∈ V :=
    ⟨ha, by simpa only [Finset.mem_coe, Finset.mem_insert, not_or] using ⟨hac, haPoints⟩⟩
  obtain ⟨p, hstart, hjoin, hp⟩ :=
    exists_support_subset_of_joinedIn hV (hVconn.joinedIn _ haV _ (hq hqstart))
  have hreturn := closed_excursion_return_join p q hjoin hclosed
  refine ⟨(p.concat q).concat p.reverse, (start_concat hreturn).trans
    ((start_concat hjoin).trans hstart), (finish_concat hreturn).trans
    ((p.endpoint_reverse true).trans hstart), ?_, ?_, ?_⟩
  · rw [support_concat _ _ hreturn, support_concat _ _ hjoin, support_reverse]
    exact Set.union_subset (Set.union_subset hp hq) hp
  · exact (rayParity_closed_excursion p q hjoin hclosed _ _).trans hodd
  · exact fun z hz hne => (rayParity_closed_excursion p q hjoin hclosed _ _).trans (heven z hz hne)

/-- Realize a prescribed subset of odd ray-parity observations by one closed polygonal
route based at an unmarked point. The whole route remains in the open region and avoids
every observation. The route may retrace segments. -/
theorem exists_rayParity_excursion_of_subset {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPathConnected U) (points odd : Finset ℂ) (hodd : odd ⊆ points)
    (hUodd : ∀ c ∈ odd, c ∈ U) {a : ℂ} (ha : a ∈ U) (haPoints : a ∉ points) :
    ∃ p : Route, p.start = a ∧ p.finish = a ∧ p.support ⊆ U \ (↑points : Set ℂ) ∧
      ∀ z ∈ points, p.rayParity 1 z = decide (z ∈ odd) := by
  classical
  induction odd using Finset.induction_on with
  | empty =>
      refine ⟨line a a, start_line _ _, finish_line _ _, ?_, ?_⟩
      · simp [support_line, ha, haPoints]
      · exact fun z _ => by simp [rayParity_line, not_rayCrosses_of_im_eq rfl]
  | @insert c odd hc ih =>
      have hcPoints : c ∈ points := hodd (Finset.mem_insert_self _ _)
      have hcU : c ∈ U := hUodd c (Finset.mem_insert_self _ _)
      have hsub : odd ⊆ points := fun _ hz => hodd (Finset.mem_insert_of_mem hz)
      obtain ⟨p, hps, hpf, hp, hparity⟩ :=
        ih hsub (fun z hz => hUodd z (Finset.mem_insert_of_mem hz))
      obtain ⟨q, hqs, hqf, hq, hqc, hqRest⟩ :=
        exists_rayParity_isolating_excursion hU hconn points ha hcU haPoints
          (fun heq => haPoints (heq.symm ▸ hcPoints))
      have hjoin : p.finish = q.start := hpf.trans hqs.symm
      rw [Finset.insert_eq_of_mem hcPoints] at hq
      refine ⟨p.concat q, (start_concat hjoin).trans hps, (finish_concat hjoin).trans hqf, ?_, ?_⟩
      · rw [support_concat p q hjoin]
        exact Set.union_subset hp hq
      · intro z hz
        rw [rayParity_concat p q hjoin, hparity z hz]
        by_cases heq : z = c
        · subst z
          simp [hc, hqc, Bool.add_eq_xor]
        · simp [Finset.mem_insert, heq, hqRest z hz heq, Bool.add_eq_xor]

/-- Insert a closed excursion at a join to add the prescribed ray-parity bits in a
nonzero complex coordinate factor. The new support stays in the union of the original
support and the punctured region. Both outer endpoints and germs are preserved, and
the route retains at least as many segments as the two routes at the join. -/
theorem exists_concat_add_rayParity {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPathConnected U) (points odd : Finset ℂ) (hodd : odd ⊆ points)
    (hUodd : ∀ z ∈ odd, z ∈ U) (p q : Route) (hjoin : p.finish = q.start)
    (ha : p.finish ∈ U) (haPoints : p.finish ∉ points) {u : ℂ} (hu : u ≠ 0) :
    ∃ r : Route, (∀ b, r.endpoint b = (p.concat q).endpoint b) ∧
      (∀ b, r.germ b = (p.concat q).germ b) ∧
      (p.concat q).support ⊆ r.support ∧
      r.support ⊆ (p.concat q).support ∪ (U \ (↑points : Set ℂ)) ∧
      (∀ z ∈ points, r.rayParity u z = (p.concat q).rayParity u z + decide (z ∈ odd)) ∧
      p.segments + q.segments ≤ r.segments := by
  classical
  let f := Homeomorph.mulLeft₀ u hu
  have hf (z : ℂ) : f z = u * z := rfl
  let embedding := f.toEquiv.toEmbedding
  let points' := points.map embedding
  let odd' := odd.map embedding
  have hsub : odd' ⊆ points' := Finset.map_subset_map.mpr hodd
  have huodd : ∀ z ∈ odd', z ∈ f '' U :=
    Finset.forall_mem_map.mpr fun w hw => ⟨w, hUodd w hw, rfl⟩
  obtain ⟨l, hls, hlf, hl, hpar⟩ :=
    exists_rayParity_excursion_of_subset (f.isOpenMap _ hU)
      (hconn.image f.continuous) points' odd' hsub huodd
      (Set.mem_image_of_mem f ha) (fun h => haPoints ((Finset.mem_map' embedding).mp h))
  let e := mulComplex u⁻¹ l
  have hend (b : Bool) (hb : l.endpoint b = f p.finish) : e.endpoint b = p.finish := by
    rw [endpoint_mulComplex, hb, hf, inv_mul_cancel_left₀ hu]
  have hstart : e.start = p.finish := hend false hls
  have hfinish : e.finish = p.finish := hend true hlf
  have hsupport : e.support ⊆ U \ (↑points : Set ℂ) := by
    rw [support_mulComplex]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨⟨v, hv, rfl⟩, hn⟩ := hl hw
    simp only [hf, inv_mul_cancel_left₀ hu]
    exact ⟨hv, fun h => hn (Finset.mem_map_of_mem embedding h)⟩
  have hparity (z : ℂ) (hz : z ∈ points) : e.rayParity u z = decide (z ∈ odd) := by
    have h : e.rayParity u z = l.rayParity 1 (f z) := by
      simp only [Route.rayParity, Cslib.Polygonal.rayParity, e, mulComplex,
        mul_inv_cancel_left₀ hu, one_mul, hf]
      rfl
    rw [h, hpar (f z) (Finset.mem_map_of_mem embedding hz)]
    exact Bool.decide_congr (Finset.mem_map' embedding)
  have he : p.finish = e.start := hstart.symm
  have hq : (p.concat e).finish = q.start := (finish_concat he).trans (hfinish.trans hjoin)
  refine ⟨(p.concat e).concat q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | _) <;> simp [endpoint_concat _ _ hq, endpoint_concat p q hjoin,
      endpoint_concat p e he]
  · rintro (_ | _) <;> simp [germ_concat _ _ hq, germ_concat p q hjoin, germ_concat p e he]
  · rw [support_concat _ _ hq, support_concat p e he, support_concat p q hjoin]
    exact fun _ => Or.imp Or.inl id
  · rw [support_concat _ _ hq, support_concat p e he, support_concat p q hjoin]
    rintro z ((hp | hl) | hq')
    exacts [Or.inl (Or.inl hp), Or.inr (hsupport hl), Or.inl (Or.inr hq')]
  · intro z hz
    rw [rayParity_concat _ _ hq, rayParity_concat p e he, rayParity_concat p q hjoin,
      hparity z hz]
    ac_rfl
  · rw [segments_concat, segments_concat]; omega

/-- Insert a prescribed parity excursion at an interior point of a straight route.
The excursion avoids the marked points, and each outer germ remains a positive
multiple of its original value. -/
theorem exists_line_add_rayParity {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPathConnected U) (points odd : Finset ℂ) (hodd : odd ⊆ points)
    (hUodd : ∀ z ∈ odd, z ∈ U) (a b : ℂ) {t : ℝ} (ht : t ∈ Set.Ioo 0 1)
    (hm : AffineMap.lineMap a b t ∈ U \ (↑points : Set ℂ)) {u : ℂ} (hu : u ≠ 0) :
    ∃ r : Route, (∀ s, r.endpoint s = (line a b).endpoint s) ∧
      (∀ s, r.germ s = (if s then 1 - t else t) • (line a b).germ s) ∧
      segment ℝ a b ⊆ r.support ∧
      r.support ⊆ segment ℝ a b ∪ (U \ (↑points : Set ℂ)) ∧
      ∀ z ∈ points, r.rayParity u z = (line a b).rayParity u z + decide (z ∈ odd) := by
  let m := AffineMap.lineMap a b t
  let p := line a m
  let q := line m b
  obtain ⟨r, he, hg, hcontains, hsupport, hpar, -⟩ :=
    exists_concat_add_rayParity hU hconn points odd hodd hUodd p q rfl hm.1 hm.2 hu
  have hsegments : (p.concat q).support = segment ℝ a b := by
    let L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
    have hleft : L '' Set.Icc 0 t = segment ℝ a m := by
      rw [← segment_eq_Icc ht.1.le, image_segment ℝ L]
      simp only [L, m, AffineMap.lineMap_apply_zero]
    have hright : L '' Set.Icc t 1 = segment ℝ m b := by
      rw [← segment_eq_Icc ht.2.le, image_segment ℝ L]
      simp only [L, m, AffineMap.lineMap_apply_one]
    rw [support_concat _ _ rfl]
    change (line a m).support ∪ (line m b).support = segment ℝ a b
    rw [support_line, support_line, ← hleft, ← hright, ← Set.image_union,
      Set.Icc_union_Icc_eq_Icc ht.1.le ht.2.le]
    exact (segment_eq_image_lineMap ℝ a b).symm
  refine ⟨r, fun s => ?_, fun s => ?_, hsegments ▸ hcontains, hsegments ▸ hsupport,
    fun z hz => by rw [hpar z hz, rayParity_line_split a b u z ht]⟩
  · rw [he, endpoint_concat p q rfl]
    cases s <;> rfl
  · rw [hg, germ_concat p q rfl]
    cases s <;>
      first | exact AffineMap.lineMap_vsub_left a b t | exact AffineMap.lineMap_vsub_right a b t

end Cslib.Polygonal.Route
