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
  classical
  have hlast := Fin.sum_univ_castSucc f
  have hfirst := Fin.sum_univ_succ f
  rw [Finset.sum_add_distrib,
    eq_sub_iff_add_eq.mpr hlast.symm,
    eq_sub_iff_add_eq'.mpr hfirst.symm]
  simp only [sub_eq_add_neg, BooleanRing.neg_eq]
  calc
    _ = ((∑ i, f i) + ∑ i, f i) +
        (f 0 + f (Fin.last n)) := by ac_rfl
    _ = _ := by rw [BooleanRing.add_self, zero_add]

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
    have hsupport : segment ℝ (p.point j.castSucc) (p.point j.succ) ⊆ p.support := by
      rw [segment_eq_image_lineMap]
      rintro z ⟨t, ht, rfl⟩
      exact p.at_mem_support j ht
    apply rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
      a b x _ _ hheight (hpheight j) (hnodes j.castSucc) (hnodes j.succ)
    · exact fun i hx hz => (hends i hx).1 (hsupport hz)
    · exact fun i hx hz => (hends i hx).2 (hsupport hz)
    · intro z _
      exact sum_rayParity_endpoint_jumps_eq_zero a b x heven z
  calc
    _ = ∑ j : Fin p.segments,
        (rayParity a b x (p.point j.castSucc) + rayParity a b x (p.point j.succ)) := by
      rw [sum_segment_endpoints]
      exact add_comm _ _
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
  classical
  unfold Route.rayParity Cslib.Polygonal.rayParity
  change (∑ i : Fin 1, if RayCrosses (u * (line a b).point i.castSucc)
    (u * (line a b).point i.succ) (u * z) then (true : Bool) else 0) = _
  rw [Fin.sum_univ_one]
  change (if RayCrosses (u * a) (u * b) (u * z) then true else false) = _
  by_cases h : RayCrosses (u * a) (u * b) (u * z) <;> simp [h]

/-- Cutting a straight route into two at an interior point preserves the ray parity of
the concatenation, including at observations on the cut height. -/
theorem rayParity_line_split (a b u z : ℂ) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    let m := AffineMap.lineMap a b t
    ((line a m).concat (line m b)).rayParity u z = (line a b).rayParity u z := by
  let m := AffineMap.lineMap a b t
  change ((line a m).concat (line m b)).rayParity u z = (line a b).rayParity u z
  have hm : u * m = AffineMap.lineMap (u * a) (u * b) t := by
    let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
    exact f.toAffineMap.apply_lineMap a b t
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
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.rev_castSucc, Fin.rev_succ,
        rayCrosses_reverse (u * p.point i.rev.castSucc) (u * p.point i.rev.succ) (u * z)]
    _ = _ := Equiv.sum_comp e (fun i =>
      if RayCrosses (u * p.point i.castSucc) (u * p.point i.succ) (u * z) then true else 0)

private theorem closed_excursion_return_join (p q : Route)
    (hjoin : p.finish = q.start) (hclosed : q.finish = q.start) :
    (p.concat q).finish = p.reverse.start := by
  change (p.concat q).endpoint true = p.reverse.endpoint false
  rw [endpoint_concat p q hjoin, endpoint_reverse]
  simpa only [endpoint, Bool.not_false, ↓reduceIte] using hclosed.trans hjoin.symm

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
  have hx : z.re ∈ segment ℝ w.re y.re := by
    rw [segment_eq_Icc (hzw.trans hyre.le)]
    exact ⟨hzw, hyre.le⟩
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, he⟩ := hx
  have heq : AffineMap.lineMap w y t = z := by
    apply Complex.ext
    · exact (Complex.reLm.toAffineMap.apply_lineMap w y t).trans he
    · rw [lineMap_im, hh, hyim, sub_self, mul_zero, add_zero]
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
  · subst u
    change p.rayParity 0 z = 0
    simp only [Route.rayParity, Cslib.Polygonal.rayParity, zero_mul,
      not_rayCrosses_of_im_eq rfl, ite_false, Finset.sum_const_zero]
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  let K' := f '' K
  let z' := u * z
  have hK' : Convex ℝ K' := hK.linear_image f
  have hz' : z' ∉ K' := by
    rintro ⟨w, hw, heq⟩
    exact hz ((mul_left_cancel₀ hu heq) ▸ hw)
  let right := decide (∃ y ∈ K', y.im = z'.im ∧ z'.re < y.re)
  let observe (w : ℂ) := right * decide ((u * w).im ≤ z'.im)
  have hsegment (i : Fin p.segments) :
      segment ℝ (u * p.point i.castSucc) (u * p.point i.succ) ⊆ K' := by
    change segment ℝ (f.toAffineMap (p.point i.castSucc)) (f.toAffineMap (p.point i.succ)) ⊆
      f.toAffineMap '' K
    rw [← image_segment ℝ f.toAffineMap]
    apply Set.image_mono
    intro w hw
    exact hp (Set.mem_iUnion.mpr ⟨i, hw⟩)
  have hpiece (i : Fin p.segments) :
      (if RayCrosses (u * p.point i.castSucc) (u * p.point i.succ) z' then (true : Bool) else 0) =
        observe (p.point i.castSucc) + observe (p.point i.succ) := by
    let a := u * p.point i.castSucc
    let b := u * p.point i.succ
    change (if RayCrosses a b z' then (true : Bool) else 0) =
      right * decide (a.im ≤ z'.im) + right * decide (b.im ≤ z'.im)
    rw [← mul_add, ← decide_height_between]
    by_cases hh : z'.im ∈ Set.Ico (min a.im b.im) (max a.im b.im)
    · have hw : (⟨horizontalIntercept a b z'.im, z'.im⟩ : ℂ) ∈ K' :=
        hsegment i (horizontalIntercept_mem_segment hh)
      have hc : RayCrosses a b z' ↔ ∃ y ∈ K', y.im = z'.im ∧ z'.re < y.re :=
        (and_iff_right hh.1).trans ((and_iff_right hh.2).trans (right_slice_iff hK' hz' hw rfl))
      by_cases h : RayCrosses a b z'
      · simp [h, hh, right, hc.mp h, Bool.mul_eq_and]
      · have hn : ¬∃ y ∈ K', y.im = z'.im ∧ z'.re < y.re := fun hy => h (hc.mpr hy)
        simp [h, hh, right, hn, Bool.mul_eq_and, Bool.zero_eq_false]
    · have h : ¬RayCrosses a b z' := fun h => hh ⟨h.1, h.2.1⟩
      simp [h, hh, ← Bool.zero_eq_false]
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
    change (p.concat q.reverse).endpoint true = (p.concat q.reverse).endpoint false
    rw [endpoint_concat _ _ hjoin, endpoint_concat _ _ hjoin, endpoint_reverse]
    exact hs.symm
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
  classical
  unfold Route.rayParity at *
  change (∑ i : Fin p.segments, if RayCrosses (u * p.point i.castSucc)
    (u * p.point i.succ) (u * z) then (true : Bool) else 0) = _
  apply Finset.sum_congr rfl
  intro i _
  change _ = (line (p.point i.castSucc) (p.point i.succ)).rayParity u z
  rw [rayParity_line]
  by_cases h : RayCrosses (u * p.point i.castSucc) (u * p.point i.succ) (u * z) <;>
    simp [h, Bool.zero_eq_false]

open Pointwise in
/-- An observation off a route's support admits one radius for simultaneous small changes
to all its listed points. If the endpoints stay fixed, the new support avoids the observation
and preserves ray parity there in every direction, even at an old bend height. -/
theorem exists_pos_rayParity_eq_of_point_dist_lt (p : Route) {z : ℂ} (hz : z ∉ p.support) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) →
      z ∉ (⟨p.bends, q⟩ : Route).support ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  classical
  have hcompact : IsCompact p.support := by
    unfold support
    apply isCompact_iUnion
    intro i
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl z hz
  refine ⟨ε, hε, fun q hs hf hdist => ?_⟩
  let r : Route := ⟨p.bends, q⟩
  let link (u : ℂ) (i : Fin (p.segments + 1)) := (line (p.point i) (q i)).rayParity u z
  have hpieces (i : Fin p.segments) :
      z ∉ segment ℝ (q i.castSucc) (q i.succ) ∧
      ∀ u : ℂ, (line (p.point i.castSucc) (p.point i.succ)).rayParity u z =
        (line (q i.castSucc) (q i.succ)).rayParity u z + (link u i.castSucc + link u i.succ) := by
    let a := p.point i.castSucc
    let b := p.point i.succ
    let c := q i.castSucc
    let d := q i.succ
    let K := segment ℝ a b + Metric.ball (0 : ℂ) ε
    have hK : Convex ℝ K := (convex_segment _ _).add (convex_ball _ _)
    have hzK : z ∉ K := by
      rintro ⟨x, hx, w, hw, heq⟩
      have hdist' : dist x z < ε := by
        rw [dist_comm, dist_eq_norm, ← heq, add_sub_cancel_left]
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      exact hball (show x ∈ Metric.ball z ε from hdist') (Set.mem_iUnion.mpr ⟨i, hx⟩)
    have old {x : ℂ} (hx : x ∈ segment ℝ a b) : x ∈ K :=
      ⟨x, hx, 0, Metric.mem_ball_self hε, add_zero x⟩
    have moved {x y : ℂ} (hx : x ∈ segment ℝ a b) (hy : dist y x < ε) : y ∈ K := by
      refine ⟨x, hx, y - x, ?_, ?_⟩
      · simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy
      · change x + (y - x) = y
        rw [add_comm, sub_add_cancel]
    have ha := old (left_mem_segment ℝ a b)
    have hb := old (right_mem_segment ℝ a b)
    have hc := moved (left_mem_segment ℝ a b) (hdist i.castSucc)
    have hd := moved (right_mem_segment ℝ a b) (hdist i.succ)
    have hline {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) : (line x y).support ⊆ K := by
      rw [support_line]
      exact hK.segment_subset hx hy
    let s := (line a c).concat (line c d)
    have hjoin : s.finish = (line d b).start := by
      change ((line a c).concat (line c d)).endpoint true = (line d b).endpoint false
      rw [endpoint_concat _ _ rfl]
      rfl
    have hend (side : Bool) : (line a b).endpoint side =
        (s.concat (line d b)).endpoint side := by
      rw [endpoint_concat _ _ hjoin]
      cases side
      · change (line a b).endpoint false = ((line a c).concat (line c d)).endpoint false
        rw [endpoint_concat _ _ rfl]
        rfl
      · rfl
    have hsupport : (s.concat (line d b)).support ⊆ K := by
      rw [support_concat _ _ hjoin]
      change ((line a c).concat (line c d)).support ∪ (line d b).support ⊆ K
      rw [support_concat _ _ rfl]
      exact Set.union_subset (Set.union_subset (hline ha hc) (hline hc hd)) (hline hd hb)
    refine ⟨fun hz => hzK (hK.segment_subset hc hd hz), fun u => ?_⟩
    have h := rayParity_eq_of_support_subset_convex (line a b) (s.concat (line d b))
      (u := u) (hend false) (hend true) hK (hline ha hb) hsupport hzK
    rw [rayParity_concat _ _ hjoin] at h
    change (line a b).rayParity u z =
      ((line a c).concat (line c d)).rayParity u z + (line d b).rayParity u z at h
    rw [rayParity_concat _ _ rfl, ← reverse_line b d, rayParity_reverse] at h
    refine h.trans ?_
    change _ = (line c d).rayParity u z + ((line a c).rayParity u z + (line b d).rayParity u z)
    ac_rfl
  change z ∉ r.support ∧ ∀ u : ℂ, r.rayParity u z = p.rayParity u z
  refine ⟨?_, fun u => ?_⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact (hpieces i).1 hi
  have hlinks : (∑ i : Fin p.segments, (link u i.castSucc + link u i.succ)) = 0 := by
    rw [sum_adjacent_bool]
    change (line p.start (q 0)).rayParity u z +
      (line p.finish (q (Fin.last p.segments))).rayParity u z = 0
    rw [hs, hf, rayParity_line, rayParity_line]
    simp only [not_rayCrosses_of_im_eq rfl, decide_false]
    rfl
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

/-- One positive perturbation radius works simultaneously at all finitely many
observations disjoint from the original route and for every ray direction. -/
theorem exists_pos_rayParity_eq_of_point_dist_lt_finset (p : Route) (points : Finset ℂ)
    (havoid : ∀ z ∈ points, z ∉ p.support) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin (p.segments + 1) → ℂ,
      q 0 = p.start → q (Fin.last p.segments) = p.finish →
      (∀ i, dist (q i) (p.point i) < ε) → ∀ z ∈ points,
        z ∉ (⟨p.bends, q⟩ : Route).support ∧
        ∀ u : ℂ, (⟨p.bends, q⟩ : Route).rayParity u z = p.rayParity u z := by
  classical
  induction points using Finset.induction_on with
  | empty =>
    exact ⟨1, one_pos, fun _ _ _ _ _ hz => (Finset.notMem_empty _ hz).elim⟩
  | @insert z points hz ih =>
    obtain ⟨r, hr, hlocal⟩ :=
      p.exists_pos_rayParity_eq_of_point_dist_lt (havoid z (Finset.mem_insert_self _ _))
    obtain ⟨s, hs, hrest⟩ := ih fun w hw => havoid w (Finset.mem_insert_of_mem hw)
    refine ⟨min r s, lt_min hr hs, fun q hfirst hlast hdist w hw => ?_⟩
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hlocal q hfirst hlast (fun i => (hdist i).trans_le (min_le_left _ _))
    · exact hrest q hfirst hlast (fun i => (hdist i).trans_le (min_le_right _ _)) w hw

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
    change c.re - r + (z.im - (c.im - r)) / (c.im - (c.im - r)) *
      (c.re + r - (c.re - r)) = _
    rw [show c.im - (c.im - r) = r by ring]
    field_simp [hr.ne']
    ring
  have hbd : horizontalIntercept b d z.im = c.re + r - 2 * (z.im - c.im) := by
    change c.re + r + (z.im - c.im) / (c.im + r - c.im) * (c.re - r - (c.re + r)) = _
    rw [show c.im + r - c.im = r by ring]
    field_simp [hr.ne']
    ring
  have hda : horizontalIntercept d a z.im = c.re - r := by
    change c.re - r + (z.im - (c.im + r)) / (c.im - r - (c.im + r)) *
      (c.re - r - (c.re - r)) = _
    rw [sub_self, mul_zero, add_zero]
  have ha : a.im ≤ b.im := by
    dsimp only [a, b]
    linarith
  have hb : b.im ≤ d.im := by
    dsimp only [b, d]
    linarith
  have hsum : (parityTriangle c r).rayParity 1 z =
      (if RayCrosses a b z then true else 0) +
      (if RayCrosses b d z then true else 0) +
      (if RayCrosses d a z then true else 0) := by
    unfold Route.rayParity Cslib.Polygonal.rayParity
    change (∑ i : Fin 3, if RayCrosses (1 * (parityTriangle c r).point i.castSucc)
      (1 * (parityTriangle c r).point i.succ) (1 * z) then (true : Bool) else 0) = _
    simp only [Fin.sum_univ_three, one_mul]
    rfl
  rw [hsum]
  simp only [RayCrosses, min_eq_left ha, max_eq_right ha, min_eq_left hb, max_eq_right hb,
    min_eq_right (ha.trans hb), max_eq_left (ha.trans hb), hab, hbd, hda]
  rfl

private theorem parityTriangle_center (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (parityTriangle c r).rayParity 1 c = true := by
  rw [parityTriangle_bits c c hr]
  have hlo : c.im - r ≤ c.im := by linarith
  have hhi : c.im < c.im + r := by linarith
  have hleft : ¬ c.re < c.re - r := by linarith
  have hright : c.re < c.re + r := by linarith
  simp [hlo, hhi, hleft, hright, Bool.add_eq_xor, Bool.zero_eq_false]

private theorem parityTriangle_outside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hout : r < max |z.re - c.re| |z.im - c.im|) :
    (parityTriangle c r).rayParity 1 z = false := by
  rw [parityTriangle_bits c z hr]
  by_cases hlo : c.im - r ≤ z.im
  · by_cases hhi : z.im < c.im + r
    · have hy : |z.im - c.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
      have hside : z.re < c.re - r ∨ c.re + r < z.re := by
        by_contra! h
        have hx : |z.re - c.re| ≤ r := abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
        exact (not_lt_of_ge (max_le hx hy)) hout
      by_cases hmid : z.im < c.im
      · have hmid' : ¬ c.im ≤ z.im := not_le.mpr hmid
        rcases hside with hx | hx
        · have h : z.re < c.re + r + 2 * (z.im - c.im) := by linarith
          simp [hlo, hhi, hmid, hmid', hx, h, Bool.add_eq_xor]
        · have h : ¬ z.re < c.re + r + 2 * (z.im - c.im) := by linarith
          have hleft : ¬ z.re < c.re - r := by linarith
          simp [hlo, hhi, hmid, hmid', hleft, h, Bool.zero_eq_false]
      · have hmid' : c.im ≤ z.im := le_of_not_gt hmid
        rcases hside with hx | hx
        · have h : z.re < c.re + r - 2 * (z.im - c.im) := by linarith
          simp [hlo, hhi, hmid, hmid', hx, h, Bool.add_eq_xor]
        · have h : ¬ z.re < c.re + r - 2 * (z.im - c.im) := by linarith
          have hleft : ¬ z.re < c.re - r := by linarith
          simp [hlo, hhi, hmid, hmid', hleft, h, Bool.zero_eq_false]
    · have hmid : ¬ z.im < c.im := by linarith [le_of_not_gt hhi]
      simp [hhi, hmid, Bool.zero_eq_false]
  · have hmid : ¬ c.im ≤ z.im := by linarith [lt_of_not_ge hlo]
    simp [hlo, hmid, Bool.zero_eq_false]

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
      have hx := congrArg Complex.re heq
      have hy := congrArg Complex.im heq
      norm_num [Route.eval, parityTriangle_point] at hx hy
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
      · refine ⟨r, hr, hrε, ?_⟩
        intro w hw hwc
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (hwc hzc).elim
        · exact hs w hw hwc
      let d := max |z.re - c.re| |z.im - c.im|
      have hd : 0 < d := by
        by_contra! h
        have hre := (le_max_left |z.re - c.re| |z.im - c.im|).trans h
        have him := (le_max_right |z.re - c.re| |z.im - c.im|).trans h
        exact hzc (Complex.ext
          (by have := abs_le.mp hre; linarith) (by have := abs_le.mp him; linarith))
      refine ⟨min r (d / 2), lt_min hr (by linarith), (min_le_left _ _).trans_lt hrε, ?_⟩
      intro w hw hwc
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (min_le_right _ _).trans_lt (by
          change d / 2 < d
          linarith)
      · exact (min_le_left _ _).trans_lt (hs w hw hwc)
  obtain ⟨r, hr, hrε, hpoints⟩ := chooseRadius points
  refine ⟨parityTriangle c r, rfl, rfl, ?_, ?_, ?_, ?_, parityTriangle_center c hr, ?_⟩
  · intro i
    change Fin 3 at i
    fin_cases i <;> intro heq <;> norm_num [parityTriangle_point] at heq <;> linarith
  · exact fun h => (parityTriangle_support c hr h).1 rfl
  · intro z hz hs
    obtain ⟨hne, hle⟩ := parityTriangle_support c hr hs
    exact (not_lt_of_ge hle) (hpoints z hz hne)
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
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (Nat.cast_lt.mpr (show (1 : ℕ) < 2 by decide) : (↑(1 : ℕ) : Cardinal) < ↑(2 : ℕ))
  have hVconn : IsPathConnected V :=
    isPathConnected_sdiff_finite_of_isOpen hrank hU hconn hfinite
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨q, -, hclosed, -, hcenter, hpoints, hbound, hodd, heven⟩ :=
    exists_rayParity_isolating_loop points c (half_pos hε)
  have hq : q.support ⊆ V := by
    intro z hz
    have hmax := hbound z hz
    have hx := (le_max_left _ _).trans_lt hmax
    have hy := (le_max_right _ _).trans_lt hmax
    have hd : dist z c < ε := by
      rw [dist_eq_norm]
      have hnorm := Complex.norm_le_abs_re_add_abs_im (z - c)
      rw [Complex.sub_re, Complex.sub_im] at hnorm
      linarith only [hx, hy, hnorm]
    refine ⟨hball (Metric.mem_ball.mpr hd), ?_⟩
    intro hz'
    rcases Finset.mem_insert.mp hz' with rfl | hz'
    · exact hcenter hz
    · exact hpoints z hz' hz
  have hqstart : q.start ∈ q.support := by
    have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have he := q.at_eq_start 0 hzero (by simp [position])
    exact he ▸ q.at_mem_support 0 hzero
  have haV : a ∈ V := by
    refine ⟨ha, ?_⟩
    simpa only [Finset.mem_coe, Finset.mem_insert, not_or] using (And.intro hac haPoints)
  obtain ⟨p, hstart, hjoin, hp⟩ :=
    exists_support_subset_of_joinedIn hV (hVconn.joinedIn _ haV _ (hq hqstart))
  have hreturn := closed_excursion_return_join p q hjoin hclosed
  have hfirst : ((p.concat q).concat p.reverse).start = a := by
    change ((p.concat q).concat p.reverse).endpoint false = a
    rw [endpoint_concat _ _ hreturn]
    change (p.concat q).endpoint false = a
    rw [endpoint_concat _ _ hjoin]
    exact hstart
  have hlast : ((p.concat q).concat p.reverse).finish = a := by
    change ((p.concat q).concat p.reverse).endpoint true = a
    rw [endpoint_concat _ _ hreturn]
    change p.reverse.endpoint true = a
    rw [endpoint_reverse]
    exact hstart
  refine ⟨(p.concat q).concat p.reverse, hfirst, hlast, ?_, ?_, ?_⟩
  · rw [support_concat _ _ hreturn, support_concat _ _ hjoin, support_reverse]
    exact Set.union_subset (Set.union_subset hp hq) hp
  · rw [rayParity_closed_excursion p q hjoin hclosed]
    exact hodd
  · intro z hz hne
    rw [rayParity_closed_excursion p q hjoin hclosed]
    exact heven z hz hne

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
      · rw [support_line, segment_same]
        intro z hz
        have heq := Set.mem_singleton_iff.mp hz
        subst z
        exact ⟨ha, haPoints⟩
      · intro z _
        unfold Route.rayParity Cslib.Polygonal.rayParity
        change (∑ i : Fin 1, if RayCrosses (1 * (line a a).point i.castSucc)
          (1 * (line a a).point i.succ) (1 * z) then (true : Bool) else 0) = _
        rw [Fin.sum_univ_one]
        change (if RayCrosses (1 * a) (1 * a) (1 * z) then (true : Bool) else 0) = _
        simp only [not_rayCrosses_of_im_eq rfl, ite_false, Finset.notMem_empty,
          decide_false, Bool.zero_eq_false]
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
      have hstart : (p.concat q).start = a := by
        change (p.concat q).endpoint false = a
        rw [endpoint_concat p q hjoin]
        exact hps
      have hfinish : (p.concat q).finish = a := by
        change (p.concat q).endpoint true = a
        rw [endpoint_concat p q hjoin]
        exact hqf
      rw [Finset.insert_eq_of_mem hcPoints] at hq
      refine ⟨p.concat q, hstart, hfinish, ?_, ?_⟩
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
support and the punctured region. Both outer endpoints and germs are preserved. -/
theorem exists_concat_add_rayParity {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPathConnected U) (points odd : Finset ℂ) (hodd : odd ⊆ points)
    (hUodd : ∀ z ∈ odd, z ∈ U) (p q : Route) (hjoin : p.finish = q.start)
    (ha : p.finish ∈ U) (haPoints : p.finish ∉ points) {u : ℂ} (hu : u ≠ 0) :
    ∃ r : Route, (∀ b, r.endpoint b = (p.concat q).endpoint b) ∧
      (∀ b, r.germ b = (p.concat q).germ b) ∧
      (p.concat q).support ⊆ r.support ∧
      r.support ⊆ (p.concat q).support ∪ (U \ (↑points : Set ℂ)) ∧
      ∀ z ∈ points, r.rayParity u z = (p.concat q).rayParity u z + decide (z ∈ odd) := by
  classical
  let f := Homeomorph.mulLeft₀ u hu
  have hf (z : ℂ) : f z = u * z := rfl
  let embedding := f.toEquiv.toEmbedding
  let points' := points.map embedding
  let odd' := odd.map embedding
  have hsub : odd' ⊆ points' := Finset.map_subset_map.mpr hodd
  have huodd : ∀ z ∈ odd', z ∈ f '' U := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨w, hUodd w hw, rfl⟩
  obtain ⟨l, hls, hlf, hl, hpar⟩ :=
    exists_rayParity_excursion_of_subset (f.isOpenMap _ hU)
      (hconn.image f.continuous) points' odd' hsub huodd
      (Set.mem_image_of_mem f ha) (fun h => haPoints ((Finset.mem_map' embedding).mp h))
  let e := mulComplex u⁻¹ l
  have hstart : e.start = p.finish := by
    change e.endpoint false = _
    rw [endpoint_mulComplex]
    change u⁻¹ * l.start = _
    rw [hls, hf, inv_mul_cancel_left₀ hu]
  have hfinish : e.finish = p.finish := by
    change e.endpoint true = _
    rw [endpoint_mulComplex]
    change u⁻¹ * l.finish = _
    rw [hlf, hf, inv_mul_cancel_left₀ hu]
  have hsupport : e.support ⊆ U \ (↑points : Set ℂ) := by
    intro z hz
    change z ∈ (mulComplex u⁻¹ l).support at hz
    rw [support_mulComplex] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨⟨v, hv, heq⟩, hn⟩ := hl hw
    have heq' : w = u * v := heq.symm
    change u⁻¹ * w ∈ U \ (↑points : Set ℂ)
    rw [heq', inv_mul_cancel_left₀ hu]
    exact ⟨hv, fun h => hn (heq ▸ Finset.mem_map_of_mem embedding h)⟩
  have hparity (z : ℂ) (hz : z ∈ points) : e.rayParity u z = decide (z ∈ odd) := by
    have h : e.rayParity u z = l.rayParity 1 (f z) := by
      unfold Route.rayParity Cslib.Polygonal.rayParity
      simp only [e, mulComplex, mul_inv_cancel_left₀ hu, one_mul, hf]
      rfl
    rw [h, hpar (f z) (Finset.mem_map_of_mem embedding hz)]
    change decide (embedding z ∈ odd.map embedding) = decide (z ∈ odd)
    exact Bool.decide_congr (Finset.mem_map' embedding)
  have he : p.finish = e.start := hstart.symm
  have hq : (p.concat e).finish = q.start := by
    change (p.concat e).endpoint true = q.start
    rw [endpoint_concat p e he]
    exact hfinish.trans hjoin
  refine ⟨(p.concat e).concat q, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [endpoint_concat _ _ hq, endpoint_concat p q hjoin, endpoint_concat p e he]
    cases b <;> rfl
  · intro b
    rw [germ_concat _ _ hq, germ_concat p q hjoin, germ_concat p e he]
    cases b <;> rfl
  · rw [support_concat _ _ hq, support_concat p e he, support_concat p q hjoin]
    intro z hz
    exact hz.elim (fun hp => Or.inl (Or.inl hp)) Or.inr
  · rw [support_concat _ _ hq, support_concat p e he, support_concat p q hjoin]
    rintro z ((hp | hl) | hq')
    · exact Or.inl (Or.inl hp)
    · exact Or.inr (hsupport hl)
    · exact Or.inl (Or.inr hq')
  · intro z hz
    rw [rayParity_concat _ _ hq, rayParity_concat p e he, rayParity_concat p q hjoin,
      hparity z hz]
    ac_rfl

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
  obtain ⟨r, he, hg, hcontains, hsupport, hpar⟩ :=
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
    fun z hz => ?_⟩
  · rw [he, endpoint_concat _ _ rfl]
    cases s <;> rfl
  · rw [hg, germ_concat _ _ rfl]
    cases s
    · exact AffineMap.lineMap_vsub_left a b t
    · exact AffineMap.lineMap_vsub_right a b t
  · have hcut : (p.concat q).rayParity u z = (line a b).rayParity u z :=
      rayParity_line_split a b u z ht
    rw [hpar z hz, hcut]

end Cslib.Polygonal.Route
