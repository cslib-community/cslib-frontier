/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.ComplexMul
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import CslibFrontier.Foundations.Geometry.Polygonal.RayParityDirection

/-!
# Intersection parity of polygonal routes

`Route.intersectionParity` counts pairs of indexed segments whose open interiors meet.
The count retains both occurrences of any retraced segment. It is symmetric and
invariant under reversal and nonzero complex multiplication. The parity of a concatenated
route is the sum of the parities of its two parts. When the listed nodes of each route
avoid the other route, observing a closed route at the ends of a second route computes
this parity. Two finite families of routes with nondegenerate segments and even endpoint
incidence have even total intersection parity when the selected families avoid each other's
listed points. This also covers two closed routes.
-/

public section

namespace Cslib.Polygonal.Route

open Classical in
/-- The parity of the number of indexed pairs of segments with a common open point. -/
@[expose] noncomputable def intersectionParity (p q : Route) : Bool :=
  ∑ i : Fin p.segments, ∑ j : Fin q.segments, decide
    ((openSegment ℝ (p.point i.castSucc) (p.point i.succ) ∩
      openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty)

/-- Interchanging the routes preserves the parity of their indexed intersections. -/
theorem intersectionParity_symm (p q : Route) :
    p.intersectionParity q = q.intersectionParity p := by
  classical
  unfold intersectionParity
  rw [Finset.sum_comm]
  simp only [Set.inter_comm]

/-- Reversal permutes the indexed segments and reverses the ends of each one. -/
theorem intersectionParity_reverse_left (p q : Route) :
    p.reverse.intersectionParity q = p.intersectionParity q := by
  classical
  unfold intersectionParity
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin p.segments)) _ _ fun i => ?_
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  change decide ((openSegment ℝ (p.point i.castSucc.rev) (p.point i.succ.rev) ∩
    openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty) =
    decide ((openSegment ℝ (p.point i.rev.castSucc) (p.point i.rev.succ) ∩
      openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty)
  rw [Fin.rev_castSucc, Fin.rev_succ, openSegment_symm ℝ (p.point i.rev.succ)]

/-- Joining two routes with matching ends adds their indexed crossing parities against a
third route. No disjointness of the first two supports is needed. -/
theorem intersectionParity_concat_left (p q s : Route) (h : p.finish = q.start) :
    (p.concat q).intersectionParity s = p.intersectionParity s + q.intersectionParity s := by
  classical
  exact sum_segments_concat p q h fun a b =>
    ∑ j : Fin s.segments, decide
      ((openSegment ℝ a b ∩ openSegment ℝ (s.point j.castSucc) (s.point j.succ)).Nonempty)

open Classical in
/-- Two straight routes have one indexed pair of segments, so their intersection parity
is exactly the test for a common point of the two open segments. -/
theorem intersectionParity_line_line (a b c d : ℂ) :
    (line a b).intersectionParity (line c d) =
      decide ((openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty) := by
  unfold intersectionParity
  change (∑ i : Fin 1, ∑ j : Fin 1, _) = _
  rw [Fin.sum_univ_one, Fin.sum_univ_one]; rfl

/-- Nonzero complex multiplication preserves incidence of the open segment pairs. -/
theorem intersectionParity_mulComplex (p q : Route) {u : ℂ} (hu : u ≠ 0) :
    (mulComplex u p).intersectionParity (mulComplex u q) = p.intersectionParity q := by
  classical
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  have hf : Function.Injective f.toAffineMap := fun _ _ h => mul_left_cancel₀ hu h
  unfold intersectionParity
  change (∑ i : Fin p.segments, ∑ j : Fin q.segments, _) = _
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change decide ((openSegment ℝ (f.toAffineMap (p.point i.castSucc))
    (f.toAffineMap (p.point i.succ))) ∩ openSegment ℝ
    (f.toAffineMap (q.point j.castSucc)) (f.toAffineMap (q.point j.succ))).Nonempty = _
  rw [← image_openSegment ℝ f.toAffineMap, ← image_openSegment ℝ f.toAffineMap,
    ← Set.image_inter hf, Set.image_nonempty]

/-- A finite family of routes with nondegenerate pieces admits one coordinate factor
making every piece nonhorizontal. -/
theorem exists_mul_im_ne_of_segments_ne {ι : Type*} [Finite ι] (p : ι → Route)
    (hne : ∀ k (i : Fin (p k).segments), (p k).point i.castSucc ≠ (p k).point i.succ) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ k (i : Fin (p k).segments),
      (u * (p k).point i.castSucc).im ≠ (u * (p k).point i.succ).im := by
  classical
  let _ := Fintype.ofFinite ι
  let points := Finset.univ.biUnion fun k => Finset.univ.image (p k).point
  have hmem (k : ι) (i : Fin ((p k).segments + 1)) : (p k).point i ∈ points :=
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨u, hu, hinj⟩ := exists_mul_im_injOn points
  exact ⟨u, hu, fun k i he => hne k i (hinj (hmem k _) (hmem k _) he)⟩

private theorem mul_point_notMem_support {p q : Route}
    (h : ∀ i : Fin (p.segments + 1), p.point i ∉ q.support)
    {u : ℂ} (hu : u ≠ 0) (i : Fin (p.segments + 1)) :
    u * p.point i ∉ (mulComplex u q).support := by
  have hinj : Function.Injective (fun z => u * z) := fun _ _ => mul_left_cancel₀ hu
  simpa only [support_mulComplex, hinj.mem_set_image] using h i

open Classical in
private theorem even_mul_segment_endpoints {α : Type*} [Fintype α]
    (r : α → Route) (w : α → Bool) {u : ℂ} (hu : u ≠ 0)
    (hw : ∀ z : ℂ, (∑ i, ((if (r i).start = z then w i else 0) +
      (if (r i).finish = z then w i else 0))) = false) (z : ℂ) :
    (∑ k : (i : α) × Fin (r i).segments,
      ((if u * (r k.1).point k.2.castSucc = z then w k.1 else 0) +
        (if u * (r k.1).point k.2.succ = z then w k.1 else 0))) = false := by
  classical
  have hz : u * (u⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  rw [← hz, Fintype.sum_sigma]
  calc
    _ = ∑ i, ((if u * (r i).start = u * (u⁻¹ * z) then w i else 0) +
        (if u * (r i).finish = u * (u⁻¹ * z) then w i else 0)) :=
      Finset.sum_congr rfl (fun i _ => sum_segment_endpoint_incidence (r i) (w i) u _)
    _ = false := by
      simpa only [mul_right_inj' hu] using hw (u⁻¹ * z)

open Classical in
/-- Two finite weighted route families with nondegenerate segments have even total
indexed intersection parity if their selected endpoints cancel and no selected route
contains a listed point of the other selected family. The individual routes may be open. -/
theorem sum_intersectionParity_eq_false_of_even {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Route) (q : κ → Route) (x : ι → Bool) (y : κ → Bool)
    (hp : ∀ i (k : Fin (p i).segments), (p i).point k.castSucc ≠ (p i).point k.succ)
    (hq : ∀ j (k : Fin (q j).segments), (q j).point k.castSucc ≠ (q j).point k.succ)
    (hpq : ∀ i j, x i = true → y j = true →
      ∀ k : Fin ((p i).segments + 1), (p i).point k ∉ (q j).support)
    (hqp : ∀ i j, x i = true → y j = true →
      ∀ k : Fin ((q j).segments + 1), (q j).point k ∉ (p i).support)
    (hx : ∀ z : ℂ, (∑ i, ((if (p i).start = z then x i else 0) +
      (if (p i).finish = z then x i else 0))) = false)
    (hy : ∀ z : ℂ, (∑ j, ((if (q j).start = z then y j else 0) +
      (if (q j).finish = z then y j else 0))) = false) :
    (∑ j, y j * ∑ i, x i * (p i).intersectionParity (q j)) = false := by
  classical
  let routes : ι ⊕ κ → Route := Sum.elim p q
  have hne : ∀ i (k : Fin (routes i).segments),
      (routes i).point k.castSucc ≠ (routes i).point k.succ := Sum.rec hp hq
  obtain ⟨u, hu, hheight⟩ := exists_mul_im_ne_of_segments_ne routes hne
  let a (k : (i : ι) × Fin (p i).segments) := u * (p k.1).point k.2.castSucc
  let b (k : (i : ι) × Fin (p i).segments) := u * (p k.1).point k.2.succ
  let c (k : (j : κ) × Fin (q j).segments) := u * (q k.1).point k.2.castSucc
  let d (k : (j : κ) × Fin (q j).segments) := u * (q k.1).point k.2.succ
  have h := sum_openIntersections_eq_zero_of_even a b c d
    (fun k => x k.1) (fun k => y k.1)
    (fun k => hheight (.inl k.1) k.2) (fun k => hheight (.inr k.1) k.2)
    (fun i j hi hj => by
      have pointP (k : Fin ((p i.1).segments + 1)) :
          u * (p i.1).point k ∉ segment ℝ (c j) (d j) :=
        fun hz => mul_point_notMem_support (hpq i.1 j.1 hi hj) hu k
          (Set.mem_iUnion.mpr ⟨j.2, hz⟩)
      have pointQ (k : Fin ((q j.1).segments + 1)) :
          u * (q j.1).point k ∉ segment ℝ (a i) (b i) :=
        fun hz => mul_point_notMem_support (hqp i.1 j.1 hi hj) hu k
          (Set.mem_iUnion.mpr ⟨i.2, hz⟩)
      exact ⟨pointP _, pointP _, pointQ _, pointQ _⟩)
    (even_mul_segment_endpoints p x hu hx) (even_mul_segment_endpoints q y hu hy)
  rw [← Bool.zero_eq_false, ← h, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fintype.sum_sigma, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intersectionParity_mulComplex (p i) (q j) hu, intersectionParity]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by congr 2

/-- The ray-parity difference of a closed route at the ends of a second route equals
their indexed intersection parity. Each route's listed nodes avoid the other support,
and the given coordinate factor makes every segment nonhorizontal. -/
theorem rayParity_add_eq_intersectionParity_of_closed {p q : Route} (hp : p.finish = p.start)
    {u : ℂ} (hu : u ≠ 0)
    (hph : ∀ i : Fin p.segments, (u * p.point i.castSucc).im ≠ (u * p.point i.succ).im)
    (hqh : ∀ j : Fin q.segments, (u * q.point j.castSucc).im ≠ (u * q.point j.succ).im)
    (hpq : ∀ i : Fin (p.segments + 1), p.point i ∉ q.support)
    (hqp : ∀ j : Fin (q.segments + 1), q.point j ∉ p.support) :
    p.rayParity u q.finish + p.rayParity u q.start = p.intersectionParity q := by
  classical
  have h := rayParity_endpoints_add_eq_sum_intersections
    (fun i : Fin p.segments => u * p.point i.castSucc)
    (fun i : Fin p.segments => u * p.point i.succ) (fun _ => true) (mulComplex u q)
    hph hqh
    (fun j i _ hz => mul_point_notMem_support hqp hu j (Set.mem_iUnion.mpr ⟨i, hz⟩))
    (fun i _ => ⟨mul_point_notMem_support hpq hu i.castSucc,
      mul_point_notMem_support hpq hu i.succ⟩)
    (fun z => by rw [sum_segment_endpoint_incidence p true u z, hp, BooleanRing.add_self]; rfl)
  change p.rayParity u q.finish + p.rayParity u q.start =
    ∑ j : Fin q.segments, ∑ i : Fin p.segments, decide
      ((openSegment ℝ (u * p.point i.castSucc) (u * p.point i.succ) ∩
        openSegment ℝ (u * q.point j.castSucc) (u * q.point j.succ)).Nonempty) at h
  rw [Finset.sum_comm] at h
  exact h.trans (intersectionParity_mulComplex p q hu)

/-- Two closed polygonal routes with nondegenerate segments and reciprocal node avoidance
have even parity of open segment-pair events. The common axis is constructed from the
listed points, so horizontal input segments are allowed. -/
theorem intersectionParity_eq_false_of_closed {p q : Route}
    (hp : p.finish = p.start) (hq : q.finish = q.start)
    (hpne : ∀ i : Fin p.segments, p.point i.castSucc ≠ p.point i.succ)
    (hqne : ∀ j : Fin q.segments, q.point j.castSucc ≠ q.point j.succ)
    (hpq : ∀ i : Fin (p.segments + 1), p.point i ∉ q.support)
    (hqp : ∀ j : Fin (q.segments + 1), q.point j ∉ p.support) :
    p.intersectionParity q = false := by
  classical
  have evenEnds (r : Route) (hr : r.finish = r.start) (z : ℂ) :
      (∑ _ : Fin 1, ((if r.start = z then true else 0) +
        (if r.finish = z then true else 0))) = false := by
    simp only [Fin.sum_univ_one, hr, BooleanRing.add_self, Bool.zero_eq_false]
  have h := sum_intersectionParity_eq_false_of_even (fun _ : Fin 1 => p) (fun _ : Fin 1 => q)
    (fun _ => true) (fun _ => true) (fun _ => hpne) (fun _ => hqne)
    (fun _ _ _ _ => hpq) (fun _ _ _ _ => hqp) (evenEnds p hp) (evenEnds q hq)
  simpa only [Fin.sum_univ_one, ← Bool.one_eq_true, one_mul] using h

end Cslib.Polygonal.Route
