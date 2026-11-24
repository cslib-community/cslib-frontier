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
invariant under nonzero complex multiplication. When the listed nodes of each route
avoid the other route, observing a closed route at the ends of a second route computes
this parity. Two such closed routes with nondegenerate segments have even intersection parity.
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

/-- Nonzero complex multiplication preserves incidence of the open segment pairs. -/
theorem intersectionParity_mulComplex (p q : Route) {u : ℂ} (hu : u ≠ 0) :
    (mulComplex u p).intersectionParity (mulComplex u q) = p.intersectionParity q := by
  classical
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
  have hf : Function.Injective f := fun _ _ h => mul_left_cancel₀ hu h
  unfold intersectionParity
  change (∑ i : Fin p.segments, ∑ j : Fin q.segments, _) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change decide ((openSegment ℝ (f.toAffineMap (p.point i.castSucc))
    (f.toAffineMap (p.point i.succ))) ∩ openSegment ℝ
    (f.toAffineMap (q.point j.castSucc)) (f.toAffineMap (q.point j.succ))).Nonempty = _
  rw [← image_openSegment ℝ f.toAffineMap, ← image_openSegment ℝ f.toAffineMap,
    ← Set.image_inter (show Function.Injective f.toAffineMap from hf), Set.image_nonempty]

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
  let routes : Bool → Route := fun b => if b then q else p
  have hne (b : Bool) (i : Fin (routes b).segments) :
      (routes b).point i.castSucc ≠ (routes b).point i.succ := by
    cases b
    · exact hpne i
    · exact hqne i
  obtain ⟨u, hu, hheight⟩ := exists_mul_im_ne_of_segments_ne routes hne
  have h := rayParity_add_eq_intersectionParity_of_closed (q := q) hp hu
    (hheight false) (hheight true) hpq hqp
  rw [hq, BooleanRing.add_self] at h
  exact h.symm

end Cslib.Polygonal.Route
