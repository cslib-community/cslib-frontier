/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityIntersections
import Mathlib.Algebra.BigOperators.Fin

/-!
# Indexed endpoint and observation parity of polygonal routes

`Route.sum_segment_endpoint_incidence` keeps both ends and every internal bend occurrence.
`Route.rayParity_endpoints_add_eq_sum_intersections` applies the straight observation law
on every actual segment, with explicit reciprocal closed endpoint exclusions. It is a
component theorem, not a drawing perturbation or recognition theorem. The positioned
embedding necessity construction and full #3091 remain separate obligations.
-/

public section

namespace Cslib.Polygonal.Route

/-- The weighted endpoint incidence of all actual route segments is the incidence of
its two parameter ends. Internal bends cancel, including repeated geometric points. -/
theorem sum_segment_endpoint_incidence (p : Route) (weight : Bool) (u z : ℂ) :
    (∑ i : Fin p.segments,
      ((if u * p.point i.castSucc = z then weight else 0) +
        (if u * p.point i.succ = z then weight else 0))) =
      (if u * p.start = z then weight else 0) +
        (if u * p.finish = z then weight else 0) := by
  classical
  let f (i : Fin (p.segments + 1)) : Bool := if u * p.point i = z then weight else 0
  have hlast := Fin.sum_univ_castSucc f
  have hfirst := Fin.sum_univ_succ f
  change (∑ i : Fin p.segments, (f i.castSucc + f i.succ)) =
    f 0 + f (Fin.last p.segments)
  rw [Finset.sum_add_distrib,
    eq_sub_iff_add_eq.mpr hlast.symm,
    eq_sub_iff_add_eq'.mpr hfirst.symm]
  simp only [sub_eq_add_neg, BooleanRing.neg_eq]
  calc
    _ = ((∑ i, f i) + ∑ i, f i) +
        (f 0 + f (Fin.last p.segments)) := by ac_rfl
    _ = _ := by rw [BooleanRing.add_self, zero_add]

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
  let f (n : ℕ) : Bool := if h : n < p.segments + 1 then
    rayParity a b x (p.point ⟨n, h⟩) else 0
  have hsum := Finset.sum_range_sub f p.segments
  have hterm (j : Fin p.segments) :
      f (j.val + 1) - f j.val =
        rayParity a b x (p.point j.succ) + rayParity a b x (p.point j.castSucc) := by
    simp only [f, dite_eq_left (by omega : j.val + 1 < p.segments + 1),
      dite_eq_left (by omega : j.val < p.segments + 1), sub_eq_add_neg, BooleanRing.neg_eq]
    rfl
  rw [Finset.sum_range] at hsum
  simp only [hterm, hpiece, f, dite_eq_left (by omega : p.segments < p.segments + 1),
    dite_eq_left (by omega : 0 < p.segments + 1), sub_eq_add_neg, BooleanRing.neg_eq] at hsum
  exact hsum.symm

end Cslib.Polygonal.Route
