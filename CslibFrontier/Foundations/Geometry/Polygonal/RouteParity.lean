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
public import Mathlib.Topology.Connected.PathConnected
import CslibFrontier.Foundations.Geometry.Polygonal.SampledRoute
import CslibFrontier.Foundations.Geometry.PuncturedPaths
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

end Cslib.Polygonal.Route
