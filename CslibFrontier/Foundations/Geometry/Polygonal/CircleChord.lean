/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayOrder
import CslibFrontier.Foundations.Geometry.SegmentSign
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Circle chords and affine separation

The midpoint of a chord is an interior point of the circle. The two open circular
arcs cut out by its endpoints are exactly the two strict affine half-planes of the
chord. This works for both major and minor arcs, including a diameter.
`circle_chord_inter_iff_alternates` characterizes an interior contact between chords
with four distinct endpoints by alternation around their common circle. A segment through
the center can be cut at the circle, with an exact interval of parameters in the disk.
The chords joining two antipodal pairs across the original diameters are disjoint.
-/

public section

namespace Cslib.Polygonal

/-- The open upper half-plane is the strict angle interval from zero to pi. -/
theorem sbtw_zero_arg_pi_iff (w : ℂ) :
    sbtw (0 : Real.Angle) (w.arg : Real.Angle) (Real.pi : Real.Angle) ↔ 0 < w.im := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hi | hi
    · have ha := Complex.arg_neg_iff.mpr hi
      have hrev := (sbtw_angle_of_lt_of_span_lt ha Real.pi_pos
        (by linarith [Complex.neg_pi_lt_arg w])).cyclic_right
      exact h.not_sbtw hrev
    · by_cases hr : 0 ≤ w.re
      · have ha := Complex.arg_eq_zero_iff.mpr ⟨hr, hi⟩
        rw [ha, Real.Angle.coe_zero] at h
        exact sbtw_irrefl_left h
      · have ha := Complex.arg_eq_pi_iff.mpr ⟨lt_of_not_ge hr, hi⟩
        rw [ha] at h
        exact sbtw_irrefl_right h
  · intro hi
    have h₀ : 0 < w.arg := by
      have hnonneg := Complex.arg_nonneg_iff.mpr hi.le
      have hne : w.arg ≠ 0 := fun h => hi.ne' (Complex.arg_eq_zero_iff.mp h).2
      exact lt_of_le_of_ne hnonneg hne.symm
    have hπ : w.arg < Real.pi := by
      have hne : w.arg ≠ Real.pi := fun h => hi.ne' (Complex.arg_eq_pi_iff.mp h).2
      exact lt_of_le_of_ne (Complex.arg_le_pi w) hne
    simpa only [Real.Angle.coe_zero] using
      sbtw_angle_of_lt_of_span_lt h₀ hπ (by linarith [Real.pi_pos])

/-- Two distinct points on a circle have a chord midpoint strictly inside it. -/
theorem midpoint_mem_ball_of_mem_sphere {z p q : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q) :
    midpoint ℝ p q ∈ Metric.ball z ρ := by
  have hρ : ρ ≠ 0 := by
    intro h
    rw [h, Metric.sphere_zero] at hp hq
    exact hpq ((Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hq).symm)
  rw [← interior_closedBall z hρ]
  exact (strictConvex_closedBall ℝ z ρ).openSegment_subset
    (Metric.sphere_subset_closedBall hp) (Metric.sphere_subset_closedBall hq) hpq
    (midpoint_mem_openSegment p q)

/-- A segment through the center with endpoints outside the closed disk has two strictly
interior cuts on the circle. The cut points are antipodal, and the cut interval describes
the whole preimage of the disk under the affine parameterization. -/
theorem exists_closedBall_lineMap_cuts {a b z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hz : z ∈ openSegment ℝ a b) (ha : a ∉ Metric.closedBall z ρ)
    (hb : b ∉ Metric.closedBall z ρ) :
    ∃ l u : ℝ, 0 < l ∧ l < u ∧ u < 1 ∧
      (∀ t, AffineMap.lineMap a b t ∈ Metric.closedBall z ρ ↔ t ∈ Set.Icc l u) ∧
      (∀ t, AffineMap.lineMap a b t ∈ Metric.sphere z ρ ↔ t = l ∨ t = u) ∧
      midpoint ℝ (AffineMap.lineMap a b l) (AffineMap.lineMap a b u) = z := by
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hab : a ≠ b := by
    rintro rfl
    apply ha
    rw [AffineMap.lineMap_same_apply]
    exact Metric.mem_closedBall_self hρ.le
  have hd : 0 < dist a b := dist_pos.mpr hab
  let δ := ρ / dist a b
  have hδ : 0 < δ := div_pos hρ hd
  have hdist (t : ℝ) : dist (AffineMap.lineMap a b t) (AffineMap.lineMap a b s) =
      |t - s| * dist a b := by rw [dist_lineMap_lineMap, Real.dist_eq]
  have hclosed (t : ℝ) :
      AffineMap.lineMap a b t ∈ Metric.closedBall (AffineMap.lineMap a b s) ρ ↔
        t ∈ Set.Icc (s - δ) (s + δ) := by
    rw [Metric.mem_closedBall, hdist, ← le_div_iff₀ hd, abs_le]
    constructor <;> rintro ⟨hl, hu⟩ <;> exact ⟨by linarith, by linarith⟩
  have hleft : 0 < s - δ := by
    by_contra! h
    apply ha
    simpa only [AffineMap.lineMap_apply_zero] using
      (hclosed 0).mpr ⟨h, by linarith [hs.1]⟩
  have hright : s + δ < 1 := by
    by_contra! h
    apply hb
    simpa only [AffineMap.lineMap_apply_one] using
      (hclosed 1).mpr ⟨by linarith [hs.2], h⟩
  refine ⟨s - δ, s + δ, hleft, by linarith, hright, hclosed, ?_, ?_⟩
  · intro t
    rw [Metric.mem_sphere, hdist, ← eq_div_iff hd.ne']
    change |t - s| = δ ↔ _
    have habs : |t - s| = δ ↔ t - s = δ ∨ t - s = -δ := by
      rw [← abs_eq_abs, abs_of_pos hδ]
    rw [habs]
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (rfl | rfl)
      · exact Or.inr (by ring)
      · exact Or.inl (by ring)
  · rw [← AffineMap.map_midpoint]
    congr 1
    rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv]
    ring

/-- Join `p` to `q` and join their antipodes `x` to `y`. These closed chords are disjoint
whenever `p` and `q` lie on the same circle and `q` is not the antipode of `p`. -/
theorem disjoint_segments_of_antipodal_pairs {z p q x y : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hqx : q ≠ x) (hpx : midpoint ℝ p x = z) (hqy : midpoint ℝ q y = z) :
    Disjoint (segment ℝ p q) (segment ℝ x y) := by
  let reflect := AffineEquiv.pointReflection ℝ z
  have hx : reflect p = x := midpoint_eq_iff.mp hpx
  have hy : reflect q = y := midpoint_eq_iff.mp hqy
  have himage : reflect.toAffineMap '' segment ℝ p q = segment ℝ x y := by
    rw [image_segment, AffineEquiv.coe_toAffineMap, hx, hy]
  apply Set.disjoint_left.mpr
  intro w hw hwr
  rw [← himage] at hwr
  obtain ⟨v, hv, hvw⟩ := hwr
  have hmid : midpoint ℝ v w = z := midpoint_eq_iff.mpr hvw
  have hconv : Convex ℝ (segment ℝ p q) := convex_segment p q
  have hz : z ∈ segment ℝ p q := hmid ▸ hconv.midpoint_mem hv hw
  have hzmid : midpoint ℝ p q = z := by
    have hdist := dist_add_dist_of_mem_segment hz
    have hp' := Metric.mem_sphere.mp hp
    have hq' := (dist_comm z q).trans (Metric.mem_sphere.mp hq)
    exact (eq_midpoint_of_dist_eq_half
      (by linarith only [hdist, hp', hq']) (by linarith only [hdist, hp', hq'])).symm
  exact hqx ((midpoint_eq_iff.mp hzmid).symm.trans hx)

/-- The signed coordinate perpendicular to a chord, scaled so its normal has unit
coordinate. The first endpoint fixes the sign; its counterclockwise arc is positive. -/
@[expose] noncomputable def chordCoordinate (p q : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  { toFun := fun x => ((x - midpoint ℝ p q) / (p - midpoint ℝ p q)).im
    linear := Complex.imCLM.toLinearMap.comp
      (LinearMap.mulRight ℝ (p - midpoint ℝ p q)⁻¹)
    map_vadd' := by
      intro x y
      simp only [vadd_eq_add, Complex.add_im, div_eq_mul_inv,
        add_sub_assoc, add_mul, Complex.add_im]
      rfl }

/-- A circle arc has exactly the sign of its chord's affine coordinate. All real
coordinates are retained, with no angular-span restriction. -/
theorem sbtw_arg_iff_chordCoordinate_pos {z p q x : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hx : x ∈ Metric.sphere z ρ) (hpq : p ≠ q) (hpx : p ≠ x) (hxq : x ≠ q) :
    sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
      ((q - z).arg : Real.Angle) ↔ 0 < chordCoordinate p q x := by
  let m := midpoint ℝ p q
  have hm : m ∈ Metric.ball z ρ := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hρ : 0 < ρ := (dist_nonneg : 0 ≤ dist m z).trans_lt hm
  have hpm : p - m ≠ 0 := by
    intro h
    have h' : p = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp (h' ▸ hm)
  have hxm : x - m ≠ 0 := by
    intro h
    have h' : x = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx (h' ▸ hm)
  have hqm : q - m = -(p - m) := by
    simp only [m, right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  have horder := sbtw_arg_sub_iff_of_mem_ball (Metric.mem_ball_self hρ) hm
    hp hx hq hpx hxq hpq
  rw [horder, hqm, Complex.arg_neg_coe_angle hpm]
  have htranslate := sbtw_angle_add_right_iff
    (0 : Real.Angle) (((x - m).arg : Real.Angle) - (p - m).arg) Real.pi
    ((p - m).arg : Real.Angle)
  simp only [zero_add, sub_add_cancel, add_comm (Real.pi : Real.Angle)] at htranslate
  rw [htranslate, ← Complex.arg_div_coe_angle hxm hpm, sbtw_zero_arg_pi_iff]
  rfl

/-- Reversing the oriented chord reverses its affine coordinate. -/
theorem chordCoordinate_swap (p q : ℂ) : chordCoordinate q p = -chordCoordinate p q := by
  ext x
  change ((x - midpoint ℝ q p) / (q - midpoint ℝ q p)).im =
    -((x - midpoint ℝ p q) / (p - midpoint ℝ p q)).im
  rw [midpoint_comm q p]
  have hq : q - midpoint ℝ p q = -(p - midpoint ℝ p q) := by
    simp only [right_sub_midpoint, left_sub_midpoint, ← smul_neg, neg_sub]
  rw [hq, div_neg, Complex.neg_im]

/-- Offset the chord midpoint in its oriented normal direction. -/
@[expose] noncomputable def chordOffset (p q : ℂ) (t : ℝ) : ℂ :=
  midpoint ℝ p q + t • (Complex.I * (p - midpoint ℝ p q))

/-- A finite collection on the two open arcs of a circle admits arbitrarily small
opposite interior offsets strictly separated from their assigned ports. Either port set
may be empty. The offsets and affine separator are constructed from the circle and gaps. -/
theorem exists_split_offsets_of_circle_gaps {z p q : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (A B : Finset ℂ)
    (hA : ∀ x ∈ A, x ∈ Metric.sphere z ρ ∧
      sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((q - z).arg : Real.Angle))
    (hB : ∀ x ∈ B, x ∈ Metric.sphere z ρ ∧
      sbtw ((q - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
        ((p - z).arg : Real.Angle)) {bound : ℝ} (hbound : 0 < bound) :
    ∃ ε ∈ Set.Ioo 0 bound,
      chordOffset p q ε ∈ Metric.ball z ρ ∧ chordOffset p q (-ε) ∈ Metric.ball z ρ ∧
      chordCoordinate p q (chordOffset p q (-ε)) <
        chordCoordinate p q (chordOffset p q ε) ∧
      (∀ x ∈ A, chordCoordinate p q (chordOffset p q ε) < chordCoordinate p q x) ∧
      (∀ x ∈ B, chordCoordinate p q x < chordCoordinate p q (chordOffset p q (-ε))) := by
  classical
  let m := midpoint ℝ p q
  let n := Complex.I * (p - m)
  let f := chordCoordinate p q
  have hm : m ∈ Metric.ball z ρ := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hpm : p - m ≠ 0 := by
    intro h
    have h' : p = m := sub_eq_zero.mp h
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp (h' ▸ hm)
  have hpos : ∀ x ∈ A, 0 < f x := by
    intro x hx
    have h := hA x hx
    exact (sbtw_arg_iff_chordCoordinate_pos hp hq h.1 hpq
      (fun heq => sbtw_irrefl_left (heq ▸ h.2))
      (fun heq => sbtw_irrefl_right (heq ▸ h.2))).mp h.2
  have hneg : ∀ x ∈ B, f x < 0 := by
    intro x hx
    have h := hB x hx
    have hsign := (sbtw_arg_iff_chordCoordinate_pos hq hp h.1 hpq.symm
      (fun heq => sbtw_irrefl_left (heq ▸ h.2))
      (fun heq => sbtw_irrefl_right (heq ▸ h.2))).mp h.2
    rw [chordCoordinate_swap] at hsign
    change 0 < -f x at hsign
    linarith
  have hcoord (t : ℝ) : f (m + t • n) = t := by
    change ((m + t • (Complex.I * (p - m)) - m) / (p - m)).im = t
    rw [add_sub_cancel_left, Complex.real_smul]
    simp only [← mul_assoc, mul_div_cancel_right₀ _ hpm, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
  have hplus : ContinuousAt (fun t : ℝ => m + t • n) 0 := by fun_prop
  have hminus : ContinuousAt (fun t : ℝ => m + (-t) • n) 0 := by fun_prop
  have hpball : ∀ᶠ t in nhds (0 : ℝ), m + t • n ∈ Metric.ball z ρ :=
    hplus.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hm))
  have hmball : ∀ᶠ t in nhds (0 : ℝ), m + (-t) • n ∈ Metric.ball z ρ :=
    hminus.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hm))
  have hAP : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ A, t < f x :=
    (Filter.eventually_all_finset A).mpr fun x hx =>
      continuousAt_id.eventually_lt continuousAt_const (hpos x hx)
  have hBP : ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ B, f x < -t :=
    (Filter.eventually_all_finset B).mpr fun x hx =>
      continuousAt_const.eventually_lt continuousAt_id.neg (by simpa using hneg x hx)
  have hlocal := hpball.and (hmball.and (hAP.and hBP))
  obtain ⟨δ, hδ, hδlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let ε := min δ bound / 2
  have hε : 0 < ε := div_pos (lt_min hδ hbound) (by norm_num)
  have hεδ : ε < δ := by
    have h := min_le_left δ bound
    dsimp [ε]
    linarith
  have hεbound : ε < bound := by
    have h := min_le_right δ bound
    dsimp [ε]
    linarith
  have heps : dist ε (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact hεδ
  obtain ⟨ha, hb, hA', hB'⟩ := hδlocal heps
  refine ⟨ε, ⟨hε, hεbound⟩, ha, hb, ?_, ?_, ?_⟩
  · change f (m + (-ε) • n) < f (m + ε • n)
    rw [hcoord, hcoord]
    linarith
  · change ∀ x ∈ A, f (m + ε • n) < f x
    rw [hcoord]
    exact hA'
  · change ∀ x ∈ B, f x < f (m + (-ε) • n)
    rw [hcoord]
    exact hB'

private theorem exists_lineMap_eq_of_chordCoordinate_eq_zero {p q x : ℂ}
    (hpq : p ≠ q) (hx : chordCoordinate p q x = 0) :
    ∃ t : ℝ, AffineMap.lineMap p q t = x := by
  let m := midpoint ℝ p q
  have hd : p - m ≠ 0 := fun h => hpq
    ((left_eq_midpoint_iff (R := ℝ)).mp (sub_eq_zero.mp h))
  let w := (x - m) / (p - m)
  let s := w.re
  have hw : w = (s : ℂ) := Complex.ext rfl hx
  have hreal : s • (p - m) + m = x := by
    rw [Complex.real_smul, ← hw]
    change (x - m) / (p - m) * (p - m) + m = x
    rw [div_mul_cancel₀ _ hd, sub_add_cancel]
  have hm : m = AffineMap.lineMap p q (1 / 2 : ℝ) := by
    simp [m, midpoint, invOf_eq_inv, one_div]
  refine ⟨(1 - s) / 2, ?_⟩
  calc
    _ = AffineMap.lineMap p m (1 - s) := by
      rw [hm, AffineMap.lineMap_lineMap_right]
      congr 1
      ring
    _ = AffineMap.lineMap m p s := AffineMap.lineMap_apply_one_sub p m s
    _ = x := by rw [AffineMap.lineMap_apply_module']; exact hreal

private theorem lineMap_parameter_nonneg_of_mem_closedBall {z p q : ℂ} {ρ t : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (ht : AffineMap.lineMap p q t ∈ Metric.closedBall z ρ) : 0 ≤ t := by
  by_contra! htneg
  have hmid := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hρ : ρ ≠ 0 := ((dist_nonneg : 0 ≤ dist (midpoint ℝ p q) z).trans_lt hmid).ne'
  let s := -t / (1 - t)
  have hden : 0 < 1 - t := by linarith
  have hs : s ∈ Set.Ioo 0 1 :=
    ⟨div_pos (neg_pos.mpr htneg) hden, (div_lt_one hden).mpr (by linarith)⟩
  have hpar : 1 - (1 - s) * (1 - t) = 0 := by
    dsimp only [s]
    field_simp
    ring
  have hline : AffineMap.lineMap (AffineMap.lineMap p q t) q s = p := by
    rw [AffineMap.lineMap_lineMap_left, hpar, AffineMap.lineMap_apply_zero]
  have hne : AffineMap.lineMap p q t ≠ q := by
    intro he
    rcases AffineMap.lineMap_eq_right_iff.mp he with h | h
    · exact hpq h
    · linarith
  have hball := (strictConvex_closedBall ℝ z ρ).openSegment_subset ht
    (Metric.sphere_subset_closedBall hq) hne (lineMap_mem_openSegment ℝ _ _ hs)
  rw [interior_closedBall z hρ, hline] at hball
  exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp hball

private theorem lineMap_parameter_mem_Icc_of_mem_closedBall {z p q : ℂ} {ρ t : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ) (hpq : p ≠ q)
    (ht : AffineMap.lineMap p q t ∈ Metric.closedBall z ρ) : t ∈ Set.Icc 0 1 := by
  have h : AffineMap.lineMap q p (1 - t) ∈ Metric.closedBall z ρ := by
    rwa [AffineMap.lineMap_apply_one_sub]
  have hright := lineMap_parameter_nonneg_of_mem_closedBall hq hp hpq.symm h
  exact ⟨lineMap_parameter_nonneg_of_mem_closedBall hp hq hpq ht, by linarith⟩

/-- Two chords with four distinct endpoints on the same circle meet in their open
segments precisely when exactly one endpoint of the second chord lies in the strict
oriented arc from the first endpoint of the first chord to its other endpoint. -/
theorem circle_chord_inter_iff_alternates {z p q x y : ℂ} {ρ : ℝ}
    (hp : p ∈ Metric.sphere z ρ) (hq : q ∈ Metric.sphere z ρ)
    (hx : x ∈ Metric.sphere z ρ) (hy : y ∈ Metric.sphere z ρ)
    (hpq : p ≠ q) (hxy : x ≠ y)
    (hpx : p ≠ x) (hxq : x ≠ q) (hpy : p ≠ y) (hyq : y ≠ q) :
    (openSegment ℝ p q ∩ openSegment ℝ x y).Nonempty ↔
      Xor (sbtw ((p - z).arg : Real.Angle) ((x - z).arg : Real.Angle)
          ((q - z).arg : Real.Angle))
        (sbtw ((p - z).arg : Real.Angle) ((y - z).arg : Real.Angle)
          ((q - z).arg : Real.Angle)) := by
  rw [sbtw_arg_iff_chordCoordinate_pos hp hq hx hpq hpx hxq,
    sbtw_arg_iff_chordCoordinate_pos hp hq hy hpq hpy hyq]
  let f := chordCoordinate p q
  have hmid := midpoint_mem_ball_of_mem_sphere hp hq hpq
  have hρ : ρ ≠ 0 := ((dist_nonneg : 0 ≤ dist (midpoint ℝ p q) z).trans_lt hmid).ne'
  have inside {a b : ℂ} (ha : a ∈ Metric.sphere z ρ) (hb : b ∈ Metric.sphere z ρ)
      (hab : a ≠ b) {w : ℂ} (hw : w ∈ openSegment ℝ a b) : w ∈ Metric.ball z ρ := by
    rw [← interior_closedBall z hρ]
    exact (strictConvex_closedBall ℝ z ρ).openSegment_subset
      (Metric.sphere_subset_closedBall ha) (Metric.sphere_subset_closedBall hb) hab hw
  have parameter_mem_Ioo {w : ℂ} {t : ℝ} (hwt : AffineMap.lineMap p q t = w)
      (hwb : w ∈ Metric.closedBall z ρ) (hpw : p ≠ w) (hwq : w ≠ q) :
      t ∈ Set.Ioo 0 1 := by
    have ht := lineMap_parameter_mem_Icc_of_mem_closedBall hp hq hpq (hwt ▸ hwb)
    refine ⟨lt_of_le_of_ne ht.1 (fun he => hpw ?_),
      lt_of_le_of_ne ht.2 (fun he => hwq ?_)⟩
    · simpa only [← he, AffineMap.lineMap_apply_zero] using hwt
    · simpa only [he, AffineMap.lineMap_apply_one] using hwt.symm
  have f_ne_zero {w : ℂ} (hw : w ∈ Metric.sphere z ρ) (hpw : p ≠ w) (hwq : w ≠ q) :
      f w ≠ 0 := by
    intro hf
    obtain ⟨t, hwt⟩ := exists_lineMap_eq_of_chordCoordinate_eq_zero hpq hf
    have ht := parameter_mem_Ioo hwt (Metric.sphere_subset_closedBall hw) hpw hwq
    have h := inside hp hq hpq (lineMap_mem_openSegment ℝ _ _ ht)
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hw (hwt ▸ h)
  have left_zero {a b : ℂ} (hab : a ≠ b) : chordCoordinate a b a = 0 := by
    have hd : a - midpoint ℝ a b ≠ 0 := fun he => hab
      ((left_eq_midpoint_iff (R := ℝ)).mp (sub_eq_zero.mp he))
    change ((a - midpoint ℝ a b) / (a - midpoint ℝ a b)).im = 0
    rw [div_self hd, Complex.one_im]
  have hf₀ : f p = 0 := left_zero hpq
  have hf₁ : f q = 0 := by
    have h := left_zero hpq.symm
    rw [chordCoordinate_swap] at h
    exact neg_eq_zero.mp h
  have himage : f '' openSegment ℝ p q = {0} := by
    rw [image_openSegment ℝ f, hf₀, hf₁, openSegment_same]
  change _ ↔ Xor (0 < f x) (0 < f y)
  rw [← Cslib.zero_mem_openSegment_iff_xor_pos (f_ne_zero hx hpx hxq)
    (f_ne_zero hy hpy hyq), ← image_openSegment ℝ f]
  constructor
  · rintro ⟨w, hwpq, hwxy⟩
    have hw := Set.mem_image_of_mem f hwpq
    rw [himage] at hw
    exact ⟨w, hwxy, Set.mem_singleton_iff.mp hw⟩
  · rintro ⟨w, hw, hf⟩
    have hb := inside hx hy hxy hw
    obtain ⟨t, hwt⟩ := exists_lineMap_eq_of_chordCoordinate_eq_zero hpq hf
    have hpw : p ≠ w := fun he => Set.disjoint_left.mp Metric.sphere_disjoint_ball hp (he ▸ hb)
    have hwq : w ≠ q := fun he => Set.disjoint_left.mp Metric.sphere_disjoint_ball hq (he ▸ hb)
    have ht := parameter_mem_Ioo hwt (Metric.ball_subset_closedBall hb) hpw hwq
    exact ⟨w, hwt ▸ lineMap_mem_openSegment ℝ _ _ ht, hw⟩

end Cslib.Polygonal
