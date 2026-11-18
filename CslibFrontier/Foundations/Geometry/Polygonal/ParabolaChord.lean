/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import CslibFrontier.Foundations.Geometry.Polygonal.RayOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Intersections of parabola chords

The points `(x,x²)` realize strict endpoint alternation by actual straight segments in the
real plane. Four distinct endpoints give exactly one common interior point precisely when
one endpoint of the second chord lies strictly between the first chord's real coordinates.
No other parabola point lies on a chord. These are original coordinate calculations, using
Mathlib's affine images of real segments. They make no general-position claim for three chords.

## Main definitions

* `Cslib.Polygonal.parabolaPoint`: the real parabola as points of `ℂ`.

## Main results

* `Cslib.Polygonal.parabolaPoint_mem_segment_iff`: a chord contains no third parabola point.
* `Cslib.Polygonal.parabolaChord_inter_subsingleton`: distinct supporting chords have at most
  one common interior point.
* `Cslib.Polygonal.existsUnique_parabolaChord_inter_iff`: endpoint alternation is exactly one
  common interior point of two chords with four distinct endpoints.
* `Cslib.Polygonal.arg_parabolaChord_lt_iff`: rays to the right of a nonnegative parabola
  parameter have strictly increasing arguments in their other endpoint.
-/

public section

namespace Cslib.Polygonal

/-- The point with real coordinate `x` and imaginary coordinate `x²`. -/
@[expose] def parabolaPoint (x : ℝ) : ℂ := ⟨x, x ^ 2⟩

/-- Distinct real parameters name distinct parabola points. -/
theorem parabolaPoint_injective : Function.Injective parabolaPoint :=
  fun _ _ h => congrArg Complex.re h

/-- Chords leaving a nonnegative parabola parameter toward larger parameters have arguments
in increasing endpoint order. The comparison includes equal other endpoints. -/
theorem arg_parabolaChord_lt_iff {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hac : a < c) :
    (parabolaPoint b - parabolaPoint a).arg <
      (parabolaPoint c - parabolaPoint a).arg ↔ b < c := by
  have him {x : ℝ} (hx : a < x) : 0 < (parabolaPoint x - parabolaPoint a).im := by
    change 0 < x ^ 2 - a ^ 2
    have hsum : 0 < x + a := by linarith
    nlinarith only [mul_pos (sub_pos.mpr hx) hsum]
  have hb := him hab
  have hc := him hac
  rw [arg_lt_arg_iff_det_pos hb.ne' hc.ne'
    (iff_of_false (not_lt.mpr hb.le) (not_lt.mpr hc.le))]
  have hdet :
      (parabolaPoint b - parabolaPoint a).re * (parabolaPoint c - parabolaPoint a).im -
        (parabolaPoint b - parabolaPoint a).im * (parabolaPoint c - parabolaPoint a).re =
          ((b - a) * (c - a)) * (c - b) := by
    simp only [parabolaPoint, Complex.sub_re, Complex.sub_im]
    ring
  rw [hdet, mul_pos_iff_of_pos_left (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hac)), sub_pos]

private noncomputable def chordMap (a b : ℝ) : ℝ →ᵃ[ℝ] ℂ :=
  AffineMap.lineMap (⟨0, -a * b⟩ : ℂ) ⟨1, a + b - a * b⟩

private theorem chordMap_apply (a b x : ℝ) :
    chordMap a b x = ⟨x, (a + b) * x - a * b⟩ := by
  apply Complex.ext <;>
    simp [chordMap, AffineMap.lineMap_apply_module, Complex.real_smul]; ring

private theorem chordMap_left (a b : ℝ) : chordMap a b a = parabolaPoint a := by
  rw [chordMap_apply]
  apply Complex.ext <;> simp only [parabolaPoint]; ring

private theorem chordMap_right (a b : ℝ) : chordMap a b b = parabolaPoint b := by
  simpa only [chordMap_apply, add_comm b a, mul_comm b a] using chordMap_left b a

private theorem openChord_eq_image (a b : ℝ) :
    openSegment ℝ (parabolaPoint a) (parabolaPoint b) =
      chordMap a b '' openSegment ℝ a b := by
  rw [image_openSegment, chordMap_left, chordMap_right]

private theorem mem_openChord_iff {a b : ℝ} (hab : a ≠ b) (z : ℂ) :
    z ∈ openSegment ℝ (parabolaPoint a) (parabolaPoint b) ↔
      z.re ∈ Set.Ioo (min a b) (max a b) ∧ z.im = (a + b) * z.re - a * b := by
  rw [openChord_eq_image, openSegment_eq_Ioo' hab]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [chordMap_apply]
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, hy⟩
    refine ⟨z.re, hx, ?_⟩
    rw [chordMap_apply]
    exact Complex.ext rfl hy.symm

/-- A closed chord contains only its two parabola endpoints, even when they coincide. -/
theorem parabolaPoint_mem_segment_iff (a b x : ℝ) :
    parabolaPoint x ∈ segment ℝ (parabolaPoint a) (parabolaPoint b) ↔ x = a ∨ x = b := by
  constructor
  · intro hx
    have himage := image_segment ℝ (chordMap a b) a b
    rw [chordMap_left, chordMap_right] at himage
    obtain ⟨y, _, hy⟩ := himage.symm ▸ hx
    have hre := congrArg Complex.re hy
    have him := congrArg Complex.im hy
    rw [chordMap_apply] at hre him
    change y = x at hre
    change (a + b) * y - a * b = x ^ 2 at him
    have hprod : (x - a) * (x - b) = 0 := by rw [hre] at him; nlinarith only [him]
    exact (mul_eq_zero.mp hprod).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

private noncomputable def chordResidual (a b : ℝ) : ℂ →ᵃ[ℝ] ℝ :=
  (a + b) • Complex.reCLM.toLinearMap.toAffineMap - AffineMap.const ℝ ℂ (a * b) -
    Complex.imCLM.toLinearMap.toAffineMap

private theorem residual_parabola (a b x : ℝ) :
    chordResidual a b (parabolaPoint x) = (x - a) * (b - x) := by
  change (a + b) * x - a * b - x ^ 2 = _
  ring

private theorem residual_ne_zero {a b x : ℝ} (hax : a ≠ x) (hbx : b ≠ x) :
    chordResidual a b (parabolaPoint x) ≠ 0 := by
  rw [residual_parabola]
  exact mul_ne_zero (sub_ne_zero.mpr hax.symm) (sub_ne_zero.mpr hbx)

private theorem residual_pos_iff (a b x : ℝ) :
    0 < chordResidual a b (parabolaPoint x) ↔ x ∈ Set.Ioo (min a b) (max a b) := by
  rw [residual_parabola, mul_pos_iff]
  simp only [sub_pos, sub_neg, Set.mem_Ioo]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso; linarith [h.1, h.2]
    · exact Or.inl
  · rw [min_eq_right hab, max_eq_left hab]
    constructor
    · rintro (h | h)
      · exfalso; linarith [h.1, h.2]
      · exact ⟨h.2, h.1⟩
    · exact fun h => Or.inr ⟨h.2, h.1⟩

private theorem zero_mem_openSegment_iff_xor_pos {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    0 ∈ openSegment ℝ u v ↔ Xor (0 < u) (0 < v) := by
  have ordered {s t : ℝ} (hst : s ≤ t) (hs : s ≠ 0) :
      0 ∈ openSegment ℝ s t ↔ Xor (0 < s) (0 < t) := by
    by_cases he : s = t
    · subst t
      simp [openSegment_same, Xor, hs.symm]
    · rw [openSegment_eq_Ioo (lt_of_le_of_ne hst he)]
      constructor
      · intro h
        exact Or.inr ⟨h.2, not_lt_of_ge h.1.le⟩
      · rintro (⟨h, hnot⟩ | ⟨h, hnot⟩)
        · exact False.elim (hnot (h.trans_le hst))
        · exact ⟨lt_of_le_of_ne (le_of_not_gt hnot) hs, h⟩
  rcases le_total u v with huv | huv
  · exact ordered huv hu
  · rw [openSegment_symm, xor_comm (0 < u) (0 < v)]
    exact ordered huv hv

private theorem im_gt_sq_of_mem_openChord {a b : ℝ} (hab : a ≠ b) {z : ℂ}
    (hz : z ∈ openSegment ℝ (parabolaPoint a) (parabolaPoint b)) : z.re ^ 2 < z.im := by
  obtain ⟨hbetween, hline⟩ := (mem_openChord_iff hab z).mp hz
  have hpos := (residual_pos_iff a b z.re).mpr hbetween
  rw [residual_parabola] at hpos
  nlinarith only [hpos, hline]

private theorem openChord_inter_nonempty_iff {a b c d : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (openSegment ℝ (parabolaPoint a) (parabolaPoint b) ∩
      openSegment ℝ (parabolaPoint c) (parabolaPoint d)).Nonempty ↔
        Xor (c ∈ Set.Ioo (min a b) (max a b)) (d ∈ Set.Ioo (min a b) (max a b)) := by
  let f := (chordResidual a b).comp (chordMap c d)
  have hc : f c = chordResidual a b (parabolaPoint c) := by
    change chordResidual a b (chordMap c d c) = _
    rw [chordMap_left]
  have hd : f d = chordResidual a b (parabolaPoint d) := by
    change chordResidual a b (chordMap c d d) = _
    rw [chordMap_right]
  have hc0 : f c ≠ 0 := by rw [hc]; exact residual_ne_zero hac hbc
  have hd0 : f d ≠ 0 := by rw [hd]; exact residual_ne_zero had hbd
  have hsign : 0 ∈ openSegment ℝ (f c) (f d) ↔
      Xor (c ∈ Set.Ioo (min a b) (max a b)) (d ∈ Set.Ioo (min a b) (max a b)) := by
    rw [zero_mem_openSegment_iff_xor_pos hc0 hd0, hc, hd, residual_pos_iff,
      residual_pos_iff]
  constructor
  · rintro ⟨z, hz, hw⟩
    apply hsign.mp
    rw [← image_openSegment ℝ f c d]
    obtain ⟨x, hx, hzx⟩ := openChord_eq_image c d ▸ hw
    refine ⟨x, hx, ?_⟩
    have hline := ((mem_openChord_iff hab z).mp hz).2
    change chordResidual a b (chordMap c d x) = 0
    rw [hzx]
    change (a + b) * z.re - a * b - z.im = 0
    linarith only [hline]
  · intro h
    have hzero := hsign.mpr h
    rw [← image_openSegment ℝ f c d] at hzero
    obtain ⟨x, hx, hfx⟩ := hzero
    let z := chordMap c d x
    have hcdz : z ∈ openSegment ℝ (parabolaPoint c) (parabolaPoint d) := by
      rw [openChord_eq_image]
      exact ⟨x, hx, rfl⟩
    have hline : z.im = (a + b) * z.re - a * b := by
      change (a + b) * z.re - a * b - z.im = 0 at hfx
      linarith only [hfx]
    have hpos : 0 < chordResidual a b (parabolaPoint z.re) := by
      have hstrict := im_gt_sq_of_mem_openChord hcd hcdz
      change 0 < (a + b) * z.re - a * b - z.re ^ 2
      linarith only [hline, hstrict]
    refine ⟨z, ?_, hcdz⟩
    exact (mem_openChord_iff hab z).mpr ⟨(residual_pos_iff a b z.re).mp hpos, hline⟩

/-- Two nondegenerate parabola chords have at most one common interior point when the
first endpoint of the second chord differs from both endpoints of the first. The other
endpoint may be shared. In particular the claim includes parallel supporting lines. -/
theorem parabolaChord_inter_subsingleton {a b c d : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (hbc : b ≠ c) :
    (openSegment ℝ (parabolaPoint a) (parabolaPoint b) ∩
      openSegment ℝ (parabolaPoint c) (parabolaPoint d)).Subsingleton := by
  intro z hz w hw
  have hza := ((mem_openChord_iff hab z).mp hz.1).2
  have hzc := ((mem_openChord_iff hcd z).mp hz.2).2
  have hwa := ((mem_openChord_iff hab w).mp hw.1).2
  have hwc := ((mem_openChord_iff hcd w).mp hw.2).2
  have hslope : a + b - (c + d) ≠ 0 := by
    intro hsum
    have hsumz : (a + b - (c + d)) * z.re = 0 := by rw [hsum, zero_mul]
    have hsumc : (a + b - (c + d)) * c = 0 := by rw [hsum, zero_mul]
    have hprod : (c - a) * (c - b) = 0 := by
      nlinarith only [hsumz, hsumc, hza, hzc]
    exact (mul_ne_zero (sub_ne_zero.mpr hac.symm) (sub_ne_zero.mpr hbc.symm)) hprod
  have hprod : (a + b - (c + d)) * (z.re - w.re) = 0 := by
    nlinarith only [hza, hzc, hwa, hwc]
  have hre : z.re = w.re := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hslope)
  exact Complex.ext hre (by rw [hza, hwa, hre])

/-- Four distinct parabola endpoints have exactly one common chord-interior point precisely
when the two endpoints of the second chord have different strict interval memberships.
All six endpoint inequalities are explicit; neither chord is allowed to degenerate. -/
theorem existsUnique_parabolaChord_inter_iff {a b c d : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (∃! z : ℂ, z ∈ openSegment ℝ (parabolaPoint a) (parabolaPoint b) ∧
      z ∈ openSegment ℝ (parabolaPoint c) (parabolaPoint d)) ↔
        Xor (c ∈ Set.Ioo (min a b) (max a b)) (d ∈ Set.Ioo (min a b) (max a b)) := by
  constructor
  · rintro ⟨z, hz, _⟩
    exact (openChord_inter_nonempty_iff hab hcd hac had hbc hbd).mp ⟨z, hz⟩
  · intro h
    obtain ⟨z, hz⟩ := (openChord_inter_nonempty_iff hab hcd hac had hbc hbd).mpr h
    exact ⟨z, hz, fun w hw => parabolaChord_inter_subsingleton hab hcd hac hbc hw hz⟩

end Cslib.Polygonal
