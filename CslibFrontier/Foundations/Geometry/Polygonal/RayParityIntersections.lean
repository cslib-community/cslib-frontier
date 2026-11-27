/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityEven
import CslibFrontier.Foundations.Geometry.SegmentSign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Intersection parity along a straight observation segment

This is original finite coordinate geometry. The observation and listed segments are
nonhorizontal. Observation endpoints avoid selected closed segments, and selected segment
ends avoid the closed observation. Endpoint-height jumps
are summed with occurrence multiplicity, including simultaneous events and duplicate
segments. The intended application is isolated-interior ray-parity transport.

## Main result

* `Cslib.Polygonal.rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero`:
  actual open-intersection parity from endpoint ray colors and local jump cancellation.

Global edge moves, frozen placement, Hanani–Tutte and the recognition criterion remain
open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Polygonal

private noncomputable def heightMap (a b : ℂ) : ℝ →ᵃ[ℝ] ℂ :=
  (AffineMap.lineMap a b).comp
    ((b.im - a.im)⁻¹ • (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ a.im))

private theorem heightMap_left (a b : ℂ) : heightMap a b a.im = a := by
  change AffineMap.lineMap a b ((b.im - a.im)⁻¹ * (a.im - a.im)) = a
  simp

private theorem heightMap_right {a b : ℂ} (hab : a.im ≠ b.im) :
    heightMap a b b.im = b := by
  change AffineMap.lineMap a b ((b.im - a.im)⁻¹ * (b.im - a.im)) = b
  rw [inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm), AffineMap.lineMap_apply_one]

private theorem heightMap_im {a b : ℂ} (hab : a.im ≠ b.im) (h : ℝ) :
    (heightMap a b h).im = h := by
  change (AffineMap.lineMap a b ((b.im - a.im)⁻¹ * (h - a.im))).im = h
  rw [lineMap_im]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

private theorem heightMap_re (a b : ℂ) (h : ℝ) :
    (heightMap a b h).re = horizontalIntercept a b h := by
  change Complex.reCLM.toLinearMap.toAffineMap
    (AffineMap.lineMap a b ((b.im - a.im)⁻¹ * (h - a.im))) = _
  rw [AffineMap.apply_lineMap]
  change AffineMap.lineMap a.re b.re ((b.im - a.im)⁻¹ * (h - a.im)) = _
  rw [AffineMap.lineMap_apply_ring']
  simp only [horizontalIntercept, div_eq_mul_inv]
  ring

private theorem mem_heightMap_image_iff {a b : ℂ} (hab : a.im ≠ b.im)
    (S : Set ℝ) (z : ℂ) :
    z ∈ heightMap a b '' S ↔ z.im ∈ S ∧ z.re = horizontalIntercept a b z.im := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    constructor
    · simpa only [heightMap_im hab] using hh
    · rw [heightMap_im hab, heightMap_re]
  · rintro ⟨hz, hre⟩
    refine ⟨z.im, hz, Complex.ext ?_ (heightMap_im hab _)⟩
    exact (heightMap_re a b z.im).trans hre.symm

private theorem mem_segment_height_iff {a b : ℂ} (hab : a.im < b.im) (z : ℂ) :
    z ∈ segment ℝ a b ↔
      z.im ∈ Set.Icc a.im b.im ∧ z.re = horizontalIntercept a b z.im := by
  have himage := image_segment ℝ (heightMap a b) a.im b.im
  rw [heightMap_left, heightMap_right hab.ne] at himage
  rw [← himage, mem_heightMap_image_iff hab.ne, segment_eq_Icc hab.le]

private theorem mem_openSegment_height_iff {a b : ℂ} (hab : a.im < b.im) (z : ℂ) :
    z ∈ openSegment ℝ a b ↔
      z.im ∈ Set.Ioo a.im b.im ∧ z.re = horizontalIntercept a b z.im := by
  have himage := image_openSegment ℝ (heightMap a b) a.im b.im
  rw [heightMap_left, heightMap_right hab.ne] at himage
  rw [← himage, mem_heightMap_image_iff hab.ne, openSegment_eq_Ioo hab]

-- The observation's height boundary is deliberately Ioc, opposite to RayCrosses' Ico.
private def Sweep (c d p : ℂ) : Prop :=
  (min c.im d.im < p.im ∧ p.im ≤ max c.im d.im) ∧
    horizontalIntercept c d p.im < p.re

private theorem sweep_reverse {c d : ℂ} (hcd : c.im ≠ d.im) (p : ℂ) :
    Sweep d c p ↔ Sweep c d p := by
  simp only [Sweep, min_comm d.im c.im, max_comm d.im c.im,
    horizontalIntercept_reverse hcd]

private theorem interval_boundary_parity (A B C D : ℝ) (hAB : A < B) (hCD : C < D)
    (f : ℝ → Bool) :
    (if A ≤ C ∧ C < B then f C else 0) +
        (if A ≤ D ∧ D < B then f D else 0) +
        (if C < A ∧ A ≤ D then f A else 0) +
        (if C < B ∧ B ≤ D then f B else 0) =
      if max A C < min B D then f (max A C) + f (min B D) else 0 := by
  rcases le_total A C with hAC | hCA
  · rcases le_total B D with hBD | hDB
    · rw [max_eq_right hAC, min_eq_left hBD]
      have hDA : ¬D < B := not_lt_of_ge hBD
      have hCA : ¬C < A := not_lt_of_ge hAC
      by_cases hCB : C < B
      · simp [hAC, hBD, hDA, hCA, hCB]
      · simp [hAC, hBD, hDA, hCA, hCB]
    · rw [max_eq_right hAC, min_eq_right hDB]
      have hCB : C < B := hCD.trans_le hDB
      have hAD : A ≤ D := hAC.trans hCD.le
      have hCA : ¬C < A := not_lt_of_ge hAC
      by_cases hDB' : D < B
      · simp [hAC, hAD, hCA, hCB, hCD, hDB', not_le.mpr hDB']
      · have heq : D = B := le_antisymm hDB (le_of_not_gt hDB')
        subst D
        simp [hAC, hCB, hCA]
  · rcases le_total B D with hBD | hDB
    · rw [max_eq_left hCA, min_eq_left hBD]
      have hCB : C < B := hCA.trans_lt hAB
      have hAD : A ≤ D := hAB.le.trans hBD
      have hDB : ¬D < B := not_lt_of_ge hBD
      by_cases hCA' : C < A
      · simp [hCA', not_le.mpr hCA', hCB, hAD, hBD, hDB, hAB]
      · have heq : C = A := le_antisymm hCA (le_of_not_gt hCA')
        subst C
        simp [hAB, hBD, hDB]
    · rw [max_eq_left hCA, min_eq_right hDB]
      rcases lt_trichotomy A D with hAD | hAD | hDA
      · have hCB : C < B := hCA.trans_lt hAB
        by_cases hCA' : C < A
        · by_cases hDB' : D < B
          · simp [hCA', not_le.mpr hCA', hDB', not_le.mpr hDB', hAD, hAD.le, add_comm]
          · have heq : D = B := le_antisymm hDB (le_of_not_gt hDB')
            subst D
            simp [hCA', not_le.mpr hCA', hAB, hAB.le, hCB]
        · have heq : C = A := le_antisymm hCA (le_of_not_gt hCA')
          subst C
          by_cases hDB' : D < B
          · simp [hDB', not_le.mpr hDB', hAB, hAD, hAD.le]
          · have heq : D = B := le_antisymm hDB (le_of_not_gt hDB')
            subst D
            simp [hAB]
      · subst D
        have hCA' : C < A := hCD
        simp [hCA', not_le.mpr hCA', hAB, not_le.mpr hAB, Bool.add_eq_xor, Bool.zero_eq_false]
      · have hAC : ¬A ≤ C := not_le.mpr (hCD.trans hDA)
        have hAD : ¬A ≤ D := not_le.mpr hDA
        have hBD : ¬B ≤ D := not_le.mpr (hDA.trans hAB)
        simp [hAC, hAD, hBD, not_lt.mpr hDA.le]

private noncomputable def differenceMap (a b c d : ℂ) : ℝ →ᵃ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.toAffineMap.comp (heightMap a b) -
    Complex.reCLM.toLinearMap.toAffineMap.comp (heightMap c d)

private theorem differenceMap_apply (a b c d : ℂ) (h : ℝ) :
    differenceMap a b c d h = horizontalIntercept a b h - horizontalIntercept c d h := by
  change (heightMap a b h).re - (heightMap c d h).re = _
  rw [heightMap_re, heightMap_re]

private theorem common_open_iff {a b c d : ℂ} (hab : a.im < b.im) (hcd : c.im < d.im) :
    (openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty ↔
      ∃ h ∈ Set.Ioo (max a.im c.im) (min b.im d.im), differenceMap a b c d h = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨haz, ha⟩ := (mem_openSegment_height_iff hab z).mp hz.1
    obtain ⟨hcz, hc⟩ := (mem_openSegment_height_iff hcd z).mp hz.2
    refine ⟨z.im, ⟨max_lt_iff.mpr ⟨haz.1, hcz.1⟩,
      lt_min_iff.mpr ⟨haz.2, hcz.2⟩⟩, ?_⟩
    rw [differenceMap_apply, sub_eq_zero]
    exact ha.symm.trans hc
  · rintro ⟨h, hh, hf⟩
    rw [differenceMap_apply, sub_eq_zero] at hf
    refine ⟨heightMap a b h, ?_, ?_⟩
    · rw [mem_openSegment_height_iff hab, heightMap_im hab.ne, heightMap_re]
      exact ⟨⟨(le_max_left _ _).trans_lt hh.1,
        hh.2.trans_le (min_le_left _ _)⟩, rfl⟩
    · rw [mem_openSegment_height_iff hcd, heightMap_im hab.ne, heightMap_re]
      exact ⟨⟨(le_max_right _ _).trans_lt hh.1,
        hh.2.trans_le (min_le_right _ _)⟩, hf⟩

private theorem difference_boundary_ne_zero {a b c d : ℂ}
    (hab : a.im < b.im) (hcd : c.im < d.im)
    (ha : a ∉ segment ℝ c d) (hb : b ∉ segment ℝ c d)
    (hc : c ∉ segment ℝ a b) (hd : d ∉ segment ℝ a b)
    {h : ℝ} (hAB : h ∈ Set.Icc a.im b.im) (hCD : h ∈ Set.Icc c.im d.im)
    (hend : h = a.im ∨ h = b.im ∨ h = c.im ∨ h = d.im) :
    differenceMap a b c d h ≠ 0 := by
  intro hz
  rw [differenceMap_apply, sub_eq_zero] at hz
  have heq : heightMap a b h = heightMap c d h := by
    apply Complex.ext
    · simpa only [heightMap_re] using hz
    · rw [heightMap_im hab.ne, heightMap_im hcd.ne]
  have hmAB : heightMap a b h ∈ segment ℝ a b := by
    rw [mem_segment_height_iff hab, heightMap_im hab.ne, heightMap_re]
    exact ⟨hAB, rfl⟩
  have hmCD : heightMap a b h ∈ segment ℝ c d := by
    rw [mem_segment_height_iff hcd, heightMap_im hab.ne, heightMap_re]
    exact ⟨hCD, hz⟩
  rcases hend with rfl | rfl | rfl | rfl
  · exact ha (by simpa only [heightMap_left] using hmCD)
  · exact hb (by simpa only [heightMap_right hab.ne] using hmCD)
  · rw [heq, heightMap_left] at hmAB
    exact hc hmAB
  · rw [heq, heightMap_right hcd.ne] at hmAB
    exact hd hmAB

open Classical in
private theorem common_open_indicator {a b c d : ℂ}
    (hab : a.im < b.im) (hcd : c.im < d.im)
    (ha : a ∉ segment ℝ c d) (hb : b ∉ segment ℝ c d)
    (hc : c ∉ segment ℝ a b) (hd : d ∉ segment ℝ a b) :
    decide ((openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty) =
      if max a.im c.im < min b.im d.im then
        decide (0 < differenceMap a b c d (max a.im c.im)) +
          decide (0 < differenceMap a b c d (min b.im d.im))
      else 0 := by
  classical
  let L := max a.im c.im
  let H := min b.im d.im
  by_cases hLH : L < H
  · have hL : differenceMap a b c d L ≠ 0 := by
      apply difference_boundary_ne_zero hab hcd ha hb hc hd
      · exact ⟨le_max_left _ _, (hLH.trans_le (min_le_left _ _)).le⟩
      · exact ⟨le_max_right _ _, (hLH.trans_le (min_le_right _ _)).le⟩
      · rcases le_total a.im c.im with h | h
        · exact Or.inr (Or.inr (Or.inl (max_eq_right h)))
        · exact Or.inl (max_eq_left h)
    have hH : differenceMap a b c d H ≠ 0 := by
      apply difference_boundary_ne_zero hab hcd ha hb hc hd
      · exact ⟨((le_max_left _ _).trans_lt hLH).le, min_le_left _ _⟩
      · exact ⟨((le_max_right _ _).trans_lt hLH).le, min_le_right _ _⟩
      · rcases le_total b.im d.im with h | h
        · exact Or.inr (Or.inl (min_eq_left h))
        · exact Or.inr (Or.inr (Or.inr (min_eq_right h)))
    have hroot : (∃ h ∈ Set.Ioo L H, differenceMap a b c d h = 0) ↔
        0 ∈ openSegment ℝ (differenceMap a b c d L) (differenceMap a b c d H) := by
      rw [← image_openSegment ℝ (differenceMap a b c d) L H]
      simp only [Set.mem_image, openSegment_eq_Ioo hLH]
    rw [common_open_iff hab hcd, hroot, Cslib.zero_mem_openSegment_iff_xor_pos hL hH,
      ite_eq_left hLH]
    by_cases hposL : 0 < differenceMap a b c d L <;>
      by_cases hposH : 0 < differenceMap a b c d H <;>
      simp [hposL, hposH, Xor, L, H, Bool.add_eq_xor]
  · have hno : ¬(openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty := by
      rintro hz
      obtain ⟨h, hh, _⟩ := (common_open_iff hab hcd).mp hz
      exact hLH (hh.1.trans hh.2)
    dsimp only [L, H] at hLH
    simp only [hno, decide_false, ite_eq_right hLH, Bool.zero_eq_false]

open Classical in
private theorem sweep_identity_ordered {a b c d : ℂ}
    (hab : a.im < b.im) (hcd : c.im < d.im)
    (ha : a ∉ segment ℝ c d) (hb : b ∉ segment ℝ c d)
    (hc : c ∉ segment ℝ a b) (hd : d ∉ segment ℝ a b) :
    decide (RayCrosses a b d) + decide (RayCrosses a b c) =
      decide ((openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty) +
        decide (Sweep c d a) + decide (Sweep c d b) := by
  classical
  let f : ℝ → Bool := fun h => decide (0 < differenceMap a b c d h)
  have hC : decide (RayCrosses a b c) =
      if a.im ≤ c.im ∧ c.im < b.im then f c.im else 0 := by
    have hsign : c.re < horizontalIntercept a b c.im ↔
        0 < differenceMap a b c d c.im := by
      rw [differenceMap_apply, horizontalIntercept_left, sub_pos]
    rw [show RayCrosses a b c ↔ (a.im ≤ c.im ∧ c.im < b.im) ∧
        0 < differenceMap a b c d c.im by
      simp only [RayCrosses, min_eq_left hab.le, max_eq_right hab.le, hsign, and_assoc]]
    by_cases h : a.im ≤ c.im ∧ c.im < b.im <;> simp [h, f, Bool.zero_eq_false]
  have hD : decide (RayCrosses a b d) =
      if a.im ≤ d.im ∧ d.im < b.im then f d.im else 0 := by
    have hsign : d.re < horizontalIntercept a b d.im ↔
        0 < differenceMap a b c d d.im := by
      rw [differenceMap_apply, horizontalIntercept_right hcd.ne, sub_pos]
    rw [show RayCrosses a b d ↔ (a.im ≤ d.im ∧ d.im < b.im) ∧
        0 < differenceMap a b c d d.im by
      simp only [RayCrosses, min_eq_left hab.le, max_eq_right hab.le, hsign, and_assoc]]
    by_cases h : a.im ≤ d.im ∧ d.im < b.im <;> simp [h, f, Bool.zero_eq_false]
  have hA : decide (Sweep c d a) =
      if c.im < a.im ∧ a.im ≤ d.im then f a.im else 0 := by
    have hsign : horizontalIntercept c d a.im < a.re ↔
        0 < differenceMap a b c d a.im := by
      rw [differenceMap_apply, horizontalIntercept_left, sub_pos]
    by_cases h : c.im < a.im ∧ a.im ≤ d.im <;>
      simp [Sweep, min_eq_left hcd.le, max_eq_right hcd.le, hsign, h, f, Bool.zero_eq_false]
  have hB : decide (Sweep c d b) =
      if c.im < b.im ∧ b.im ≤ d.im then f b.im else 0 := by
    have hsign : horizontalIntercept c d b.im < b.re ↔
        0 < differenceMap a b c d b.im := by
      rw [differenceMap_apply, horizontalIntercept_right hab.ne, sub_pos]
    by_cases h : c.im < b.im ∧ b.im ≤ d.im <;>
      simp [Sweep, min_eq_left hcd.le, max_eq_right hcd.le, hsign, h, f, Bool.zero_eq_false]
  have hboundary := interval_boundary_parity a.im b.im c.im d.im hab hcd f
  rw [← hC, ← hD, ← hA, ← hB,
    ← common_open_indicator hab hcd ha hb hc hd] at hboundary
  have h := congrArg (fun z : Bool => z + (decide (Sweep c d a) + decide (Sweep c d b)))
    hboundary
  simpa [add_assoc, add_comm, add_left_comm, BooleanRing.add_self] using h

open Classical in
private theorem sweep_identity {a b c d : ℂ}
    (hab : a.im ≠ b.im) (hcd : c.im ≠ d.im)
    (ha : a ∉ segment ℝ c d) (hb : b ∉ segment ℝ c d)
    (hc : c ∉ segment ℝ a b) (hd : d ∉ segment ℝ a b) :
    decide (RayCrosses a b d) + decide (RayCrosses a b c) =
      decide ((openSegment ℝ a b ∩ openSegment ℝ c d).Nonempty) +
        decide (Sweep c d a) + decide (Sweep c d b) := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · rcases lt_or_gt_of_ne hcd with hcd | hcd
    · exact sweep_identity_ordered hab hcd ha hb hc hd
    · have h := sweep_identity_ordered hab hcd
        (by simpa only [segment_symm] using ha) (by simpa only [segment_symm] using hb)
        hd hc
      simpa [openSegment_symm, sweep_reverse hcd.ne.symm, add_comm] using
        (show decide (RayCrosses a b c) + decide (RayCrosses a b d) = _ from h)
  · have h : decide (RayCrosses b a d) + decide (RayCrosses b a c) =
        decide ((openSegment ℝ b a ∩ openSegment ℝ c d).Nonempty) +
          decide (Sweep c d b) + decide (Sweep c d a) := by
      rcases lt_or_gt_of_ne hcd with hcd | hcd
      · exact sweep_identity_ordered hab hcd hb ha
          (by simpa only [segment_symm] using hc) (by simpa only [segment_symm] using hd)
      · have h := sweep_identity_ordered hab hcd
          (by simpa only [segment_symm] using hb) (by simpa only [segment_symm] using ha)
          (by simpa only [segment_symm] using hd) (by simpa only [segment_symm] using hc)
        simpa [openSegment_symm, sweep_reverse hcd.ne.symm, add_comm] using h
    simpa [rayCrosses_reverse, openSegment_symm, add_comm, add_left_comm, add_assoc] using h

open Classical in
private theorem weighted_sweeps_ordered {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) {c d : ℂ} (hcd : c.im < d.im)
    (hjump : ∀ z ∈ segment ℝ c d,
      (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
        decide ((b i).im = z.im ∧ z.re < (b i).re))) = 0) :
    (∑ i, x i * (decide (Sweep c d (a i)) + decide (Sweep c d (b i)))) = 0 := by
  classical
  let endpoint (j : ι × Bool) : ℂ := if j.2 then b j.1 else a j.1
  have hsum : (∑ j : ι × Bool, x j.1 * decide (Sweep c d (endpoint j))) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image fun j : ι × Bool => (endpoint j).im)
      (g := fun j => (endpoint j).im)
      (fun j _ => Finset.mem_image_of_mem _ (Finset.mem_univ j))]
    apply Finset.sum_eq_zero
    intro h _
    rw [Finset.sum_filter]
    by_cases hwindow : c.im < h ∧ h ≤ d.im
    · have hz : heightMap c d h ∈ segment ℝ c d := by
        rw [mem_segment_height_iff hcd, heightMap_im hcd.ne, heightMap_re]
        exact ⟨⟨hwindow.1.le, hwindow.2⟩, rfl⟩
      have hJ : (∑ j : ι × Bool, x j.1 *
          decide ((endpoint j).im = h ∧ (heightMap c d h).re < (endpoint j).re)) = 0 := by
        simpa only [Fintype.sum_prod_type, Fintype.sum_bool, endpoint,
          Bool.false_eq_true, ↓reduceIte, heightMap_im hcd.ne, ← mul_add, add_comm]
          using hjump (heightMap c d h) hz
      calc
        (∑ j : ι × Bool, if (endpoint j).im = h then
            x j.1 * decide (Sweep c d (endpoint j)) else 0) =
            ∑ j : ι × Bool, x j.1 *
              decide ((endpoint j).im = h ∧ (heightMap c d h).re < (endpoint j).re) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases heq : (endpoint j).im = h
          · simp [heq, Sweep, min_eq_left hcd.le, max_eq_right hcd.le,
              hwindow.1, hwindow.2, heightMap_re]
          · simp [heq, Bool.mul_eq_and, Bool.zero_eq_false]
        _ = 0 := hJ
    · apply Finset.sum_eq_zero
      intro j _
      by_cases heq : (endpoint j).im = h
      · simp [heq, Sweep, min_eq_left hcd.le, max_eq_right hcd.le, hwindow,
          Bool.mul_eq_and, Bool.zero_eq_false]
      · simp [heq, Bool.zero_eq_false]
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, endpoint,
    Bool.false_eq_true, ↓reduceIte, ← mul_add, add_comm] using hsum

open Classical in
private theorem weighted_sweeps_eq_zero {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) {c d : ℂ} (hcd : c.im ≠ d.im)
    (hjump : ∀ z ∈ segment ℝ c d,
      (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
        decide ((b i).im = z.im ∧ z.re < (b i).re))) = 0) :
    (∑ i, x i * (decide (Sweep c d (a i)) + decide (Sweep c d (b i)))) = 0 := by
  rcases lt_or_gt_of_ne hcd with hcd | hcd
  · exact weighted_sweeps_ordered a b x hcd hjump
  · have h := weighted_sweeps_ordered a b x hcd (fun z hz =>
        hjump z (by simpa only [segment_symm] using hz))
    simpa only [sweep_reverse hcd.ne.symm] using h

open Classical in
/-- Endpoint ray-parity difference equals the indexed Boolean sum of actual open
intersections with a straight observation segment when endpoint-height jumps cancel
throughout its closed support. Occurrences are counted separately, even at simultaneous
contacts or for duplicate geometric segments. No simplicity or no-triple premise is used.
No separate determinant or generic-position premise is needed. -/
theorem rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
    {ι : Type*} [Fintype ι] (a b : ι → ℂ) (x : ι → Bool) (c d : ℂ)
    (hheight : ∀ i, (a i).im ≠ (b i).im) (hcd : c.im ≠ d.im)
    (hc : ∀ i, x i = true → c ∉ segment ℝ (a i) (b i))
    (hd : ∀ i, x i = true → d ∉ segment ℝ (a i) (b i))
    (ha : ∀ i, x i = true → a i ∉ segment ℝ c d)
    (hb : ∀ i, x i = true → b i ∉ segment ℝ c d)
    (hjump : ∀ z ∈ segment ℝ c d,
      (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
        decide ((b i).im = z.im ∧ z.re < (b i).re))) = 0) :
    rayParity a b x d + rayParity a b x c =
      ∑ i, x i * decide ((openSegment ℝ (a i) (b i) ∩ openSegment ℝ c d).Nonempty) := by
  classical
  have hi (i : ι) : x i * (decide (RayCrosses (a i) (b i) d) +
        decide (RayCrosses (a i) (b i) c)) =
      x i * decide ((openSegment ℝ (a i) (b i) ∩ openSegment ℝ c d).Nonempty) +
        x i * (decide (Sweep c d (a i)) + decide (Sweep c d (b i))) := by
    by_cases hx : x i = true
    · rw [sweep_identity (hheight i) hcd (ha i hx) (hb i hx) (hc i hx) (hd i hx)]
      simp only [mul_add, add_assoc]
    · have hx' : x i = false := Bool.eq_false_iff.mpr hx
      simp [hx', Bool.mul_eq_and, Bool.zero_eq_false]
  calc
    rayParity a b x d + rayParity a b x c =
        ∑ i, x i * (decide (RayCrosses (a i) (b i) d) +
          decide (RayCrosses (a i) (b i) c)) := by
      rw [rayParity, rayParity, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hD : RayCrosses (a i) (b i) d <;>
        by_cases hC : RayCrosses (a i) (b i) c <;>
        simp [hD, hC, Bool.add_eq_xor, Bool.mul_eq_and, Bool.zero_eq_false]
    _ = (∑ i, x i * decide
        ((openSegment ℝ (a i) (b i) ∩ openSegment ℝ c d).Nonempty)) +
        ∑ i, x i * (decide (Sweep c d (a i)) + decide (Sweep c d (b i))) := by
      simp only [hi, Finset.sum_add_distrib]
    _ = _ := by rw [weighted_sweeps_eq_zero a b x hcd hjump, add_zero]

end Cslib.Polygonal
