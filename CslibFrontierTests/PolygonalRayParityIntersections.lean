/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary straight-observation parity clients)

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityIntersections
import CslibFrontier.Foundations.Geometry.SegmentSign
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Ordinary-import intersection-parity clients.
The configurations retain endpoint-height coincidences and indexed multiplicities.
-/

public section

namespace CslibFrontierTests.PolygonalRayParityIntersections

open Cslib Polygonal

example : (0 : ℝ) ∈ openSegment ℝ (-1) 1 := by
  rw [Cslib.zero_mem_openSegment_iff_xor_pos (by norm_num) (by norm_num)]
  norm_num [Xor]

example : (0 : ℝ) ∉ openSegment ℝ 1 1 := by
  rw [Cslib.zero_mem_openSegment_iff_xor_pos (by norm_num) (by norm_num)]
  norm_num [Xor]

open Classical in
/-- The ordinary vertical-segment example consumes the public intersection-parity law. -/
theorem vertical_law :
    rayParity (fun _ : Unit => (⟨0, -2⟩ : ℂ)) (fun _ => ⟨0, 2⟩) (fun _ => true) ⟨1, 1⟩ +
      rayParity (fun _ : Unit => (⟨0, -2⟩ : ℂ)) (fun _ => ⟨0, 2⟩) (fun _ => true) ⟨-1, -1⟩ =
      ∑ _ : Unit, true * decide ((openSegment ℝ (⟨0, -2⟩ : ℂ) ⟨0, 2⟩ ∩
        openSegment ℝ (⟨-1, -1⟩ : ℂ) ⟨1, 1⟩).Nonempty) := by
  apply rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
  · intro _
    norm_num
  · norm_num
  · intro _ _ hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u, _, hu⟩ := hz
    have hre := congrArg Complex.re hu
    norm_num [AffineMap.lineMap_apply_module'] at hre
  · intro _ _ hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u, _, hu⟩ := hz
    have hre := congrArg Complex.re hu
    norm_num [AffineMap.lineMap_apply_module'] at hre
  · intro _ _ hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u, hu, heq⟩ := hz
    have him := congrArg Complex.im heq
    norm_num [AffineMap.lineMap_apply_module'] at him
    linarith [hu.1]
  · intro _ _ hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u, hu, heq⟩ := hz
    have him := congrArg Complex.im heq
    norm_num [AffineMap.lineMap_apply_module'] at him
    linarith [hu.2]
  · intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hlow : (-2 : ℝ) ≠ -1 + u * 2 := by linarith [hu.1]
    have hhigh : (2 : ℝ) ≠ -1 + u * 2 := by linarith [hu.2]
    have him : (AffineMap.lineMap (⟨-1, -1⟩ : ℂ) ⟨1, 1⟩ u).im = -1 + u * 2 := by
      rw [lineMap_im]
      ring
    simp [him, hlow, hhigh, Bool.add_eq_xor, Bool.mul_eq_and, Bool.zero_eq_false]

-- A selected segment with odd endpoint incidence is admitted: jump cancellation is local.
example : ¬(∀ z : ℂ, (∑ _ : Unit,
      ((if (⟨0, -2⟩ : ℂ) = z then true else 0) +
        (if (⟨0, 2⟩ : ℂ) = z then true else 0))) = false) ∧
    (openSegment ℝ (⟨0, -2⟩ : ℂ) ⟨0, 2⟩ ∩
      openSegment ℝ (⟨-1, -1⟩ : ℂ) ⟨1, 1⟩).Nonempty := by
  classical
  constructor
  · intro h
    have hz := h ⟨0, -2⟩
    norm_num at hz
  · have h := vertical_law
    norm_num [rayParity, RayCrosses, horizontalIntercept, Bool.mul_eq_and] at h
    exact h

-- Each orientation reversal preserves the actual indexed event equation.
open Classical in
example :
    rayParity (fun _ : Unit => (⟨0, 2⟩ : ℂ)) (fun _ => ⟨0, -2⟩) (fun _ => true) ⟨1, 1⟩ +
      rayParity (fun _ : Unit => (⟨0, 2⟩ : ℂ)) (fun _ => ⟨0, -2⟩) (fun _ => true) ⟨-1, -1⟩ =
      ∑ _ : Unit, true * decide ((openSegment ℝ (⟨0, 2⟩ : ℂ) ⟨0, -2⟩ ∩
        openSegment ℝ (⟨-1, -1⟩ : ℂ) ⟨1, 1⟩).Nonempty) := by
  simpa only [rayParity, rayCrosses_reverse, openSegment_symm] using vertical_law

open Classical in
example :
    rayParity (fun _ : Unit => (⟨0, -2⟩ : ℂ)) (fun _ => ⟨0, 2⟩) (fun _ => true) ⟨-1, -1⟩ +
      rayParity (fun _ : Unit => (⟨0, -2⟩ : ℂ)) (fun _ => ⟨0, 2⟩) (fun _ => true) ⟨1, 1⟩ =
      ∑ _ : Unit, true * decide ((openSegment ℝ (⟨0, -2⟩ : ℂ) ⟨0, 2⟩ ∩
        openSegment ℝ (⟨1, 1⟩ : ℂ) ⟨-1, -1⟩).Nonempty) := by
  simpa [openSegment_symm, add_comm] using vertical_law

open Classical in
private theorem symmetric_events {ι : Type*} [Fintype ι] (k : ι → ℝ)
    (hk : ∀ i, 2 ≤ k i) (x : ι → Bool) :
    (∑ i, x i * decide ((openSegment ℝ (⟨-1, -k i⟩ : ℂ) ⟨1, k i⟩ ∩
      openSegment ℝ (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩).Nonempty)) =
      ∑ i, x i := by
  classical
  have h := rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
    (fun i => (⟨-1, -k i⟩ : ℂ)) (fun i => ⟨1, k i⟩) x
    ⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ ⟨1 / 2, 1 / 2⟩
    (by intro i; have := hk i; norm_num; linarith) (by norm_num)
    (by
      intro i _ hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨u, _, heq⟩ := hz
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      norm_num [AffineMap.lineMap_apply_module'] at hre him
      have := hk i
      nlinarith)
    (by
      intro i _ hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨u, _, heq⟩ := hz
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      norm_num [AffineMap.lineMap_apply_module'] at hre him
      have := hk i
      nlinarith)
    (by
      intro i _ hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨u, hu, heq⟩ := hz
      have hre := congrArg Complex.re heq
      norm_num [AffineMap.lineMap_apply_module'] at hre
      linarith [hu.1])
    (by
      intro i _ hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨u, hu, heq⟩ := hz
      have hre := congrArg Complex.re heq
      norm_num [AffineMap.lineMap_apply_module'] at hre
      linarith [hu.2])
    (by
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      apply Finset.sum_eq_zero
      intro i _
      have hlo : -k i ≠ -(1 / 2 : ℝ) + u := by linarith [hk i, hu.1]
      have hhi : k i ≠ -(1 / 2 : ℝ) + u := by linarith [hk i, hu.2]
      have him : (AffineMap.lineMap (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ)
          ⟨1 / 2, 1 / 2⟩ u).im = -(1 / 2 : ℝ) + u := by
        rw [lineMap_im]
        ring
      rw [him]
      simp only [hlo, hhi, false_and, decide_false, Bool.add_eq_xor, Bool.xor_false,
      Bool.mul_eq_and, Bool.and_false, Bool.zero_eq_false])
  have hleft (i : ι) : RayCrosses (⟨-1, -k i⟩ : ℂ) ⟨1, k i⟩
      ⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ := by
    have hden : 0 < k i - -k i := by linarith [hk i]
    simp only [RayCrosses, horizontalIntercept]
    norm_num only [show (1 : ℝ) - -1 = 2 by norm_num]
    change min (-k i) (k i) ≤ -(1 / 2 : ℝ) ∧
      -(1 / 2 : ℝ) < max (-k i) (k i) ∧
      -(1 / 2 : ℝ) < -1 + (-(1 / 2 : ℝ) - -k i) / (k i - -k i) * 2
    rw [min_eq_left (by linarith : -k i ≤ k i),
      max_eq_right (by linarith : -k i ≤ k i)]
    refine ⟨by linarith [hk i], by linarith [hk i], ?_⟩
    have hq : (1 / 4 : ℝ) < (-(1 / 2 : ℝ) - -k i) / (k i - -k i) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith [hk i]
    linarith
  have hright (i : ι) : ¬RayCrosses (⟨-1, -k i⟩ : ℂ) ⟨1, k i⟩
      ⟨1 / 2, 1 / 2⟩ := by
    intro hi
    have hx := hi.2.2
    change (1 / 2 : ℝ) < -1 + (1 / 2 - -k i) / (k i - -k i) * (1 - -1) at hx
    rw [sub_neg_eq_add, show (1 : ℝ) - -1 = 2 by norm_num] at hx
    have hden : 0 < k i - -k i := by linarith [hk i]
    have hq : (3 / 4 : ℝ) < (1 / 2 + k i) / (k i - -k i) := by linarith
    have hm := (lt_div_iff₀ hden).mp hq
    nlinarith [hk i]
  simpa only [rayParity, hleft, hright, ↓reduceIte, Finset.sum_const_zero, zero_add,
      Bool.mul_eq_and, Bool.and_true] using h.symm

-- Three indexed segments meet at one point: no no3 hypothesis may be smuggled in.
open Classical in
example : (∑ i : Fin 3, true * decide
    ((openSegment ℝ (⟨-1, -((i.val : ℝ) + 2)⟩ : ℂ) ⟨1, (i.val : ℝ) + 2⟩ ∩
      openSegment ℝ (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩).Nonempty)) = true := by
  have h := symmetric_events (fun i : Fin 3 => (i.val : ℝ) + 2)
    (fun i => by have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _; linarith) (fun _ => true)
  exact h.trans (by decide)

-- Geometrically identical segments are separate occurrences and cancel.
open Classical in
example : (∑ _ : Fin 2, true * decide
    ((openSegment ℝ (⟨-1, -2⟩ : ℂ) ⟨1, 2⟩ ∩
      openSegment ℝ (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩).Nonempty)) = false := by
  have h := symmetric_events (fun _ : Fin 2 => (2 : ℝ)) (by intro _; norm_num) (fun _ => true)
  exact h.trans (by decide)

open Classical in
example : (∑ _i : Fin 0, true * decide
    ((openSegment ℝ (⟨-1, -(2 : ℝ)⟩ : ℂ) ⟨1, 2⟩ ∩
      openSegment ℝ (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩).Nonempty)) = false := by
  have h := symmetric_events (fun _ : Fin 0 => (2 : ℝ)) (by intro _; norm_num) (fun _ => true)
  exact h.trans (by decide)

-- The common point in the three-event fixture really is the origin.
private theorem symmetric_origin_mem (k : ℝ) :
    (0 : ℂ) ∈ openSegment ℝ (⟨-1, -k⟩ : ℂ) ⟨1, k⟩ := by
  have himage := image_openSegment ℝ
    (AffineMap.lineMap (⟨-1, -k⟩ : ℂ) ⟨1, k⟩) (0 : ℝ) 1
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at himage
  rw [← himage]
  refine ⟨(1 / 2 : ℝ), ?_, ?_⟩
  · norm_num [openSegment_eq_Ioo]
  · apply Complex.ext <;> simp [AffineMap.lineMap_apply_module']
    <;> ring

-- Without jump cancellation parity changes despite no geometric intersection.
example : rayParity (fun _ : Unit => (⟨0, 0⟩ : ℂ)) (fun _ => ⟨2, 2⟩)
      (fun _ => true) ⟨-1, 1⟩ +
    rayParity (fun _ : Unit => (⟨0, 0⟩ : ℂ)) (fun _ => ⟨2, 2⟩)
      (fun _ => true) ⟨-1, -1⟩ = true := by
  norm_num [rayParity, RayCrosses, horizontalIntercept]

example : ¬(segment ℝ (⟨0, 0⟩ : ℂ) ⟨2, 2⟩ ∩
    segment ℝ (⟨-1, -1⟩ : ℂ) ⟨-1, 1⟩).Nonempty := by
  rintro ⟨z, hz⟩
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, hsx⟩ := hz.1
  obtain ⟨t, _, htx⟩ := hz.2
  have hre := congrArg Complex.re (hsx.trans htx.symm)
  norm_num [AffineMap.lineMap_apply_module'] at hre
  linarith [hs.1]

open Classical in
example : (∑ _ : Unit, true *
    (decide ((0 : ℝ) = 0 ∧ (-1 : ℝ) < 0) + decide ((2 : ℝ) = 0 ∧ (-1 : ℝ) < 2))) ≠ 0 := by
  norm_num [Bool.mul_eq_and, Bool.add_eq_xor, Bool.zero_eq_false]

-- Starting on a selected support violates the CLOSED endpoint exclusion.
example : (0 : ℂ) ∈ segment ℝ (⟨0, -2⟩ : ℂ) ⟨0, 2⟩ := by
  rw [segment_eq_image_lineMap]
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module']

-- A star center on the observation is an arrangement ENDPOINT, not a transverse event.
example : (0 : ℂ) ∈ segment ℝ (⟨0, -1⟩ : ℂ) ⟨0, 2⟩ ∧
    (0 : ℂ) ∈ segment ℝ 0 (⟨-1, 1⟩ : ℂ) ∧
    (0 : ℂ) ∈ segment ℝ 0 (⟨1, 1⟩ : ℂ) := by
  refine ⟨?_, left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  rw [segment_eq_image_lineMap]
  refine ⟨(1 / 3 : ℝ), by norm_num, ?_⟩
  apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module']

-- Collinear overlap violates the endpoint exclusions; it is not a valid observation.
example :
    ((⟨0, 2⟩ : ℂ) - ⟨0, -2⟩).re * ((⟨0, 1⟩ : ℂ) - ⟨0, -1⟩).im -
      ((⟨0, 2⟩ : ℂ) - ⟨0, -2⟩).im * ((⟨0, 1⟩ : ℂ) - ⟨0, -1⟩).re = 0 := by
  norm_num

private theorem cycle_even {n : ℕ} (v : Fin n → ℂ) (p : ℂ) :
    (∑ i : Fin n, ((if v i = p then (true : Bool) else 0) +
      (if v (finRotate n i) = p then true else 0))) = false := by
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp (finRotate n) (fun i => if v i = p then (true : Bool) else 0)]
  simpa only [Bool.zero_eq_false] using BooleanRing.add_self (∑ i,
      if v i = p then (true : Bool) else 0)

private def diamond (i : Fin 4) : ℂ :=
  if i = 0 then ⟨0, 2⟩ else if i = 1 then ⟨2, 0⟩ else
    if i = 2 then ⟨0, -2⟩ else ⟨-2, 0⟩

private noncomputable def diamondStart (once : Bool) : ℂ :=
  if once then 0 else ⟨-3, -(1 / 2 : ℝ)⟩

private theorem diamond_observation_avoids (once endpoint : Bool) (i : Fin 4) :
    (if endpoint then diamondStart once else (⟨3, 1 / 2⟩ : ℂ)) ∉
      segment ℝ (diamond i) (diamond (finRotate 4 i)) := by
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, hu, heq⟩ := hz
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases once <;> cases endpoint <;> fin_cases i <;>
    norm_num [diamondStart, diamond, finRotate_apply,
      AffineMap.lineMap_apply_module'] at hre him <;>
    linarith [hu.1, hu.2]

private theorem diamond_endpoints_avoid (once endpoint : Bool) (i : Fin 4) :
    (if endpoint then diamond i else diamond (finRotate 4 i)) ∉
      segment ℝ (diamondStart once) (⟨3, 1 / 2⟩ : ℂ) := by
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, _, heq⟩ := hz
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases once <;> cases endpoint <;> fin_cases i <;>
    norm_num [diamondStart, diamond, finRotate_apply,
      AffineMap.lineMap_apply_module'] at hre him <;>
    linarith

open Classical in
private theorem diamond_law (once : Bool) :
    rayParity diamond (fun i => diamond (finRotate 4 i)) (fun _ => true) ⟨3, 1 / 2⟩ +
      rayParity diamond (fun i => diamond (finRotate 4 i)) (fun _ => true) (diamondStart once) =
      ∑ i : Fin 4, true * decide
        ((openSegment ℝ (diamond i) (diamond (finRotate 4 i)) ∩
          openSegment ℝ (diamondStart once) (⟨3, 1 / 2⟩ : ℂ)).Nonempty) := by
  apply rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
  · intro i
    fin_cases i <;> norm_num [diamond, finRotate_apply]
  · cases once <;> norm_num [diamondStart]
  · exact fun i _ => diamond_observation_avoids once true i
  · exact fun i _ => diamond_observation_avoids once false i
  · exact fun i _ => diamond_endpoints_avoid once true i
  · exact fun i _ => diamond_endpoints_avoid once false i
  · intro z _
    exact sum_rayParity_endpoint_jumps_eq_zero diamond (fun i => diamond (finRotate 4 i))
      (fun _ => true) (cycle_even diamond) z

-- The first observation begins inside; the second passes through the whole even cycle.
open Classical in
example : (∑ i : Fin 4, true * decide
    ((openSegment ℝ (diamond i) (diamond (finRotate 4 i)) ∩
      openSegment ℝ 0 (⟨3, 1 / 2⟩ : ℂ)).Nonempty)) = true := by
  have hcolors : rayParity diamond (fun i => diamond (finRotate 4 i)) (fun _ => true)
      ⟨3, 1 / 2⟩ + rayParity diamond (fun i => diamond (finRotate 4 i))
      (fun _ => true) (diamondStart true) = true := by
    norm_num [rayParity, Fin.sum_univ_succ, diamondStart, diamond, finRotate_apply,
      RayCrosses, horizontalIntercept, Bool.add_eq_xor, Bool.zero_eq_false]
  exact (diamond_law true).symm.trans hcolors

open Classical in
example : (∑ i : Fin 4, true * decide
    ((openSegment ℝ (diamond i) (diamond (finRotate 4 i)) ∩
      openSegment ℝ (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩).Nonempty)) = false := by
  have hcolors : rayParity diamond (fun i => diamond (finRotate 4 i)) (fun _ => true)
      ⟨3, 1 / 2⟩ + rayParity diamond (fun i => diamond (finRotate 4 i))
      (fun _ => true) (diamondStart false) = false := by
    norm_num [rayParity, Fin.sum_univ_succ, diamondStart, diamond, finRotate_apply,
      RayCrosses, horizontalIntercept, Bool.add_eq_xor, Bool.zero_eq_false]
  exact (diamond_law false).symm.trans hcolors

-- Two distinct actual events justify the description "twice", independently of parity.
example :
    (openSegment ℝ (diamond 0) (diamond 1) ∩
      openSegment ℝ (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩).Nonempty ∧
    (openSegment ℝ (diamond 2) (diamond 3) ∩
      openSegment ℝ (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩).Nonempty := by
  have hfirst : (⟨12 / 7, 2 / 7⟩ : ℂ) ∈ openSegment ℝ (diamond 0) (diamond 1) := by
    have h := image_openSegment ℝ (AffineMap.lineMap (diamond 0) (diamond 1)) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    exact ⟨6 / 7, by norm_num [openSegment_eq_Ioo], by apply Complex.ext <;> norm_num [diamond,
      AffineMap.lineMap_apply_module']⟩
  have hsecond : (⟨-12 / 7, -2 / 7⟩ : ℂ) ∈ openSegment ℝ (diamond 2) (diamond 3) := by
    have h := image_openSegment ℝ (AffineMap.lineMap (diamond 2) (diamond 3)) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    exact ⟨6 / 7, by norm_num [openSegment_eq_Ioo], by apply Complex.ext <;> norm_num [diamond,
      AffineMap.lineMap_apply_module']⟩
  have hobs (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
      AffineMap.lineMap (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩ v ∈
        openSegment ℝ (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩ := by
    have h := image_openSegment ℝ
      (AffineMap.lineMap (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    exact ⟨v, by simpa only [openSegment_eq_Ioo (by norm_num : (0 : ℝ) < 1)] using hv, rfl⟩
  refine ⟨⟨⟨12 / 7, 2 / 7⟩, hfirst, ?_⟩, ⟨⟨-12 / 7, -2 / 7⟩, hsecond, ?_⟩⟩
  · have heq : AffineMap.lineMap (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩ (11 / 14 : ℝ) =
        (⟨12 / 7, 2 / 7⟩ : ℂ) := by
      apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module']
    simpa only [heq] using hobs (11 / 14) (by norm_num)
  · have heq : AffineMap.lineMap (⟨-3, -(1 / 2 : ℝ)⟩ : ℂ) ⟨3, 1 / 2⟩ (3 / 14 : ℝ) =
        (⟨-12 / 7, -2 / 7⟩ : ℂ) := by
      apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module']
    simpa only [heq] using hobs (3 / 14) (by norm_num)

private def boundaryTriangle (i : Fin 3) : ℂ :=
  if i = 0 then ⟨-3, -5⟩ else if i = 1 then ⟨1, 5⟩ else ⟨4, -6⟩

private def boundaryC : ℂ := ⟨-1, 5⟩
private def boundaryD : ℂ := ⟨4, 1⟩

private theorem boundary_observation_avoids (endpoint : Bool) (i : Fin 3) :
    (if endpoint then boundaryC else boundaryD) ∉
      segment ℝ (boundaryTriangle i) (boundaryTriangle (finRotate 3 i)) := by
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, _, heq⟩ := hz
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases endpoint <;> fin_cases i <;>
    norm_num [boundaryTriangle, boundaryC, boundaryD, finRotate_apply,
      AffineMap.lineMap_apply_module'] at hre him <;> linarith

private theorem boundary_endpoints_avoid (endpoint : Bool) (i : Fin 3) :
    (if endpoint then boundaryTriangle i else boundaryTriangle (finRotate 3 i)) ∉
      segment ℝ boundaryC boundaryD := by
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, hu, heq⟩ := hz
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  cases endpoint <;> fin_cases i <;>
    norm_num [boundaryTriangle, boundaryC, boundaryD, finRotate_apply,
      AffineMap.lineMap_apply_module'] at hre him <;> linarith [hu.1, hu.2]

-- A genuine closed arrangement admits the coincident UPPER endpoint height.
open Classical in
private theorem boundary_law :
    rayParity boundaryTriangle (fun i => boundaryTriangle (finRotate 3 i))
        (fun _ => true) boundaryD +
      rayParity boundaryTriangle (fun i => boundaryTriangle (finRotate 3 i))
        (fun _ => true) boundaryC =
      ∑ i : Fin 3, true * decide
        ((openSegment ℝ (boundaryTriangle i) (boundaryTriangle (finRotate 3 i)) ∩
          openSegment ℝ boundaryC boundaryD).Nonempty) := by
  apply rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
  · intro i
    fin_cases i <;> norm_num [boundaryTriangle, finRotate_apply]
  · norm_num [boundaryC, boundaryD]
  · exact fun i _ => boundary_observation_avoids true i
  · exact fun i _ => boundary_observation_avoids false i
  · exact fun i _ => boundary_endpoints_avoid true i
  · exact fun i _ => boundary_endpoints_avoid false i
  · intro z _
    exact sum_rayParity_endpoint_jumps_eq_zero boundaryTriangle
      (fun i => boundaryTriangle (finRotate 3 i)) (fun _ => true)
      (cycle_even boundaryTriangle) z

open Classical in
example : (∑ i : Fin 3, true * decide
    ((openSegment ℝ (boundaryTriangle i) (boundaryTriangle (finRotate 3 i)) ∩
      openSegment ℝ boundaryC boundaryD).Nonempty)) = false := by
  have hcolors : rayParity boundaryTriangle (fun i => boundaryTriangle (finRotate 3 i))
      (fun _ => true) boundaryD +
      rayParity boundaryTriangle (fun i => boundaryTriangle (finRotate 3 i))
        (fun _ => true) boundaryC = false := by
    norm_num [rayParity, Fin.sum_univ_succ, boundaryTriangle, boundaryC, boundaryD,
      finRotate_apply, RayCrosses, horizontalIntercept, Bool.add_eq_xor, Bool.zero_eq_false]
    rfl
  exact boundary_law.symm.trans hcolors

open Classical in
example : (boundaryTriangle 1).im = max boundaryC.im boundaryD.im ∧
    (∑ i : Fin 3, true *
      (decide ((boundaryTriangle i).im = boundaryC.im ∧ boundaryC.re < (boundaryTriangle i).re) +
        decide ((boundaryTriangle (finRotate 3 i)).im = boundaryC.im ∧
          boundaryC.re < (boundaryTriangle (finRotate 3 i)).re))) = 0 := by
  constructor
  · norm_num [boundaryTriangle, boundaryC, boundaryD]
  · exact sum_rayParity_endpoint_jumps_eq_zero boundaryTriangle
      (fun i => boundaryTriangle (finRotate 3 i)) (fun _ => true)
      (cycle_even boundaryTriangle) boundaryC

private theorem boundary_first_contact :
    (openSegment ℝ (boundaryTriangle 0) (boundaryTriangle 1) ∩
      openSegment ℝ boundaryC boundaryD).Nonempty := by
  refine ⟨⟨17 / 33, 125 / 33⟩, ?_, ?_⟩
  · have h := image_openSegment ℝ
      (AffineMap.lineMap (boundaryTriangle 0) (boundaryTriangle 1)) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    exact ⟨29 / 33, by norm_num [openSegment_eq_Ioo], by
      apply Complex.ext <;> norm_num [boundaryTriangle, AffineMap.lineMap_apply_module']⟩
  · have h := image_openSegment ℝ (AffineMap.lineMap boundaryC boundaryD) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    exact ⟨10 / 33, by norm_num [openSegment_eq_Ioo], by
      apply Complex.ext <;> norm_num [boundaryC, boundaryD, AffineMap.lineMap_apply_module']⟩

-- Replacing the sweep's Ioc by Ico gives a FALSE per-segment identity here.
open Classical in
example : decide (RayCrosses (boundaryTriangle 0) (boundaryTriangle 1) boundaryD) +
      decide (RayCrosses (boundaryTriangle 0) (boundaryTriangle 1) boundaryC) ≠
    decide ((openSegment ℝ (boundaryTriangle 0) (boundaryTriangle 1) ∩
      openSegment ℝ boundaryC boundaryD).Nonempty) +
    decide (min boundaryC.im boundaryD.im ≤ (boundaryTriangle 0).im ∧
      (boundaryTriangle 0).im < max boundaryC.im boundaryD.im ∧
      horizontalIntercept boundaryC boundaryD (boundaryTriangle 0).im < (boundaryTriangle 0).re) +
    decide (min boundaryC.im boundaryD.im ≤ (boundaryTriangle 1).im ∧
      (boundaryTriangle 1).im < max boundaryC.im boundaryD.im ∧
      horizontalIntercept boundaryC boundaryD (boundaryTriangle 1).im <
        (boundaryTriangle 1).re) := by
  have hevent : decide ((openSegment ℝ (boundaryTriangle 0) (boundaryTriangle 1) ∩
      openSegment ℝ boundaryC boundaryD).Nonempty) = true := by
    exact decide_eq_true boundary_first_contact
  rw [hevent]
  norm_num [boundaryTriangle, boundaryC, boundaryD, RayCrosses, horizontalIntercept]

example (i : Fin 3) : (0 : ℂ) ∈
    openSegment ℝ (⟨-1, -((i.val : ℝ) + 2)⟩ : ℂ) ⟨1, (i.val : ℝ) + 2⟩ ∩
      openSegment ℝ (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩ := by
  refine ⟨symmetric_origin_mem _, ?_⟩
  have h := image_openSegment ℝ
    (AffineMap.lineMap (⟨-(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩ : ℂ) ⟨1 / 2, 1 / 2⟩) (0 : ℝ) 1
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
  rw [← h]
  exact ⟨1 / 2, by norm_num [openSegment_eq_Ioo], by
    apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module']⟩

example : (openSegment ℝ (⟨0, -2⟩ : ℂ) ⟨0, 2⟩ ∩
    openSegment ℝ (⟨0, -1⟩ : ℂ) ⟨0, 1⟩).Nonempty := by
  have hzero (r : ℝ) : (0 : ℂ) ∈ openSegment ℝ (⟨0, -r⟩ : ℂ) ⟨0, r⟩ := by
    have h := image_openSegment ℝ (AffineMap.lineMap (⟨0, -r⟩ : ℂ) ⟨0, r⟩) (0 : ℝ) 1
    rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
    rw [← h]
    refine ⟨1 / 2, by norm_num [openSegment_eq_Ioo], ?_⟩
    apply Complex.ext <;> simp [AffineMap.lineMap_apply_module']
    ring
  exact ⟨0, hzero 2, hzero 1⟩

end CslibFrontierTests.PolygonalRayParityIntersections
