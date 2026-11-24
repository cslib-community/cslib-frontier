/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary straight-observation parity clients)

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityIntersections
import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Foundations.Geometry.SegmentSign
import Mathlib.Analysis.Convex.PathConnected
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

private def excursionStem : Route := Route.line ⟨4, 2⟩ 0

private def excursionSquare : Route where
  bends := 3
  point i := if i.val = 1 then ⟨2, 0⟩ else if i.val = 2 then ⟨2, 2⟩ else
    if i.val = 3 then ⟨0, 2⟩ else 0

-- The connector contributes at the interior observation, but its retracing cancels it.
example :
    let p := (excursionStem.concat excursionSquare).concat excursionStem.reverse
    excursionStem.rayParity 1 ⟨1, 1⟩ = true ∧
      p.rayParity 1 ⟨1, 1⟩ = true ∧ p.rayParity 1 ⟨3, 1⟩ = false := by
  classical
  dsimp only
  simp only [Route.rayParity_closed_excursion excursionStem excursionSquare rfl rfl]
  let bit (a b z : ℂ) : Bool := if RayCrosses a b z then true else 0
  have stemBit (z : ℂ) : excursionStem.rayParity 1 z = bit ⟨4, 2⟩ 0 z := by
    unfold Route.rayParity rayParity
    change (∑ i : Fin 1, if RayCrosses (1 * excursionStem.point i.castSucc)
      (1 * excursionStem.point i.succ) (1 * z) then (true : Bool) else 0) = _
    simp only [Fin.sum_univ_one, one_mul]
    rfl
  have squareBits (z : ℂ) : excursionSquare.rayParity 1 z =
      bit 0 ⟨2, 0⟩ z + bit ⟨2, 0⟩ ⟨2, 2⟩ z + bit ⟨2, 2⟩ ⟨0, 2⟩ z + bit ⟨0, 2⟩ 0 z := by
    unfold Route.rayParity rayParity
    change (∑ i : Fin 4, if RayCrosses (1 * excursionSquare.point i.castSucc)
      (1 * excursionSquare.point i.succ) (1 * z) then (true : Bool) else 0) = _
    simp only [Fin.sum_univ_four, one_mul]
    rfl
  norm_num [stemBit, squareBits, bit, RayCrosses, horizontalIntercept]
  exact Bool.zero_eq_false

-- Distinct observations can have the same height and lie on opposite sides.
example :
    ∃ p : Route, p.finish = p.start ∧ p.rayParity 1 ⟨2, 3⟩ = true ∧
      p.rayParity 1 ⟨1, 3⟩ = false ∧ p.rayParity 1 ⟨3, 3⟩ = false := by
  classical
  let points : Finset ℂ := {⟨1, 3⟩, ⟨2, 3⟩, ⟨3, 3⟩}
  obtain ⟨p, -, hclosed, -, -, -, -, hcenter, houtside⟩ :=
    Route.exists_rayParity_isolating_loop points ⟨2, 3⟩ (ε := 1) (by norm_num)
  refine ⟨p, hclosed, hcenter, houtside _ (by simp [points]) ?_,
    houtside _ (by simp [points]) ?_⟩
  all_goals
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre

-- A closed excursion based away from the observations gives the specified parity
-- and avoids all three marked points, including the one whose bit it flips.
example :
    ∃ p : Route, p.start = 0 ∧ p.finish = 0 ∧
      (⟨2, 3⟩ : ℂ) ∉ p.support ∧ (⟨1, 3⟩ : ℂ) ∉ p.support ∧
      (⟨3, 3⟩ : ℂ) ∉ p.support ∧
      p.rayParity 1 ⟨2, 3⟩ = true ∧ p.rayParity 1 ⟨1, 3⟩ = false ∧
      p.rayParity 1 ⟨3, 3⟩ = false := by
  classical
  let points : Finset ℂ := {⟨1, 3⟩, ⟨3, 3⟩}
  have hne₀ : ∀ z ∈ points, (0 : ℂ) ≠ z := by
    intro z hz heq
    have hre := congrArg Complex.im heq
    simp only [points, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> norm_num at hre
  have ha : (0 : ℂ) ∉ points := fun h => hne₀ _ h rfl
  have hac : (0 : ℂ) ≠ ⟨2, 3⟩ := by
    intro h
    have hre := congrArg Complex.im h
    norm_num at hre
  have hconn : IsPathConnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isPathConnected ⟨0, Set.mem_univ 0⟩
  obtain ⟨p, hstart, hfinish, hs, hodd, heven⟩ :=
    Route.exists_rayParity_isolating_excursion isOpen_univ hconn points
      (Set.mem_univ 0) (Set.mem_univ ⟨2, 3⟩) ha hac
  have avoids (z : ℂ) (hz : z ∈ insert ⟨2, 3⟩ points) : z ∉ p.support :=
    fun h => (hs h).2 hz
  refine ⟨p, hstart, hfinish, avoids _ (by simp), avoids _ (by simp [points]),
    avoids _ (by simp [points]), hodd, heven _ (by simp [points]) ?_,
    heven _ (by simp [points]) ?_⟩
  all_goals
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre

-- Two points have odd parity, while the third marked point has even parity.
example : ∃ p : Route, p.start = 0 ∧ p.finish = 0 ∧
    p.rayParity 1 ⟨1, 1⟩ = true ∧ p.rayParity 1 ⟨3, 1⟩ = true ∧
    p.rayParity 1 ⟨2, 1⟩ = false := by
  classical
  let odd : Finset ℂ := {⟨1, 1⟩, ⟨3, 1⟩}
  let points : Finset ℂ := insert ⟨2, 1⟩ odd
  have ha : (0 : ℂ) ∉ points := by
    intro hz
    simp only [points, odd, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> have hi := congrArg Complex.im h <;> norm_num at hi
  have hconn : IsPathConnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isPathConnected ⟨0, Set.mem_univ 0⟩
  have hsub : odd ⊆ points := fun _ hz => Finset.mem_insert_of_mem hz
  obtain ⟨p, hs, hf, -, hparity⟩ :=
    Route.exists_rayParity_excursion_of_subset isOpen_univ hconn points odd hsub
      (fun z _ => Set.mem_univ z) (Set.mem_univ 0) ha
  have heven : (⟨2, 1⟩ : ℂ) ∉ odd := by
    intro hz
    simp only [odd, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h <;> have hr := congrArg Complex.re h <;> norm_num at hr
  refine ⟨p, hs, hf, ?_, ?_, ?_⟩
  · rw [hparity _ (hsub (by simp [odd]))]
    simp [odd]
  · rw [hparity _ (hsub (by simp [odd]))]
    simp [odd]
  · rw [hparity _ (by simp [points])]
    exact decide_eq_false heven

-- Rotated coordinates preserve the endpoint germs and realize the marked bit.
example :
    let p := Route.line 0 ⟨0, 1⟩
    let q := Route.line ⟨0, 1⟩ ⟨0, 2⟩
    ∃ r : Route, (∀ b, r.germ b = (p.concat q).germ b) ∧
      r.rayParity ⟨1, 1⟩ ⟨1, 1⟩ = (p.concat q).rayParity ⟨1, 1⟩ ⟨1, 1⟩ + true := by
  classical
  dsimp only
  let p := Route.line 0 ⟨0, 1⟩
  let q := Route.line ⟨0, 1⟩ ⟨0, 2⟩
  let c : ℂ := ⟨1, 1⟩
  have hconn : IsPathConnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isPathConnected ⟨0, Set.mem_univ 0⟩
  have ha : p.finish ∉ ({c} : Finset ℂ) := by
    intro h
    have he : p.finish = c := Finset.mem_singleton.mp h
    have hr := congrArg Complex.re he
    norm_num [p, c] at hr
  obtain ⟨r, -, hgerm, -, -, hray⟩ :=
    Route.exists_concat_add_rayParity isOpen_univ hconn {c} {c} (fun _ h => h)
      (fun z _ => Set.mem_univ z) p q rfl (Set.mem_univ p.finish) ha
      (u := ⟨1, 1⟩) (by
        intro h
        have hr := congrArg Complex.re h
        norm_num at hr)
  have h := hray c (Finset.mem_singleton_self c)
  exact ⟨r, hgerm, by simpa only [Finset.mem_singleton_self, decide_true] using h⟩

-- The observation is exactly at cut height and starts with odd ray parity.
example : ∃ r : Route, r.start = 0 ∧ r.finish = ⟨0, 2⟩ ∧
    r.rayParity 1 ⟨-1, 1⟩ = false := by
  classical
  let b : ℂ := ⟨0, 2⟩
  let c : ℂ := ⟨-1, 1⟩
  let points : Finset ℂ := {c}
  have hconn : IsPathConnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isPathConnected ⟨0, Set.mem_univ 0⟩
  have hcut : AffineMap.lineMap (0 : ℂ) b (1 / 2 : ℝ) ∈
      Set.univ \ (↑points : Set ℂ) := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro h
    have he : AffineMap.lineMap (0 : ℂ) b (1 / 2 : ℝ) = c := Finset.mem_singleton.mp h
    have hr := congrArg Complex.re he
    norm_num [AffineMap.lineMap_apply_module', Complex.real_smul, Complex.mul_re, b, c] at hr
  obtain ⟨r, he, -, -, -, hr⟩ :=
    Route.exists_line_add_rayParity isOpen_univ hconn points points (fun _ h => h)
      (fun z _ => Set.mem_univ z) 0 b (t := 1 / 2) (by constructor <;> norm_num) hcut
      (u := 1) one_ne_zero
  have hline : (Route.line 0 b).rayParity 1 c = true := by
    rw [Route.rayParity_line]
    norm_num [RayCrosses, horizontalIntercept, b, c]
  refine ⟨r, he false, he true, ?_⟩
  have hc : c ∈ points := Finset.mem_singleton_self _
  simpa only [hline, hc, decide_true, BooleanRing.add_self, Bool.zero_eq_false] using hr c hc

-- The bent route crosses the observation ray twice, while the horizontal route
-- has no crossings. The observation is aligned with both endpoints.
example :
    ((Route.line 0 ⟨1, 2⟩).concat (Route.line ⟨1, 2⟩ ⟨2, 0⟩)).rayParity 1 ⟨-1, 0⟩ =
      false := by
  classical
  let b : ℂ := ⟨2, 0⟩
  let m : ℂ := ⟨1, 2⟩
  let p := (Route.line 0 m).concat (Route.line m b)
  let q := Route.line 0 b
  let K := Complex.reLm ⁻¹' Set.Ici (0 : ℝ)
  have hK : Convex ℝ K := (convex_Ici _).linear_preimage Complex.reLm
  have hz : (⟨-1, 0⟩ : ℂ) ∉ K := by
    change ¬(0 : ℝ) ≤ -1
    norm_num
  have h0 : (0 : ℂ) ∈ K := by change (0 : ℝ) ≤ 0; exact le_rfl
  have hm : m ∈ K := by change (0 : ℝ) ≤ 1; exact zero_le_one
  have hb : b ∈ K := by change (0 : ℝ) ≤ 2; norm_num
  have hp : p.support ⊆ K := by
    change ((Route.line 0 m).concat (Route.line m b)).support ⊆ K
    rw [Route.support_concat _ _ rfl, Route.support_line, Route.support_line]
    exact Set.union_subset (hK.segment_subset h0 hm) (hK.segment_subset hm hb)
  have hq : q.support ⊆ K := by
    change (Route.line 0 b).support ⊆ K
    rw [Route.support_line]
    exact hK.segment_subset h0 hb
  have hend (side : Bool) : p.endpoint side = q.endpoint side := by
    change ((Route.line 0 m).concat (Route.line m b)).endpoint side =
      (Route.line 0 b).endpoint side
    rw [Route.endpoint_concat _ _ rfl]
    cases side <;> rfl
  change p.rayParity 1 ⟨-1, 0⟩ = false
  rw [Route.rayParity_eq_of_support_subset_convex p q (hend false) (hend true)
    hK hp hq hz]
  change (Route.line 0 b).rayParity 1 ⟨-1, 0⟩ = false
  rw [Route.rayParity_line]
  exact decide_eq_false (not_rayCrosses_of_im_eq (by simp only [one_mul]; rfl) _)

-- The original bend lies at the observation height. A perturbation can put it on either side.
open Classical in
example :
    let bend (m : ℂ) : Route := ⟨1, fun i => if i.val = 1 then m else ⟨i.val, 0⟩⟩
    ∃ ε : ℝ, 0 < ε ∧ ∀ m : ℂ, dist m ⟨1, 1⟩ < ε →
      ∀ w ∈ ({⟨-1, 1⟩, ⟨-1, 0⟩} : Finset ℂ),
        w ∉ (bend m).support ∧ ∀ u : ℂ,
          (bend m).rayParity u w = (bend ⟨1, 1⟩).rayParity u w := by
  let bend (m : ℂ) : Route := ⟨1, fun i => if i.val = 1 then m else ⟨i.val, 0⟩⟩
  let c : ℂ := ⟨1, 1⟩
  let points : Finset ℂ := {⟨-1, 1⟩, ⟨-1, 0⟩}
  let K := Complex.reLm ⁻¹' Set.Ici (0 : ℝ)
  have hK : Convex ℝ K := (convex_Ici _).linear_preimage Complex.reLm
  have hnode (i : Fin ((bend c).segments + 1)) : (bend c).point i ∈ K := by
    fin_cases i <;> norm_num [bend, c, K]
  have havoid (z : ℂ) (hz : z ∈ points) : z ∉ (bend c).support := by
    have hre : z.re = -1 := by
      simp only [points, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> rfl
    rw [Route.support]
    intro hz'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
    have hc := hK.segment_subset (hnode i.castSucc) (hnode i.succ) hi
    change (0 : ℝ) ≤ z.re at hc
    norm_num [hre] at hc
  obtain ⟨ε, hε, hmove⟩ :=
    (bend c).exists_pos_rayParity_eq_of_point_dist_lt_finset points havoid
  refine ⟨ε, hε, fun m hm w hw => ?_⟩
  have hdist (i : Fin ((bend c).segments + 1)) :
      dist ((bend m).point i) ((bend c).point i) < ε := by
    fin_cases i
    · simpa [bend] using hε
    · exact hm
    · simpa [bend] using hε
  exact hmove (bend m).point rfl rfl hdist w hw

private def retracedSegment (a b : ℂ) : Route where
  bends := 1
  point i := if i.val = 1 then b else a

private theorem support_retracedSegment (a b : ℂ) :
    (retracedSegment a b).support = segment ℝ a b := by
  ext z
  rw [Route.support, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    change Fin 2 at i
    fin_cases i
    · exact hi
    · rw [segment_symm]
      exact hi
  · exact fun hz => ⟨0, hz⟩

private theorem retracedSegment_point_eq (a b : ℂ) (i : Fin 3) :
    (retracedSegment a b).point i = a ∨ (retracedSegment a b).point i = b := by
  change (if i.val = 1 then b else a) = a ∨ (if i.val = 1 then b else a) = b
  by_cases h : i.val = 1 <;> simp [h]

-- A horizontal and a vertical closed route both retrace their segment through zero.
open Classical in
example :
    let p := retracedSegment (-1) 1
    let q := retracedSegment (-Complex.I) Complex.I
    (0 : ℂ) ∈ openSegment ℝ (p.point (0 : Fin p.segments).castSucc)
      (p.point (0 : Fin p.segments).succ) ∧
    (0 : ℂ) ∈ openSegment ℝ (q.point (0 : Fin q.segments).castSucc)
      (q.point (0 : Fin q.segments).succ) ∧
    p.intersectionParity q = false := by
  have hmid (a : ℂ) : (0 : ℂ) ∈ openSegment ℝ (-a) a := by
    simpa only [midpoint_neg_self] using midpoint_mem_openSegment (𝕜 := ℝ) (-a) a
  refine ⟨hmid 1, hmid Complex.I, ?_⟩
  apply Route.intersectionParity_eq_false_of_closed rfl rfl
  · intro i
    change Fin 2 at i
    fin_cases i
    · change (-1 : ℂ) ≠ 1
      norm_num [Complex.ext_iff]
    · change (1 : ℂ) ≠ -1
      norm_num [Complex.ext_iff]
  · intro i
    change Fin 2 at i
    fin_cases i
    · change -Complex.I ≠ Complex.I
      norm_num [Complex.ext_iff]
    · change Complex.I ≠ -Complex.I
      norm_num [Complex.ext_iff]
  · intro i
    rw [support_retracedSegment, segment_eq_image_lineMap]
    rintro ⟨t, _, h⟩
    rcases retracedSegment_point_eq (-1) 1 i with hi | hi <;>
      rw [hi] at h <;> have hre := congrArg Complex.re h <;>
      norm_num [AffineMap.lineMap_apply_module'] at hre
  · intro i
    rw [support_retracedSegment, segment_eq_image_lineMap]
    rintro ⟨t, _, h⟩
    rcases retracedSegment_point_eq (-Complex.I) Complex.I i with hi | hi <;>
      rw [hi] at h <;> have him := congrArg Complex.im h <;>
      norm_num [AffineMap.lineMap_apply_module'] at him

-- Each family repeats a nonhorizontal segment twice. The two supports cross at zero.
open Classical in
example :
    let a : ℂ := Complex.I
    let b : ℂ := ⟨1, 1⟩
    let crosses := (openSegment ℝ (-a) a ∩ openSegment ℝ (-b) b).Nonempty
    crosses ∧ (∑ _ : Bool, true * ∑ _ : Bool, true * decide crosses) = (0 : Bool) := by
  intro a b crosses
  have hm (z : ℂ) : (0 : ℂ) ∈ openSegment ℝ (-z) z := by
    simpa only [midpoint_neg_self] using midpoint_mem_openSegment (𝕜 := ℝ) (-z) z
  refine ⟨⟨0, hm a, hm b⟩, ?_⟩
  have vertical {z : ℂ} (hz : z ∈ segment ℝ (-a) a) : z.re = 0 := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨s, _, rfl⟩ := hz
    simp [a, AffineMap.lineMap_apply_module']
  have diagonal {z : ℂ} (hz : z ∈ segment ℝ (-b) b) : z.re = z.im := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨s, _, rfl⟩ := hz
    simp [b, AffineMap.lineMap_apply_module']
  apply sum_openIntersections_eq_zero_of_even
    (fun _ : Bool => -a) (fun _ => a) (fun _ : Bool => -b) (fun _ => b)
    (fun _ => true) (fun _ => true)
  · intro i
    norm_num [a]
  · intro j
    norm_num [b]
  · intro i j _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have hh := diagonal h
      norm_num [a] at hh
    · intro h
      have hh := diagonal h
      norm_num [a] at hh
    · intro h
      have hh := vertical h
      norm_num [b] at hh
    · intro h
      have hh := vertical h
      norm_num [b] at hh
  · intro p
    simp only [Fintype.sum_bool, BooleanRing.add_self, Bool.zero_eq_false]
  · intro p
    simp only [Fintype.sum_bool, BooleanRing.add_self, Bool.zero_eq_false]

-- Two open routes cross once. Repeating each balances the endpoints of its family.
open Classical in
example :
    let p := Route.line (-1) 1
    let q := Route.line (-Complex.I) Complex.I
    p.start ≠ p.finish ∧ q.start ≠ q.finish ∧ p.intersectionParity q = true ∧
      (∑ _ : Bool, true * ∑ _ : Bool, true * p.intersectionParity q) = false := by
  intro p q
  have hpn : (-1 : ℂ) ≠ 1 := by norm_num [Complex.ext_iff]
  have hqn : -Complex.I ≠ Complex.I := by norm_num [Complex.ext_iff]
  have hm (a : ℂ) : (0 : ℂ) ∈ openSegment ℝ (-a) a := by
    simpa only [midpoint_neg_self] using midpoint_mem_openSegment (𝕜 := ℝ) (-a) a
  refine ⟨hpn, hqn, ?_, ?_⟩
  · change (Route.line (-1) 1).intersectionParity (Route.line (-Complex.I) Complex.I) = true
    rw [Route.intersectionParity_line_line]
    exact decide_eq_true ⟨0, hm 1, hm Complex.I⟩
  have hre {z : ℂ} (hz : z ∈ q.support) : z.re = 0 := by
    change z ∈ (Route.line (-Complex.I) Complex.I).support at hz
    rw [Route.support_line, segment_eq_image_lineMap] at hz
    obtain ⟨t, _, rfl⟩ := hz
    simp [AffineMap.lineMap_apply_module']
  have him {z : ℂ} (hz : z ∈ p.support) : z.im = 0 := by
    change z ∈ (Route.line (-1) 1).support at hz
    rw [Route.support_line, segment_eq_image_lineMap] at hz
    obtain ⟨t, _, rfl⟩ := hz
    simp [AffineMap.lineMap_apply_module']
  apply Route.sum_intersectionParity_eq_false_of_even (fun _ : Bool => p) (fun _ : Bool => q)
    (fun _ => true) (fun _ => true)
  · intro _ i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hpn
  · intro _ j
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hqn
  · intro _ _ _ _ k hz
    have h := hre hz
    change Fin 2 at k
    fin_cases k
    · change (-1 : ℂ).re = 0 at h
      norm_num at h
    · change (1 : ℂ).re = 0 at h
      norm_num at h
  · intro _ _ _ _ k hz
    have h := him hz
    change Fin 2 at k
    fin_cases k
    · change (-Complex.I).im = 0 at h
      norm_num at h
    · change Complex.I.im = 0 at h
      norm_num at h
  · intro z
    simp only [Fintype.sum_bool, BooleanRing.add_self, Bool.zero_eq_false]
  · intro z
    simp only [Fintype.sum_bool, BooleanRing.add_self, Bool.zero_eq_false]

end CslibFrontierTests.PolygonalRayParityIntersections
