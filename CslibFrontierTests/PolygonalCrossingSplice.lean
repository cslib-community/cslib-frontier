/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary crossing-splice API client)

public import CslibFrontier.Foundations.Geometry.Polygonal.CrossingSplice
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # An orthogonal self-crossing with two exterior connector segments -/

public section

namespace CslibFrontierTests.PolygonalCrossingSplice

open Cslib.Polygonal

private def route : Route :=
  ⟨5, ![-2, 2, 2 + 2 * Complex.I, 2 * Complex.I, -2 * Complex.I, -2 - 2 * Complex.I, -2]⟩

private theorem constant_coordinate (f : ℂ →ᵃ[ℝ] ℝ) {a b w : ℂ} {c : ℝ}
    (ha : f a = c) (hb : f b = c) (hw : w ∈ segment ℝ a b) : f w = c := by
  simpa only [image_segment, ha, hb, segment_same, Set.mem_singleton_iff] using
    Set.mem_image_of_mem f hw

private theorem outside_disk {w : ℂ} (h : 2 ≤ ‖w‖) : w ∉ Metric.closedBall (0 : ℂ) 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    fun h' : ‖w‖ ≤ 1 => (by norm_num : ¬(2 : ℝ) ≤ 1) (h.trans h')

private theorem route_ends_outside (k : Fin (route.segments + 1)) :
    route.point k ∉ Metric.closedBall (0 : ℂ) 1 := by
  apply outside_disk
  fin_cases k
  · change 2 ≤ ‖(-2 : ℂ)‖
    simp
  · change 2 ≤ ‖(2 : ℂ)‖
    simp
  · change 2 ≤ ‖(2 : ℂ) + 2 * Complex.I‖
    exact (by norm_num [Complex.add_re, Complex.mul_re] :
      2 ≤ |((2 : ℂ) + 2 * Complex.I).re|).trans (Complex.abs_re_le_norm _)
  · change 2 ≤ ‖(2 : ℂ) * Complex.I‖
    simp
  · change 2 ≤ ‖(-2 : ℂ) * Complex.I‖
    simp
  · change 2 ≤ ‖(-2 : ℂ) - 2 * Complex.I‖
    exact (by norm_num [Complex.sub_re, Complex.mul_re] :
      2 ≤ |((-2 : ℂ) - 2 * Complex.I).re|).trans (Complex.abs_re_le_norm _)
  · change 2 ≤ ‖(-2 : ℂ)‖
    simp

private theorem connector_segments_outside (k : Fin route.segments) (h₀ : k ≠ 0) (h₃ : k ≠ 3) :
    Disjoint (segment ℝ (route.point k.castSucc) (route.point k.succ))
      (Metric.closedBall (0 : ℂ) 1) := by
  fin_cases k
  · exact (h₀ rfl).elim
  · apply Set.disjoint_left.mpr
    intro w hw hball
    change w ∈ segment ℝ (2 : ℂ) (2 + 2 * Complex.I) at hw
    have hre : w.re = 2 := constant_coordinate Complex.reCLM.toLinearMap.toAffineMap
      (by norm_num) (by norm_num [Complex.add_re, Complex.mul_re]) hw
    apply outside_disk _ hball
    simpa only [hre, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using Complex.abs_re_le_norm w
  · apply Set.disjoint_left.mpr
    intro w hw hball
    change w ∈ segment ℝ (2 + 2 * Complex.I : ℂ) (2 * Complex.I) at hw
    have him : w.im = 2 := constant_coordinate Complex.imCLM.toLinearMap.toAffineMap
      (by norm_num [Complex.add_im, Complex.mul_im]) (by norm_num [Complex.mul_im]) hw
    apply outside_disk _ hball
    simpa only [him, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using Complex.abs_im_le_norm w
  · exact (h₃ rfl).elim
  · apply Set.disjoint_left.mpr
    intro w hw hball
    change w ∈ segment ℝ (-2 * Complex.I : ℂ) (-2 - 2 * Complex.I) at hw
    have him : w.im = -2 := constant_coordinate Complex.imCLM.toLinearMap.toAffineMap
      (by norm_num [Complex.mul_im]) (by norm_num [Complex.sub_im, Complex.mul_im]) hw
    apply outside_disk _ hball
    simpa only [him, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      Complex.abs_im_le_norm w
  · apply Set.disjoint_left.mpr
    intro w hw hball
    change w ∈ segment ℝ (-2 - 2 * Complex.I : ℂ) (-2) at hw
    have hre : w.re = -2 := constant_coordinate Complex.reCLM.toLinearMap.toAffineMap
      (by norm_num [Complex.sub_re, Complex.mul_re]) (by norm_num) hw
    apply outside_disk _ hball
    simpa only [hre, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      Complex.abs_re_le_norm w

private theorem observer_disjoint_disk : Disjoint (Metric.closedBall (0 : ℂ) 1)
    (Route.line (((-3 / 2 : ℝ) : ℂ) - Complex.I) (((-3 / 2 : ℝ) : ℂ) + Complex.I)).support := by
  rw [Route.support_line]
  apply Set.disjoint_left.mpr
  intro w hball hw
  have hre : w.re = -3 / 2 := constant_coordinate Complex.reCLM.toLinearMap.toAffineMap
    (by simp [Complex.sub_re]) (by simp [Complex.add_re]) hw
  have hn := Complex.abs_re_le_norm w
  rw [hre, abs_of_nonpos (by norm_num : (-3 / 2 : ℝ) ≤ 0)] at hn
  have hb : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hball
  linarith

/-- The orthogonal splice strictly reduces the set of interior crossings. It preserves endpoints,
outgoing directions, exterior support and parity against an exterior observer. Points in the
closed disk have unique positions. The shared start and finish outside the disk trace back to
distinct original positions at original segment endpoints. -/
theorem removes_orthogonal_crossing :
    let r := Route.line (((-3 / 2 : ℝ) : ℂ) - Complex.I) (((-3 / 2 : ℝ) : ℂ) + Complex.I)
    let crossings (p : Route) := openSegmentCrossings
      (fun k : Fin p.segments => p.point k.castSucc) (fun k => p.point k.succ)
    ∃ p : Route, (0 : ℂ) ∈ crossings p ∧ ∃ q : Route,
      q.start = p.start ∧ q.finish = p.finish ∧ (0 : ℂ) ∉ q.support ∧
      q.support \ Metric.closedBall (0 : ℂ) 1 = p.support \ Metric.closedBall (0 : ℂ) 1 ∧
      (∀ b : Bool, (q.germ b).arg = (p.germ b).arg) ∧
      crossings q ⊂ crossings p ∧
      (∀ (i j : Fin q.segments) {s t : ℝ}, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        q.eval i s ∈ Metric.closedBall (0 : ℂ) 1 → q.eval i s = q.eval j t →
          q.position i s = q.position j t) ∧
      (∃ (a b : Fin p.segments) (u v : ℝ), u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧
        p.eval a u = q.start ∧ p.eval b v = q.finish ∧ p.position a u ≠ p.position b v ∧
        u ∉ Set.Ioo 0 1 ∧ v ∉ Set.Ioo 0 1) ∧
      q.intersectionParity r = p.intersectionParity r := by
  have hx : (0 : ℂ) ∈ openSegment ℝ (route.point (0 : Fin route.segments).castSucc)
      (route.point (0 : Fin route.segments).succ) := by
    change (0 : ℂ) ∈ openSegment ℝ (-2) 2
    rw [openSegment_eq_image_lineMap]
    exact ⟨1 / 2, by norm_num, by norm_num [AffineMap.lineMap_apply_module', Complex.real_smul]⟩
  have hy : (0 : ℂ) ∈ openSegment ℝ (route.point (3 : Fin route.segments).castSucc)
      (route.point (3 : Fin route.segments).succ) := by
    change (0 : ℂ) ∈ openSegment ℝ (2 * Complex.I) (-2 * Complex.I)
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [AffineMap.lineMap_apply_module', Complex.real_smul]
    norm_num
    ring
  have hpair : (segment ℝ (-2 : ℂ) 2 ∩
      segment ℝ (2 * Complex.I) (-2 * Complex.I)).Subsingleton := by
    have him {w : ℂ} (hw : w ∈ segment ℝ (-2 : ℂ) 2) : w.im = 0 :=
      constant_coordinate Complex.imCLM.toLinearMap.toAffineMap (by norm_num) (by norm_num) hw
    have hre {w : ℂ} (hw : w ∈ segment ℝ (2 * Complex.I) (-2 * Complex.I)) : w.re = 0 :=
      constant_coordinate Complex.reCLM.toLinearMap.toAffineMap
        (by norm_num [Complex.mul_re]) (by norm_num [Complex.mul_re]) hw
    intro x hx y hy
    exact Complex.ext ((hre hx.2).trans (hre hy.2).symm) ((him hx.1).trans (him hy.1).symm)
  intro r crossings
  have hz : (0 : ℂ) ∈ crossings route := ⟨0, 3, by decide, hx, hy⟩
  refine ⟨route, hz, ?_⟩
  obtain ⟨q, hstart, hfinish, hn, hout, hparity, hgerm, hcross, hpositions, hExterior, _⟩ :=
    route.exists_splice_of_isolated_crossing 0 3 (by decide) (by norm_num) hx hy hpair
      route_ends_outside connector_segments_outside
  refine ⟨q, hstart, hfinish, hn, hout, ?_, ?_, hpositions, ?_, hparity r observer_disjoint_disk⟩
  · intro b
    obtain ⟨c, hc, he⟩ := hgerm b
    rw [he, Complex.real_smul, Complex.arg_real_mul _ hc]
  · exact Set.ssubset_iff_exists.mpr
      ⟨fun _ hw => (hcross hw).1, 0, hz,
        fun h => (hcross h).2 (Metric.mem_closedBall_self zero_le_one)⟩
  · have hfirst : q.eval 0 0 = q.start := by simp [Route.eval, Route.start]
    have hlast : q.eval (Fin.last q.bends) 1 = q.finish := by simp [Route.eval, Route.finish]
    have houtside : q.start ∉ Metric.closedBall (0 : ℂ) 1 := hstart.symm ▸ route_ends_outside 0
    have hclosed : q.start = q.finish := hstart.trans hfinish.symm
    have hneq : q.position 0 0 ≠ q.position (Fin.last q.bends) 1 := by
      apply ne_of_lt
      simp only [Route.position, Fin.val_zero, Fin.val_last, Nat.cast_zero, zero_add]
      linarith only [Nat.cast_nonneg (α := ℝ) q.bends]
    obtain ⟨a, b, u, v, hu, hv, ha, hb, hab, hua, hvb⟩ :=
      hExterior 0 (Fin.last q.bends) (by simp) (by simp) (hfirst.symm ▸ houtside)
        (hfirst.trans (hclosed.trans hlast.symm)) hneq
    exact ⟨a, b, u, v, hu, hv, ha.trans hfirst, hb.trans hlast, hab,
      fun h => (lt_irrefl 0) (hua.mpr h).1, fun h => (lt_irrefl 1) (hvb.mpr h).2⟩

end CslibFrontierTests.PolygonalCrossingSplice
