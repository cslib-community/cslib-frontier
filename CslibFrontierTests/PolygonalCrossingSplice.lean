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

private theorem route_segments_nondegenerate (k : Fin route.segments) :
    route.point k.castSucc ≠ route.point k.succ := by
  fin_cases k <;> intro he
  · change (-2 : ℂ) = 2 at he
    norm_num at he
  · change (2 : ℂ) = 2 + 2 * Complex.I at he
    have h := congrArg Complex.im he
    norm_num [Complex.add_im, Complex.mul_im] at h
  · change (2 : ℂ) + 2 * Complex.I = 2 * Complex.I at he
    have h := congrArg Complex.re he
    norm_num [Complex.add_re, Complex.mul_re] at h
  · change (2 : ℂ) * Complex.I = -2 * Complex.I at he
    have h := congrArg Complex.im he
    norm_num [Complex.mul_im] at h
  · change (-2 : ℂ) * Complex.I = -2 - 2 * Complex.I at he
    have h := congrArg Complex.re he
    norm_num [Complex.sub_re, Complex.mul_re] at h
  · change (-2 : ℂ) - 2 * Complex.I = -2 at he
    have h := congrArg Complex.im he
    norm_num [Complex.sub_im, Complex.mul_im] at h

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
outgoing directions, nondegenerate segments, exterior support and parity against an exterior
observer. Points in the closed disk have unique positions. Exterior points gain no open segment
visits on any fixed line. The shared start and finish trace back to distinct original endpoint
positions. Exterior points of the original support that are not listed points still have
strict-interior visits after splicing. -/
theorem removes_orthogonal_crossing :
    let r := Route.line (((-3 / 2 : ℝ) : ℂ) - Complex.I) (((-3 / 2 : ℝ) : ℂ) + Complex.I)
    let crossings (p : Route) := openSegmentCrossings
      (fun k : Fin p.segments => p.point k.castSucc) (fun k => p.point k.succ)
    let onLine (p : Route) (w : ℂ) (L : AffineSubspace ℝ ℂ) :=
      {k : Fin p.segments // w ∈ openSegment ℝ (p.point k.castSucc) (p.point k.succ) ∧
        affineSpan ℝ ({p.point k.castSucc, p.point k.succ} : Set ℂ) = L}
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
      (∀ k : Fin q.segments, q.point k.castSucc ≠ q.point k.succ) ∧
      (∀ w ∉ Metric.closedBall (0 : ℂ) 1, w ∈ p.support → (∀ a, p.point a ≠ w) →
        ∃ (k : Fin q.segments) (s : ℝ), s ∈ Set.Ioo 0 1 ∧ q.eval k s = w) ∧
      (∀ w ∉ Metric.closedBall (0 : ℂ) 1, ∀ L, Nat.card (onLine q w L) ≤ Nat.card (onLine p w L)) ∧
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
  intro r crossings onLine
  have hz : (0 : ℂ) ∈ crossings route := ⟨0, 3, by decide, hx, hy⟩
  refine ⟨route, hz, ?_⟩
  obtain ⟨q, hstart, hfinish, hn, hout, hparity, hgerm, hcross, hpos, hExt, hNondeg,
    hVisit, _, _, hOpen, _⟩ :=
    route.exists_splice_of_isolated_crossing 0 3 (by decide) (by norm_num) hx hy hpair
      route_ends_outside connector_segments_outside
  refine ⟨q, hstart, hfinish, hn, hout, ?_, ?_, hpos, ?_,
    hNondeg route_segments_nondegenerate, ?_, ?_, hparity r observer_disjoint_disk⟩
  · intro b
    obtain ⟨c, hc, he⟩ := hgerm b
    rw [he, Complex.real_smul, Complex.arg_ofReal_mul hc _]
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
      hExt 0 (Fin.last q.bends) (by simp) (by simp) (hfirst.symm ▸ houtside)
        (hfirst.trans (hclosed.trans hlast.symm)) hneq
    exact ⟨a, b, u, v, hu, hv, ha.trans hfirst, hb.trans hlast, hab,
      fun h => (lt_irrefl 0) (hua.mpr h).1, fun h => (lt_irrefl 1) (hvb.mpr h).2⟩
  · intro w hw hp hnodes
    have hq : w ∈ q.support \ Metric.closedBall (0 : ℂ) 1 := hout.symm ▸ ⟨hp, hw⟩
    obtain ⟨k, s, hs, hks⟩ := (q.mem_support_iff w).mp hq.1
    obtain ⟨j, t, ht, hjt, hclass⟩ := hVisit k hs (hks.symm ▸ hw)
    refine ⟨k, s, hclass.mpr ?_, hks⟩
    by_contra hboundary
    have ht' : t ∈ ({0, 1} : Set ℝ) :=
      Set.Icc_sdiff_Ioo_same (show (0 : ℝ) ≤ 1 from zero_le_one) ▸ ⟨ht, hboundary⟩
    rcases Set.mem_insert_iff.mp ht' with rfl | ht'
    · apply hnodes j.castSucc
      simpa only [Route.eval, AffineMap.lineMap_apply_zero] using hjt.trans hks
    · rw [Set.mem_singleton_iff] at ht'
      subst t
      apply hnodes j.succ
      simpa only [Route.eval, AffineMap.lineMap_apply_one] using hjt.trans hks
  · intro w hw L
    obtain ⟨f, hline⟩ := hOpen w hw
    let g (k : onLine q w L) : onLine route w L :=
      let x : {j : Fin q.segments // w ∈ openSegment ℝ (q.point j.castSucc) (q.point j.succ)} :=
        ⟨k.val, k.property.1⟩
      ⟨(f x).val, (f x).property, (hline x).symm.trans k.property.2⟩
    refine Nat.card_le_card_of_injective g ?_
    intro a b hab
    apply Subtype.ext
    have hf : f ⟨a.val, a.property.1⟩ = f ⟨b.val, b.property.1⟩ :=
      Subtype.ext (congrArg (fun k : onLine route w L => k.val) hab)
    exact Subtype.mk.inj (f.injective hf)

end CslibFrontierTests.PolygonalCrossingSplice
