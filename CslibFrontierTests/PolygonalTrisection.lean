/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary trisection API client)

public import CslibFrontier.Foundations.Geometry.Polygonal.Trisection
import CslibFrontier.Foundations.Geometry.Polygonal.CircleChord
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Two cuts within one segment -/

public section

namespace CslibFrontierTests.PolygonalTrisection

open Cslib.Polygonal

private def p : Route := Route.line 0 3

/-- Two cuts in the same original segment give distinct new ends. -/
theorem one_segment_cut_points :
    ((Route.line 0 3).trisect (1 / 3) (1 / 3) 1).start = 1 ∧
      ((Route.line 0 3).trisect (1 / 3) (1 / 3) 1).finish = 2 := by
  change (p.trisect (1 / 3) (1 / 3) 1).endpoint false = 1 ∧
    (p.trisect (1 / 3) (1 / 3) 1).endpoint true = 2
  rw [Route.endpoint_trisect, Route.endpoint_trisect]
  change (Route.line 0 3).eval 0 (1 / 3) = 1 ∧
    (Route.line 0 3).eval 0 (1 - 1 / 3) = 2
  rw [Route.eval_line, Route.eval_line]
  norm_num [AffineMap.lineMap_apply_module', Complex.real_smul]

example : (∀ k : Fin 3, (p.trisect (1 / 3) (1 / 3) k).IsSimple) ∧
    (⋃ k : Fin 3, (p.trisect (1 / 3) (1 / 3) k).support) = p.support := by
  have hp : p.IsSimple := Route.isSimple_line (by norm_num)
  exact ⟨hp.trisect (by norm_num) (by norm_num) (by norm_num),
    p.support_trisect (by norm_num) (by norm_num) (by norm_num)⟩

-- The local time of the first cut can exceed that of the last cut on a later segment.
-- The joined point at 8 is still reached at the end of the first retained segment.
example : ∃ q : Route, q.start = 7 ∧ q.finish = 9 ∧ (8 : ℂ) ∈ q.support := by
  let r : Route := ⟨2, ![0, 4, 8, 12]⟩
  have hne : (1 : Fin r.segments) ≠ 2 := by decide
  obtain ⟨q, e, hstart, hfinish, hseg⟩ := r.exists_subroute_between 1 2 (by decide)
    (s := 3 / 4) (t := 1 / 4) (by norm_num [Set.mem_Ico]) (by norm_num [Set.mem_Ioc])
    (fun h => (hne h).elim)
  refine ⟨q, hstart.trans ?_, hfinish.trans ?_, ?_⟩
  · change AffineMap.lineMap (4 : ℂ) 8 (3 / 4) = 7
    norm_num [AffineMap.lineMap_apply_module', Complex.real_smul]
  · change AffineMap.lineMap (8 : ℂ) 12 (1 / 4) = 9
    norm_num [AffineMap.lineMap_apply_module', Complex.real_smul]
  · let i : Set.Icc (1 : Fin r.segments) 2 := ⟨1, ⟨by decide, by decide⟩⟩
    let k := e.symm i
    have hk : (e k).val = (1 : Fin r.segments) := congrArg Subtype.val (e.apply_symm_apply i)
    obtain ⟨_, _, _, heval⟩ := hseg k
    have hend : q.eval k 1 = 8 := by
      have he := heval 1
      rw [AffineMap.lineMap_apply_one, hk, ite_eq_right hne] at he
      refine he.trans ?_
      change AffineMap.lineMap (4 : ℂ) 8 (1 : ℝ) = 8
      exact AffineMap.lineMap_apply_one _ _
    exact hend ▸ q.at_mem_support k (by simp)

-- The final chord's first point represents the second cut in the old parameter.
example : ∃ (j : Fin p.segments) (r : ℝ), r ∈ Set.Icc 0 1 ∧
    p.eval j r = (p.trisect (1 / 3) (1 / 3) 2).eval 0 0 ∧
    p.position j r = 2 / 3 := by
  obtain ⟨j, r, hr, he, _, hlo, _⟩ := p.exists_trisect_eval
    (s := 1 / 3) (t := 1 / 3) (by norm_num) (by norm_num) (by norm_num) 2 0 0 (by simp)
  refine ⟨j, r, hr, he, ?_⟩
  have h := hlo.mpr (by simp [Route.AtEnd, Route.position])
  have hi : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  rw [hi] at h
  change p.position j r = (p.segments : ℝ) - 1 / 3 at h
  have hc : p.segments = 1 := rfl
  rw [hc, Nat.cast_one] at h
  linarith

-- The disk centered at 2 with radius 1 cuts the segment from 0 to 4 at 1 and 3.
example : ∃ l u : ℝ, 0 < l ∧ l < u ∧ u < 1 ∧
    ((Route.line 0 4).trisect l (1 - u) 1).start = 1 ∧
    ((Route.line 0 4).trisect l (1 - u) 1).finish = 3 := by
  have heval (t : ℝ) : AffineMap.lineMap (0 : ℂ) 4 t = ((t * 4 : ℝ) : ℂ) := by
    rw [AffineMap.lineMap_apply_module', sub_zero, add_zero, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hdist (x : ℝ) : dist (x : ℂ) (2 : ℂ) = |x - 2| := by
    simpa only [Complex.ofReal_ofNat, Real.dist_eq] using Complex.isometry_ofReal.dist_eq x 2
  have hz : (2 : ℂ) ∈ openSegment ℝ 0 4 := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨1 / 2, by norm_num, by rw [heval]; norm_num⟩
  have ha : (0 : ℂ) ∉ Metric.closedBall (2 : ℂ) 1 := by
    change ¬dist ((0 : ℝ) : ℂ) (2 : ℂ) ≤ 1
    rw [hdist]
    norm_num
  have hb : (4 : ℂ) ∉ Metric.closedBall (2 : ℂ) 1 := by
    change ¬dist ((4 : ℝ) : ℂ) (2 : ℂ) ≤ 1
    rw [hdist]
    norm_num
  obtain ⟨l, u, hl, hlu, hu, _, hsphere, _⟩ :=
    exists_closedBall_lineMap_cuts (by norm_num) hz ha hb
  have hlow := (hsphere (1 / 4)).mp (by norm_num [Metric.mem_sphere, heval, hdist])
  have hhigh := (hsphere (3 / 4)).mp (by norm_num [Metric.mem_sphere, heval, hdist])
  have hcut : l = 1 / 4 ∧ u = 3 / 4 := by
    rcases hlow with h | h <;> rcases hhigh with h' | h' <;> constructor <;> linarith
  refine ⟨l, u, hl, hlu, hu, ?_⟩
  rw [hcut.1, hcut.2]
  change (Route.line 0 4 |>.trisect (1 / 4) (1 - 3 / 4) 1).endpoint false = 1 ∧
    (Route.line 0 4 |>.trisect (1 / 4) (1 - 3 / 4) 1).endpoint true = 3
  rw [Route.endpoint_trisect, Route.endpoint_trisect]
  change (Route.line 0 4).eval 0 (1 / 4) = 1 ∧
    (Route.line 0 4).eval 0 (1 - (1 - 3 / 4)) = 3
  rw [Route.eval_line, Route.eval_line, heval, heval]
  norm_num

-- Reconnect the horizontal and vertical diameters without a crossing.
example : Disjoint (segment ℝ (1 : ℂ) Complex.I) (segment ℝ (-1) (-Complex.I)) := by
  apply disjoint_segments_of_antipodal_pairs (z := 0) (ρ := 1)
  · simp
  · simp
  · intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  · rw [midpoint_eq_smul_add, add_neg_cancel, smul_zero]
  · rw [midpoint_eq_smul_add, add_neg_cancel, smul_zero]

end CslibFrontierTests.PolygonalTrisection
