/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary route concatenation client)

public import CslibFrontier.Foundations.Geometry.Polygonal.Concatenate
public import CslibFrontier.Foundations.Geometry.Polygonal.Join
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Closing a four-sided loop by concatenating two bent routes -/

public section

namespace CslibFrontierTests.PolygonalConcatenate

open Cslib.Polygonal Cslib.Polygonal.Route

private def lower : Route := (line (0 : ℂ) ⟨1, -1⟩).append 2
private def upper : Route := (line (2 : ℂ) ⟨1, 1⟩).append 0

private theorem lower_simple : lower.IsSimple := by
  apply Route.isSimple_of_strictMono_re
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · change (0 : ℝ) < 1
    norm_num
  · change (1 : ℝ) < 2
    norm_num

private theorem upper_simple : upper.IsSimple := by
  have h : upper.reverse.IsSimple := by
    apply Route.isSimple_of_strictMono_re
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · change (0 : ℝ) < 1
      norm_num
    · change (1 : ℝ) < 2
      norm_num
  simpa only [Route.reverse_reverse] using h.reverse

private theorem contact (i : Fin lower.segments) (j : Fin upper.segments) (s t : ℝ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (he : lower.eval i s = upper.eval j t) :
    (lower.AtEnd i s true ∧ upper.AtEnd j t false) ∨
      (lower.AtEnd i s false ∧ upper.AtEnd j t true) := by
  have coords {a b c d : ℂ}
      (h : AffineMap.lineMap a b s = AffineMap.lineMap c d t) :
      (s * (b.re - a.re) + a.re = t * (d.re - c.re) + c.re) ∧
        (s * (b.im - a.im) + a.im = t * (d.im - c.im) + c.im) := by
    exact ⟨by simpa only [AffineMap.lineMap_apply_module', Complex.add_re,
        Complex.smul_re, Complex.sub_re, smul_eq_mul] using congrArg Complex.re h,
      by simpa only [AffineMap.lineMap_apply_module', Complex.add_im,
        Complex.smul_im, Complex.sub_im, smul_eq_mul] using congrArg Complex.im h⟩
  fin_cases i <;> fin_cases j
  · obtain ⟨hr, hi⟩ := coords (a := 0) (b := ⟨1, -1⟩) (c := 2) (d := ⟨1, 1⟩) he
    norm_num at hr hi
    linarith [hs.1, ht.1]
  · obtain ⟨_, hi⟩ := coords (a := 0) (b := ⟨1, -1⟩) (c := ⟨1, 1⟩) (d := 0) he
    norm_num at hi
    have hsz : s = 0 := by linarith [hs.1, ht.2]
    have hto : t = 1 := by linarith
    right
    norm_num [AtEnd, position, segments, upper, line, append, hsz, hto]
  · obtain ⟨_, hi⟩ := coords (a := ⟨1, -1⟩) (b := 2) (c := 2) (d := ⟨1, 1⟩) he
    norm_num at hi
    have hso : s = 1 := by linarith [hs.2, ht.1]
    have htz : t = 0 := by linarith
    left
    norm_num [AtEnd, position, segments, lower, line, append, hso, htz]
  · obtain ⟨hr, hi⟩ := coords (a := ⟨1, -1⟩) (b := 2) (c := ⟨1, 1⟩) (d := 0) he
    norm_num at hr hi
    linarith [hs.2, ht.2]

/-- The concatenation joins two actual bends into a simple closed route with both old
supports and no extra connector. -/
theorem diamond :
    let p := (line (0 : ℂ) ⟨1, -1⟩).append 2
    let q := (line (2 : ℂ) ⟨1, 1⟩).append 0
    (p.concat q).IsSimple ∧ (p.concat q).start = (p.concat q).finish ∧
      (p.concat q).segments = 4 ∧ (p.concat q).support = p.support ∪ q.support := by
  change (lower.concat upper).IsSimple ∧
    (lower.concat upper).endpoint false = (lower.concat upper).endpoint true ∧
      (lower.concat upper).segments = 4 ∧ (lower.concat upper).support = _
  have h : lower.finish = upper.start := rfl
  have hp : lower.start ≠ lower.finish := by change (0 : ℂ) ≠ 2; norm_num
  have hq : upper.start ≠ upper.finish := by change (2 : ℂ) ≠ 0; norm_num
  refine ⟨lower_simple.concat upper_simple hp hq h contact, ?_, segments_concat lower upper,
    support_concat lower upper h⟩
  rw [endpoint_concat lower upper h, endpoint_concat lower upper h]
  rfl

example : (lower.concat upper).germ false = (⟨1, -1⟩ : ℂ) ∧
    (lower.concat upper).germ true = (⟨1, 1⟩ : ℂ) := by
  have h : lower.finish = upper.start := rfl
  rw [germ_concat lower upper h, germ_concat lower upper h]
  exact ⟨sub_zero _, sub_zero _⟩

private def lastIndex : Fin (lower.concat upper).segments := ⟨3, by rw [segments_concat]; decide⟩

example (t : ℝ) : (lower.concat upper).eval lastIndex t = upper.eval 1 t := by
  rcases concat_eval_cases lower upper rfl lastIndex with ⟨j, hj, _⟩ | ⟨j, hj, he⟩
  · change 3 = j.val at hj
    have hb := j.isLt
    change j.val < 2 at hb
    omega
  · change 3 = 2 + j.val at hj
    have h : j = 1 := Fin.ext (by change j.val = 1; omega)
    simpa only [h] using he t

end CslibFrontierTests.PolygonalConcatenate
