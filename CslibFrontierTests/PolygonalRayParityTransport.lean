/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary-import transport across a crossing)

import CslibFrontier.Foundations.Geometry.Polygonal.SegmentRays
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Interior transport across a triangle side and endpoint colors of a crossing four-cycle. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PolygonalRayParityTransport

open Cslib Polygonal

private abbrev starts : Fin 4 → ℂ := ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 2⟩]
private abbrev finishes : Fin 4 → ℂ := ![⟨0, 3⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨-1, 0⟩]
private abbrev selected (j : Fin 4) := decide (j ≠ 0)
private noncomputable abbrev probe := (AffineMap.lineMap (starts 0) (finishes 0) : ℝ →ᵃ[ℝ] ℂ)

private theorem heights (j : Fin 4) : (starts j).im ≠ (finishes j).im := by
  fin_cases j <;> norm_num [starts, finishes]

private theorem even_triangle (z : ℂ) :
    (∑ j : Fin 4, ((if starts j = z then selected j else 0) +
      (if finishes j = z then selected j else 0))) = false := by
  classical
  by_cases hA : (⟨-1, 0⟩ : ℂ) = z <;>
    by_cases hB : (⟨1, 1⟩ : ℂ) = z <;>
    by_cases hC : (⟨-1, 2⟩ : ℂ) = z <;>
    simp [Fin.sum_univ_four, starts, finishes, selected, hA, hB, hC,
      ← Bool.zero_eq_false, Bool.add_eq_xor]

private theorem probe_avoids (j : Fin 4) (hj : j ≠ 0) {t : ℝ}
    (ht : t = 1 / 8 ∨ t = 1 / 2) : probe t ∉ segment ℝ (starts j) (finishes j) := by
  rw [segment_eq_image_lineMap]
  rintro ⟨u, _, he⟩
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  rcases ht with rfl | rfl <;> fin_cases j
  all_goals try exact (hj rfl).elim
  all_goals norm_num [starts, finishes, AffineMap.lineMap_apply_module'] at hre
  all_goals norm_num [starts, finishes, AffineMap.lineMap_apply_module'] at him
  all_goals linarith

open Classical in
-- The observation stays on segment zero and crosses exactly one side of a selected triangle.
example :
    (∑ j : Fin 4, (@ite Bool (j = 0) (Classical.propDecidable _) 0 (selected j)) * decide
      ((openSegment ℝ (starts j) (finishes j) ∩
        openSegment ℝ (probe (1 / 8)) (probe (1 / 2))).Nonempty)) = true := by
  have law := rayParity_lineMap_add_eq_sum_intersections_of_even starts finishes selected
    heights even_triangle 0 (fun j hj _ t _ => by
      constructor <;> intro he <;> have hre := congrArg Complex.re he <;>
      fin_cases j <;> first | exact (hj rfl).elim |
        norm_num [starts, finishes, AffineMap.lineMap_apply_module'] at hre)
    (by norm_num : (1 / 8 : ℝ) ∈ Set.Ioo 0 1) (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    (by norm_num) (fun j hj _ => probe_avoids j hj (Or.inl rfl))
    (fun j hj _ => probe_avoids j hj (Or.inr rfl))
  refine law.symm.trans ?_
  norm_num [rayParity, RayCrosses, horizontalIntercept, Fin.sum_univ_four, starts, finishes,
    selected, AffineMap.lineMap_apply_module', Bool.add_eq_xor, ← Bool.zero_eq_false]

private abbrev bowStart : Fin 4 → ℂ := ![⟨0, -1⟩, ⟨0, 2⟩, ⟨-1, 0⟩, ⟨1, 1⟩]
private abbrev bowFinish : Fin 4 → ℂ := ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]

private theorem bow_height (j : Fin 4) : (bowStart j).im ≠ (bowFinish j).im := by
  fin_cases j <;> norm_num [bowStart, bowFinish]

private theorem bow_even (z : ℂ) :
    (∑ j : Fin 4, ((if bowStart j = z then true else 0) +
      (if bowFinish j = z then true else 0))) = false := by
  classical
  have step (j : Fin 4) : bowFinish j = bowStart (finRotate 4 j) := by
    fin_cases j <;> rfl
  simp only [Finset.sum_add_distrib, step]
  have h := Equiv.sum_comp (finRotate 4) (fun j => if bowStart j = z then true else (0 : Bool))
  rw [h, BooleanRing.add_self, Bool.zero_eq_false]

private theorem bow_nodes (j : Fin 4) (hj : j ≠ 0) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap (bowStart 0) (bowFinish 0) t ≠ bowStart j ∧
      AffineMap.lineMap (bowStart 0) (bowFinish 0) t ≠ bowFinish j := by
  constructor <;> intro he
  all_goals have hre := congrArg Complex.re he
  all_goals have him := congrArg Complex.im he
  all_goals fin_cases j
  all_goals try exact (hj rfl).elim
  all_goals norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module'] at hre
  all_goals norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module'] at him
  all_goals linarith [ht.1, ht.2]

private theorem bow_crossing (j : Fin 4) (hj : j ≠ 0) {z : ℂ}
    (hz : z ∈ openSegment ℝ (bowStart j) (bowFinish j) ∩
      openSegment ℝ (bowStart 0) (bowFinish 0)) :
    j = 2 ∧ z = ⟨0, 1 / 2⟩ := by
  obtain ⟨h₁, h₂⟩ := hz
  rw [openSegment_eq_image_lineMap] at h₁ h₂
  obtain ⟨s, hs, hsz⟩ := h₁
  obtain ⟨t, _, htz⟩ := h₂
  have hre := congrArg Complex.re (hsz.trans htz.symm)
  fin_cases j
  · exact (hj rfl).elim
  · norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module'] at hre
    linarith [hs.1]
  · refine ⟨rfl, ?_⟩
    norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module'] at hre
    have he : s = 1 / 2 := by linarith
    rw [← hsz, he]
    apply Complex.ext <;> norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module']
  · norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module'] at hre
    linarith [hs.2]

private theorem bow_has_crossing :
    (openSegment ℝ (bowStart 2) (bowFinish 2) ∩
      openSegment ℝ (bowStart 0) (bowFinish 0)).Nonempty := by
  have point (j : Fin 4) (hj : j = 0 ∨ j = 2) :
      AffineMap.lineMap (bowStart j) (bowFinish j) (1 / 2 : ℝ) = ⟨0, 1 / 2⟩ := by
    rcases hj with rfl | rfl <;>
      apply Complex.ext <;> norm_num [bowStart, bowFinish, AffineMap.lineMap_apply_module']
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  exact ⟨_, point 2 (Or.inr rfl) ▸ lineMap_mem_openSegment ℝ _ _ hhalf,
    point 0 (Or.inl rfl) ▸ lineMap_mem_openSegment ℝ _ _ hhalf⟩

private theorem bow_remote (side : Bool) (j : Fin 4)
    (ha : bowStart j ≠ rayEndpoint bowStart bowFinish (0, side))
    (hb : bowFinish j ≠ rayEndpoint bowStart bowFinish (0, side)) :
    (rayEndpoint bowStart bowFinish (0, side)).im ≠ (bowStart j).im ∧
      (rayEndpoint bowStart bowFinish (0, side)).im ≠ (bowFinish j).im ∧
      rayEndpoint bowStart bowFinish (0, side) ∉ segment ℝ (bowStart j) (bowFinish j) := by
  cases side <;> fin_cases j
  all_goals try exact (ha rfl).elim
  all_goals try exact (hb rfl).elim
  all_goals refine ⟨by norm_num [rayEndpoint, bowStart, bowFinish],
    by norm_num [rayEndpoint, bowStart, bowFinish], ?_⟩
  all_goals rw [segment_eq_image_lineMap]
  all_goals rintro ⟨t, ht, he⟩
  all_goals have him := congrArg Complex.im he
  all_goals norm_num [rayEndpoint, bowStart, bowFinish, AffineMap.lineMap_apply_module'] at him
  all_goals linarith [ht.1, ht.2]

private theorem bow_distinct (side : Bool) (e : Fin 4 × Bool)
    (hp : rayEndpoint bowStart bowFinish e = rayEndpoint bowStart bowFinish (0, side))
    (harg : turnArg (rayEndVector bowStart bowFinish e) =
      turnArg (rayEndVector bowStart bowFinish (0, side))) :
    e = (0, side) := by
  have harg' : (rayEndVector bowStart bowFinish e).arg =
      (rayEndVector bowStart bowFinish (0, side)).arg :=
    Complex.arg_coe_angle_eq_iff.mp (by
      simpa only [turnArg_coe_angle] using congrArg (fun t : ℝ => (t : Real.Angle)) harg)
  have hne (i : Fin 4) : bowStart i ≠ bowFinish i :=
    fun h => bow_height i (congrArg Complex.im h)
  obtain ⟨s, hs, t, _, hst⟩ := exists_small_smul_eq_of_arg_eq
    (rayEndVector_ne_zero bowStart bowFinish hne e)
    (rayEndVector_ne_zero bowStart bowFinish hne (0, side)) harg' zero_lt_one
  have him := congrArg Complex.im hp
  have hre := congrArg Complex.re hst
  obtain ⟨j, tag⟩ := e
  cases side <;> cases tag <;> fin_cases j
  all_goals try rfl
  all_goals norm_num [rayEndpoint, bowStart, bowFinish] at him
  all_goals norm_num [rayEndVector, bowStart, bowFinish] at hre
  all_goals linarith [hs.1]

-- The selected vertical edge crosses the selected diagonal once, so the label and
-- the crossing contribution cancel in the two endpoint colors.
example :
    rayGermColor bowStart bowFinish (fun _ => true) (bowStart 0) (bowFinish 0 - bowStart 0) +
      rayGermColor bowStart bowFinish (fun _ => true) (bowFinish 0) (bowStart 0 - bowFinish 0) =
      false := by
  classical
  have hit (j : Fin 4) (hj : j ≠ 0) :
      (openSegment ℝ (bowStart j) (bowFinish j) ∩
        openSegment ℝ (bowStart 0) (bowFinish 0)).Nonempty ↔ j = 2 :=
    ⟨fun ⟨_, hz⟩ => (bow_crossing j hj hz).1, fun h => h ▸ bow_has_crossing⟩
  rw [rayGermColor_ends_add_eq_crossings bowStart bowFinish (fun _ => true) bow_height bow_even 0
    (fun j hj _ => bow_nodes j hj)
    (fun j hj _ _ hz _ hw => (bow_crossing j hj hz).2.trans (bow_crossing j hj hw).2.symm)
    bow_remote bow_distinct]
  have term (j : Fin 4) :
      (@ite Bool (j = 0) (Classical.propDecidable _) 0 true) * decide
        ((openSegment ℝ (bowStart j) (bowFinish j) ∩
          openSegment ℝ (bowStart 0) (bowFinish 0)).Nonempty) = decide (j = 2) := by
    by_cases hj : j = 0
    · subst j
      simp [← Bool.zero_eq_false]
    · calc
        _ = true * decide (j = 2) := by
          rw [ite_eq_right hj]
          exact congrArg (true * ·) (Bool.decide_congr (hit j hj))
        _ = _ := one_mul _
  calc
    _ = true + ∑ j : Fin 4, decide (j = 2) := by rw [Finset.sum_congr rfl (fun j _ => term j)]
    _ = false := by decide

end CslibFrontierTests.PolygonalRayParityTransport
