/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary annular routing client)

public import CslibFrontier.Foundations.Geometry.Polygonal.AnnularSpokes
import CslibFrontier.Foundations.Geometry.Polygonal.AnnularPaths
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FinCases

/-! Continuous annular paths for exchanged antipodes and polygonal spokes for a cyclic shift. -/

public section

namespace CslibFrontierTests.PolygonalAnnularPaths

open Cslib.Polygonal

private noncomputable def ports (r : ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then (r : ℂ) else ((-r : ℝ) : ℂ)

private theorem norm_ports {r : ℝ} (hr : 0 ≤ r) (i : Fin 2) :
    ‖ports r i‖ = r := by
  by_cases h : i = 0 <;> simp [ports, h, Complex.norm_real, Real.norm_of_nonneg hr]

private theorem port_angles_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective (fun i => ((ports r i).arg : Real.Angle)) := by
  have hpos := Complex.arg_ofReal_of_nonneg hr.le
  have hneg : (-(r : ℂ)).arg = Real.pi := by
    rw [← Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_neg (neg_neg_of_pos hr)
  intro i j hij
  have heq := Complex.arg_coe_angle_eq_iff.mp hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (Real.pi_ne_zero (by simpa [ports, hpos, hneg] using heq.symm)).elim
  · simp [ports, hpos, hneg] at heq
  · rfl

private theorem two_port_order (dir : Fin 2 → Real.Angle) :
    ∀ i j, i ≠ Fin.last 1 → j ≠ Fin.last 1 → i ≠ j →
      (sbtw (dir (Fin.last 1)) (dir i) (dir j) ↔ j.val < i.val) := by
  intro i j hi hj hij
  fin_cases i <;> fin_cases j <;> contradiction

/-- The two exchanged antipodal pairs have disjoint continuous paths. -/
theorem antipodal_paths :
    ∃ γ : Fin 2 → ℝ → ℂ,
      (∀ i, Continuous (γ i)) ∧ γ 0 0 = 1 ∧ γ 1 0 = -1 ∧ γ 0 1 = -2 ∧ γ 1 1 = 2 ∧
      (∀ i t, t ∈ Set.Icc 0 1 → ‖γ i t‖ = AffineMap.lineMap (1 : ℝ) 2 t) ∧
      ∀ s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → γ 0 s ≠ γ 1 t := by
  let p := ports 1
  let q := ports 2 ∘ Fin.rev
  have hp (i : Fin 2) : ‖p i - 0‖ = 1 := by
    rw [sub_zero]
    exact norm_ports zero_le_one i
  have hq (i : Fin 2) : ‖q i - 0‖ = 2 := by
    rw [sub_zero]
    exact norm_ports (by norm_num) i.rev
  have hp' : Function.Injective (fun i => ((p i - 0).arg : Real.Angle)) := by
    simpa only [p, sub_zero] using (port_angles_injective (r := 1) zero_lt_one)
  have hq' : Function.Injective (fun i => ((q i - 0).arg : Real.Angle)) := by
    intro i j h
    apply Fin.rev_involutive.injective
    apply port_angles_injective (r := 2) (by norm_num)
    simpa only [q, Function.comp_apply, sub_zero] using h
  obtain ⟨γ, hcont, _, hstart, hfinish, hnorm, hinj⟩ := exists_annular_paths 1 0 (r := 1) (R := 2)
    zero_lt_one (by norm_num) p q hp hq hp' hq' (two_port_order _) (two_port_order _)
  refine ⟨γ, hcont, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [p, ports] using hstart 0
  · simpa [p, ports] using hstart 1
  · simpa [q, ports, Fin.rev] using hfinish 0
  · simpa [q, ports, Fin.rev] using hfinish 1
  · simpa only [sub_zero] using hnorm
  · intro s t hs ht heq
    have h : ((0 : Fin 2), s) = (1, t) := hinj hs ht heq
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)

private noncomputable def threeAngles (shift : Bool) (i : Fin 3) : ℝ :=
  if i = 0 then (if shift then 0 else Real.pi / 2)
  else if i = 1 then (if shift then -(Real.pi / 2) else 0)
  else if shift then Real.pi / 2 else -(Real.pi / 2)

private theorem threeAngles_mem (shift : Bool) (i : Fin 3) :
    threeAngles shift i ∈ Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  cases shift <;> fin_cases i <;> constructor <;> norm_num [threeAngles] <;>
    linarith [Real.pi_pos]

private theorem threeAngles_injective (shift : Bool) :
    Function.Injective (fun i => (threeAngles shift i : Real.Angle)) := by
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  intro i j heq
  have he := AddCircle.injOn_coe_Ico (2 * Real.pi) (-Real.pi)
    (Set.Ioo_subset_Ico_self (threeAngles_mem shift i))
    (Set.Ioo_subset_Ico_self (threeAngles_mem shift j)) heq
  cases shift <;> fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | norm_num [threeAngles] at he
      done
    | norm_num [threeAngles] at he
      linarith [Real.pi_pos]

private theorem threeAngles_order (shift : Bool) :
    ∀ i j, i ≠ Fin.last 2 → j ≠ Fin.last 2 → i ≠ j →
      (sbtw (threeAngles shift (Fin.last 2) : Real.Angle) (threeAngles shift i : Real.Angle)
        (threeAngles shift j : Real.Angle) ↔ j.val < i.val) := by
  have hlo : -(Real.pi / 2) < 0 := neg_neg_of_pos (half_pos Real.pi_pos)
  have hhi : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hbase : sbtw ((-(Real.pi / 2) : ℝ) : Real.Angle) (0 : ℝ) (Real.pi / 2 : ℝ) := by
    have hm := threeAngles_mem false
    have ha : -(Real.pi / 2) ∈ Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [threeAngles] using hm 2
    have hb : (0 : ℝ) ∈ Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [threeAngles] using hm 1
    have hc : Real.pi / 2 ∈ Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      simpa [threeAngles] using hm 0
    exact (sbtw_angle_iff_cyclic_lt ha hb hc hlo.ne hhi.ne (hlo.trans hhi).ne).mpr
      (Or.inl ⟨hlo, hhi⟩)
  have hclock : sbtw (threeAngles shift (Fin.last 2) : Real.Angle)
      (threeAngles shift 1 : Real.Angle) (threeAngles shift 0 : Real.Angle) := by
    cases shift
    · simpa [threeAngles, Fin.last] using hbase
    · simpa [threeAngles, Fin.last] using hbase.cyclic_right
  intro i j hi hj hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact iff_of_false hclock.cyclic_left.not_sbtw (by decide)
  · exact iff_of_true hclock (by decide)

private noncomputable def threePorts (r : ℝ) (shift : Bool) (i : Fin 3) : ℂ :=
  (r : ℂ) * ((threeAngles shift i : Real.Angle).toCircle : ℂ)

private theorem threePorts_norm {r : ℝ} (hr : 0 < r) (shift : Bool) (i : Fin 3) :
    ‖threePorts r shift i - 0‖ = r := by
  simp [threePorts, Complex.norm_real, Real.norm_of_nonneg hr.le]

private theorem threePorts_angle {r : ℝ} (hr : 0 < r) (shift : Bool) (i : Fin 3) :
    ((threePorts r shift i - 0).arg : Real.Angle) = threeAngles shift i := by
  rw [sub_zero, threePorts, Complex.arg_ofReal_mul hr _, Real.Angle.arg_toCircle]

-- The inner rays and the shifted outer ports form one embedded three-spoke fan.
example : ∃ T : Fin 3 → Route,
    (∀ i, (T i).start = 0 ∧ (T i).finish = threePorts 2 true i ∧
      (T i).germ false = threePorts 1 false i ∧ (T i).IsSimple ∧
      (T i).support \ Metric.ball 0 2 = {threePorts 2 true i}) ∧
    Pairwise (fun i j => (T i).support ∩ (T j).support = {0}) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  simpa only [sub_zero] using exists_annular_spokes 2 0
    zero_lt_one (by norm_num) (threePorts 1 false) (threePorts 2 true)
    (threePorts_norm zero_lt_one false) (threePorts_norm htwo true)
    (by simpa only [threePorts_angle zero_lt_one] using threeAngles_injective false)
    (by simpa only [threePorts_angle htwo] using threeAngles_injective true)
    (by simpa only [threePorts_angle zero_lt_one] using threeAngles_order false)
    (by simpa only [threePorts_angle htwo] using threeAngles_order true)

end CslibFrontierTests.PolygonalAnnularPaths
