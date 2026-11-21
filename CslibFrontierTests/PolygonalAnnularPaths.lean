/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary annular routing client)

public import CslibFrontier.Foundations.Geometry.Polygonal.AnnularPaths
import Mathlib.Tactic.FinCases

/-! Two antipodal ports exchange rays as the radius doubles. -/

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
      γ 0 0 = 1 ∧ γ 1 0 = -1 ∧ γ 0 1 = -2 ∧ γ 1 1 = 2 ∧
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
  obtain ⟨γ, _, hstart, hfinish, _, hinj⟩ := exists_annular_paths 1 0 (r := 1) (R := 2)
    zero_lt_one (by norm_num) p q hp hq hp' hq' (two_port_order _) (two_port_order _)
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [p, ports] using hstart 0
  · simpa [p, ports] using hstart 1
  · simpa [q, ports, Fin.rev] using hfinish 0
  · simpa [q, ports, Fin.rev] using hfinish 1
  · intro s t hs ht heq
    have h : ((0 : Fin 2), s) = (1, t) := hinj hs ht heq
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)

end CslibFrontierTests.PolygonalAnnularPaths
