/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of finite slope detours)

public import CslibFrontier.Foundations.Geometry.Polygonal.SlopeDetour
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Tactic.NormNum

/-!
Ordinary clients evaluate a rational quadruple with protected slope zero. Two different
contacts have the same abscissa but distinct heights. The named `protected_quadruple` client
uses the constructive theorem to obtain an actual pair contact outside a third route.
Empty/singleton families and equal-slope rejection exercise its exact input contract.
-/

public section

namespace Cslib.Tests.PolygonalSlopeDetour

open Cslib.Polygonal Cslib.Polygonal.Route

private noncomputable def quadruple (i : Fin 4) : Route :=
  if i = 0 then line ⟨-1, 0⟩ ⟨1, 0⟩
  else slopeDetour 1 (i.val : ℝ) (((i.val : ℝ) ^ 2 + 13 * i.val) / 1000)

-- The protected route is the original one-segment object, including its segment count.
example : quadruple 0 = line ⟨-1, 0⟩ ⟨1, 0⟩ ∧ (quadruple 0).segments = 1 := by
  exact ⟨rfl, rfl⟩

-- Pair03 crosses the protected line in actual open parameters of each first segment.
example :
    (quadruple 0).eval 0 (125 / 254) = (⟨-2 / 127, 0⟩ : ℂ) := by
  change (line (⟨-1, 0⟩ : ℂ) ⟨1, 0⟩).eval 0 (125 / 254) = _
  rw [eval_line]
  norm_num [AffineMap.lineMap_apply_module, Complex.ext_iff,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]

example : (quadruple 3).eval 0 (125 / 127) = (⟨-2 / 127, 0⟩ : ℂ) := by
  change (slopeDetour 1 3 (((3 : ℝ) ^ 2 + 13 * 3) / 1000)).eval 0 (125 / 127) = _
  rw [eval_slopeDetour]
  norm_num [AffineMap.lineMap_apply_module, Complex.ext_iff,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]

-- Pair12 has exactly the same abscissa, but a different height.
example :
    (quadruple 1).eval 0 (125 / 127) = (⟨-2 / 127, -1 / 508⟩ : ℂ) := by
  change (slopeDetour 1 ((1 : Fin 4).val : ℝ)
    ((((1 : Fin 4).val : ℝ) ^ 2 + 13 * ((1 : Fin 4).val : ℝ)) / 1000)).eval
      0 (125 / 127) = _
  rw [eval_slopeDetour]
  norm_num [AffineMap.lineMap_apply_module, Complex.ext_iff,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]

example : (quadruple 2).eval 0 (125 / 127) = (⟨-2 / 127, -1 / 508⟩ : ℂ) := by
  change (slopeDetour 1 2 (((2 : ℝ) ^ 2 + 13 * 2) / 1000)).eval 0 (125 / 127) = _
  rw [eval_slopeDetour]
  norm_num [AffineMap.lineMap_apply_module, Complex.ext_iff,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]

example :
    (⟨-2 / 127, 0⟩ : ℂ).re = (⟨-2 / 127, -1 / 508⟩ : ℂ).re ∧
    (⟨-2 / 127, 0⟩ : ℂ) ≠ ⟨-2 / 127, -1 / 508⟩ := by
  norm_num [Complex.ext_iff]

-- These affine parameters are interior; the contacts are not at the middle knots.
example : (125 / 254 : ℝ) ∈ Set.Ioo 0 1 ∧ (125 / 127 : ℝ) ∈ Set.Ioo 0 1 := by
  norm_num

-- The literal protected first vector is twice the width-one zero-height vector.
example : (quadruple 0).germ false = (⟨2, 0⟩ : ℂ) ∧
    (quadruple 3).germ false = (⟨1, 381 / 125⟩ : ℂ) := by
  norm_num [quadruple, slopeDetour, germ_append, germ_line, Complex.ext_iff]

open Classical in
/-- A protected quadruple supplied by the theorem has an actual pair03 contact outside
route1, witnessing the nonvacuous no-triple conclusion through ordinary imports. -/
theorem protected_quadruple :
    ∃ (d : Fin 4 → ℝ) (z : ℂ),
      let R : Fin 4 → Route := fun i =>
        if (some (0 : Fin 4)) = some i then
          line ⟨-1, -1 * (i.val : ℝ)⟩ ⟨1, 1 * (i.val : ℝ)⟩
        else slopeDetour 1 (i.val : ℝ) (d i)
      d 0 = 0 ∧ R 0 = line ⟨-1, 0⟩ ⟨1, 0⟩ ∧
        z ∈ (R 0).support ∧ z ∈ (R 3).support ∧ z ∉ (R 1).support ∧
        ∃ u v : ℝ, u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
          (R 0).eval 0 u = z ∧ (R 3).eval 0 v = z := by
  classical
  have hinj : Function.Injective (fun i : Fin 4 => (i.val : ℝ)) := by
    intro i j h
    change (i.val : ℝ) = (j.val : ℝ) at h
    exact Fin.ext (by exact_mod_cast h)
  obtain ⟨d, h⟩ := exists_slopeDetour_separation (fun i : Fin 4 => (i.val : ℝ)) hinj
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) (some 0)
  dsimp only at h
  obtain ⟨z, hz, _⟩ := h.2.2.1 0 3 (by decide)
  have hf := h.2.1 0 rfl
  have hout := h.2.2.2.2.2 0 3 1 (by decide) (by decide) (by decide) z hz.1 hz.2
  obtain ⟨_, _, u, v, hu, hv, hue, hve⟩ := h.2.2.2.1 0 3 (by decide) z hz.1 hz.2
  let ev : Route → ℝ → ℂ := fun p t => p.eval 0 t
  refine ⟨d, z, hf.1, ?_, ?_, ?_, ?_, u, v, hu, hv, ?_, ?_⟩
  · simp
  · simpa using hz.1
  · simpa using hz.2
  · simpa using hout
  · change ev _ u = z at hue ⊢
    simpa only [ite_eq_left rfl] using hue
  · change ev _ v = z at hve ⊢
    simpa only [ite_eq_right (by decide : (some (0 : Fin 4)) ≠ some 3)] using hve

-- Empty input needs neither an index nor a protected member.
example : ∃ d : Fin 0 → ℝ, ∀ i, (slopeDetour 1 (i.val : ℝ) (d i)).IsSimple := by
  have hinj : Function.Injective (fun i : Fin 0 => (i.val : ℝ)) := by
    intro i
    exact Fin.elim0 i
  obtain ⟨d, _h⟩ := exists_slopeDetour_separation (fun i : Fin 0 => (i.val : ℝ)) hinj
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) none
  refine ⟨d, ?_⟩
  intro i
  exact Fin.elim0 i

-- The protected singleton has zero chosen height and retains a literal simple line.
example : ∃ d : Fin 1 → ℝ, d 0 = 0 ∧ (line (⟨-2, -10⟩ : ℂ) ⟨2, 10⟩).IsSimple := by
  have hinj : Function.Injective (fun _ : Fin 1 => (5 : ℝ)) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨d, h⟩ := exists_slopeDetour_separation (fun _ : Fin 1 => (5 : ℝ)) hinj
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1 / 100) (some 0)
  refine ⟨d, (h.2.1 0 rfl).1, ?_⟩
  convert (h.1 0).2.2.1 using 1; norm_num

-- Two equal slopes fail the actual injectivity premise, even when all other data are valid.
example : ¬Function.Injective (fun _ : Fin 2 => (0 : ℝ)) := by
  intro h
  have h01 : (0 : Fin 2) = 1 := h rfl
  exact (by decide : (0 : Fin 2) ≠ 1) h01

end Cslib.Tests.PolygonalSlopeDetour
