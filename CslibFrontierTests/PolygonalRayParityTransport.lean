/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary-import transport across a crossing)

import CslibFrontier.Foundations.Geometry.Polygonal.RayParityTransport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A straight observation enters a closed triangle through one transverse crossing. -/

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

end CslibFrontierTests.PolygonalRayParityTransport
