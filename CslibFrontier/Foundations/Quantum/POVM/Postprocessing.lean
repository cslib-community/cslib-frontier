/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Foundations.Quantum.Algebra.Measurement

/-!
# Post-processing POVM outcomes

A deterministic function on the outcomes combines the effects in each fibre. This pushes
the distribution forward and commutes with forming a pair of local measurements.
-/

public section

namespace Cslib.Quantum.POVM

open Matrix Finset
open scoped Kronecker MatrixOrder

variable {A B C D ι κ : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Report `f a` when the original measurement has outcome `a`. -/
noncomputable def map [DecidableEq B] (M : POVM A ι) (f : A → B) : POVM B ι :=
  (M.toMeasurement.map f).toPOVM

theorem map_effect [DecidableEq B] (M : POVM A ι) (f : A → B) (b : B) :
    (M.map f).effect b = ∑ a with f a = b, M.effect a := by
  simp only [map, Measurement.toPOVM_effect, Measurement.map_effect, toMeasurement_effect]

/-- Measuring and post-processing give the pushforward of the original law. -/
theorem measure_map [DecidableEq B] (M : POVM A ι) (f : A → B)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (M.map f).measure ψ hψ = (M.measure ψ hψ).map f := by
  rw [← distribution_toMeasurement, ← distribution_toMeasurement]
  exact Measurement.distribution_map _ _ _

/-- Post-processing independently on the two sides commutes with their joint measurement. -/
theorem kronecker_map [DecidableEq C] [DecidableEq D] (M : POVM A ι) (N : POVM B κ)
    (f : A → C) (g : B → D) :
    (M.map f).kronecker (N.map g) = (M.kronecker N).map (Prod.map f g) := by
  ext ⟨c, d⟩ ⟨i, k⟩ ⟨j, l⟩
  simp only [kronecker, map_effect, kronecker_apply, Matrix.sum_apply]
  simp only [sum_filter, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases ha : f a = c <;> by_cases hb : g b = d <;> simp [ha, hb]

end Cslib.Quantum.POVM
