/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.BigOperators.Expect
public import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF

/-!
# Classical mixtures of algebraic measurements

An independent classical draw chooses a measurement. Its effect at each outcome is the
average of that outcome's effects.
-/

public section

namespace Cslib.Quantum.AlgState

open Finset
open scoped BigOperators

/-- Evaluating a uniform average of operators gives the average of their state expectations. -/
theorem re_apply_uniformAverage {ι A : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A]
    (φ : AlgState A) (f : ι → A) :
    (φ ((Fintype.card ι : ℝ)⁻¹ • ∑ x, f x)).re = 𝔼 x, (φ (f x)).re := by
  rw [← IsScalarTower.algebraMap_smul ℂ, map_smul, Complex.coe_algebraMap, smul_eq_mul,
    Complex.re_ofReal_mul, map_sum, Complex.re_sum, Fintype.expect_eq_sum_div_card, inv_mul_eq_div]

end Cslib.Quantum.AlgState

namespace Cslib.Quantum.Measurement

open Finset

variable {ι α A : Type*} [Fintype ι] [Fintype α] [Ring A] [PartialOrder A]
  [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A]

/-- Randomly choose a measurement according to a finite probability mass function. -/
noncomputable def mixture (p : PMF ι) (M : ι → Measurement α A) : Measurement α A where
  effect a := ∑ i, (p i).toReal • (M i).effect a
  nonneg a := sum_nonneg fun i _ => smul_nonneg ENNReal.toReal_nonneg ((M i).nonneg a)
  sum_effect := by
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, sum_effect, ← Finset.sum_smul,
      Cslib.Probability.PMF.sum_toReal, one_smul]

theorem mixture_effect (p : PMF ι) (M : ι → Measurement α A) (a : α) :
    (mixture p M).effect a = ∑ i, (p i).toReal • (M i).effect a := by
  unfold mixture
  rfl

/-- Mixing uniformly gives the ordinary finite average of each effect. -/
theorem mixture_uniform_effect [Nonempty ι] (M : ι → Measurement α A) (a : α) :
    (mixture (Cslib.Probability.PMF.uniformOfFintype ι) M).effect a =
      (Fintype.card ι : ℝ)⁻¹ • ∑ i, (M i).effect a := by
  rw [mixture_effect, Finset.smul_sum]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- Classical mixing commutes with postprocessing measurement outcomes. -/
theorem map_mixture {β : Type*} [Fintype β] [DecidableEq β]
    (p : PMF ι) (M : ι → Measurement α A) (f : α → β) :
    (mixture p M).map f = mixture p (fun i => (M i).map f) := by
  ext b
  simp only [map_effect, mixture_effect, Finset.smul_sum]
  exact sum_comm

end Cslib.Quantum.Measurement
