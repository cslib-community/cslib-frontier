/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Algebra.Order.Module.Defs
import CslibFrontier.Probability.PMF

/-!
# Classical mixtures of algebraic measurements

An independent classical draw chooses a measurement. Its effect at each outcome is the
average of that outcome's effects.
-/

public section

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

end Cslib.Quantum.Measurement
