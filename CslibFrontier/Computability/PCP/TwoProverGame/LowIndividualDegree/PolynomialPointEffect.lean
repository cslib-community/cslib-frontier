/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.BoundedPolynomial
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
import CslibFrontier.Probability.PMF.Uniform

/-!
# Averaged polynomial point effects

For each polynomial, select the point effect corresponding to its value at a
uniform point and average those effects. The resulting positive contractions
are the objective matrices in the self-improvement program and are bounded
by the majorants used in the slice estimates.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.averagePolynomialPointEffect`: the effect
  of matching the polynomial at a uniformly sampled point.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum MvPolynomial

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The true effect of the uniform mixture of tests for the value of a fixed polynomial. -/
noncomputable def averagePolynomialPointEffect (B : (Fin m → F) → Measurement F A)
    (g : BoundedPolynomial F m d) : A :=
  (Measurement.mixture (Cslib.Probability.PMF.uniformOfFintype (Fin m → F))
    (fun u => (B u).map (fun a => decide (a = eval u g.val)))).effect true

/-- The effect is the uniform average of the corresponding point effects. -/
theorem averagePolynomialPointEffect_eq (B : (Fin m → F) → Measurement F A)
    (g : BoundedPolynomial F m d) : averagePolynomialPointEffect B g =
      (Fintype.card ((Fin m → F)) : ℝ)⁻¹ • ∑ u : (Fin m → F), (B u).effect (eval u g.val) := by
  rw [averagePolynomialPointEffect, Measurement.mixture_uniform_effect]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  simp [Measurement.map_effect, sum_filter]

/-- The uniform average is a positive contraction, so the identity is always a majorant. -/
theorem averagePolynomialPointEffect_mem_Icc (B : (Fin m → F) → Measurement F A)
    (g : BoundedPolynomial F m d) : averagePolynomialPointEffect B g ∈ Set.Icc (0 : A) 1 :=
  ⟨Measurement.nonneg _ true, Measurement.effect_le_one _ true⟩

/-- An operator commuting with all the point effects also commutes with their average. -/
theorem commute_averagePolynomialPointEffect
    (B : (Fin m → F) → Measurement F A) (g : BoundedPolynomial F m d) (C : A)
    (hc : ∀ u b, Commute C ((B u).effect b)) : Commute C (averagePolynomialPointEffect B g) := by
  rw [averagePolynomialPointEffect_eq]
  exact (Commute.sum_left _ _ _ fun u _ => (hc u _).symm).symm.smul_right _

end Cslib.PCP.LowIndividualDegree
