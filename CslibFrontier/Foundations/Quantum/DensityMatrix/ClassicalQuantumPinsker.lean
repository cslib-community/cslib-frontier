/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumMarginal
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumPinsker
import CslibFrontier.Foundations.Algebra.Order.WithTop

/-!
# Squared trace deviation of conditional quantum states

Quantum mutual information controls the mean squared trace norm between the quantum
state conditioned on a classical observation and its unconditional marginal.
The same comparison can be summed over coordinates and averaged over a retained
classical transcript. In nats the squared trace norm has coefficient one half.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open Cslib.Probability.PMF (conditionalSnd)

variable {ι X Y T : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- One half of the mean squared trace deviation is bounded by classical–quantum mutual
information. Individual labels may have zero probability. -/
theorem mean_traceNorm_sub_sq_div_two_le_mutualInformation (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (f : X → Y) :
    ((∑ y, ((p.map f) y).toReal *
      ((quantumMarginalGivenMap p ρ f y -
        partialTraceRight (classicalQuantumState p ρ)).traceNorm ^ 2 / 2) : ℝ) : WithTop ℝ) ≤
      mutualInformation (classicalQuantumMarginal p ρ f) := by
  let q := p.map f
  let σ := quantumMarginalGivenMap p ρ f
  have hσ (y : Y) : IsDensityMatrix (σ y) := isDensityMatrix_quantumMarginalGivenMap p hρ f y
  have hm : partialTraceRight (classicalQuantumState q σ) =
      partialTraceRight (classicalQuantumState p ρ) := by
    rw [← classicalQuantumMarginal_eq_state, partialTraceRight_classicalQuantumMarginal]
  rw [classicalQuantumMarginal_eq_state, mutualInformation_classicalQuantumState _ hσ, hm,
    WithTop.coe_sum]
  apply sum_le_sum
  intro y _
  rw [WithTop.coe_mul]
  refine WithTop.mul_le_mul_of_nonneg_coe_left ENNReal.toReal_nonneg ?_
  exact traceNorm_sub_sq_div_two_le_relativeEntropy (hσ y)
    (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight

/-- Sum over the coordinates and average over the observed coordinate values and the
retained transcript. The reference quantum state at each transcript averages over the
whole tuple. The distance is the full trace norm, without a factor of one half. -/
noncomputable def sumConditionalTraceNormSq {m : ℕ} [Fintype T] (P : PMF (T × (Fin m → X)))
    (ρ : T × (Fin m → X) → Matrix ι ι ℂ) : ℝ :=
  ∑ t, ((P.map Prod.fst) t).toReal * ∑ i : Fin m,
    let q := conditionalSnd P t
    let σ (x : Fin m → X) := ρ (t, x)
    let f (x : Fin m → X) := x i
    ∑ x, ((q.map f) x).toReal *
      (quantumMarginalGivenMap q σ f x - quantumMarginalGiven P ρ t).traceNorm ^ 2

/-- A transcript-averaged coordinate information budget in nats gives at most twice
that budget for the summed mean squared trace deviation. -/
theorem sumConditionalTraceNormSq_le_of_information_bound {m : ℕ} [Fintype T]
    (P : PMF (T × (Fin m → X))) {ρ : T × (Fin m → X) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) {K : ℝ}
    (hK : (∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) * ∑ i : Fin m,
      mutualInformation (classicalQuantumMarginal (conditionalSnd P t)
        (fun x => ρ (t, x)) (fun x => x i))) ≤ (K : WithTop ℝ)) :
    sumConditionalTraceNormSq P ρ ≤ 2 * K := by
  have h : ((sumConditionalTraceNormSq P ρ / 2 : ℝ) : WithTop ℝ) ≤
      ∑ t, (((P.map Prod.fst) t).toReal : WithTop ℝ) * ∑ i : Fin m,
        mutualInformation (classicalQuantumMarginal (conditionalSnd P t)
          (fun x => ρ (t, x)) (fun x => x i)) := by
    simp only [sumConditionalTraceNormSq, sum_div, mul_div_assoc, WithTop.coe_sum, WithTop.coe_mul]
    refine sum_le_sum fun t _ => WithTop.mul_le_mul_of_nonneg_coe_left ENNReal.toReal_nonneg
      (sum_le_sum fun i _ => ?_)
    simpa only [WithTop.coe_sum, WithTop.coe_mul, quantumMarginalGiven] using
      mean_traceNorm_sub_sq_div_two_le_mutualInformation (conditionalSnd P t)
      (fun x => hρ (t, x)) (fun x => x i)
  have hh := WithTop.coe_le_coe.mp (h.trans hK)
  linarith

end Cslib.Quantum
