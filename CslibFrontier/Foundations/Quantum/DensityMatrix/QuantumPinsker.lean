/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyConvexity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantum Pinsker's inequality

Half the squared trace norm of a difference of density matrices is bounded by their
relative entropy in nats. This is
[Bavarian, Vidick and Yuen, Proposition 5.4][BavarianVidickYuen2022]
(arXiv:1509.07466v2, printed p. 19), with the factor of `log 2` absorbed by the change
from base-two logarithms. Singular density matrices are allowed, and the divergence
is infinite on a support mismatch.

In the resolvent variational formula, take a test matrix of the form
`(1 - s) • 1 + ((1 - s)^2 * d) • U`, where `d` is the trace norm of the state
difference and `U` attains its real trace overlap. This bounds the entropy integrand
below by `(1 - s) * d^2`.

## Main results

* `traceNorm_sub_sq_div_two_le_relativeEntropy`: quantum Pinsker in nats.
-/

public section

namespace Cslib.Quantum

open Matrix MeasureTheory
open scoped ComplexOrder Interval MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem resolvent_test_value {ρ σ U : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hU : U ∈ unitaryGroup ι ℂ)
    (a b t : ℝ) :
    let X := a • (1 : Matrix ι ι ℂ) + b • U
    2 * (Xᴴ * ρ).trace.re - (Xᴴ * (σ * X + t • (X * ρ))).trace.re =
      2 * (a + b * (Uᴴ * ρ).trace.re) -
        ((a ^ 2 + b ^ 2 + 2 * a * b * (Uᴴ * σ).trace.re) +
          t * (a ^ 2 + b ^ 2 + 2 * a * b * (Uᴴ * ρ).trace.re)) := by
  let X := a • (1 : Matrix ι ι ℂ) + b • U
  have hstar : Xᴴ = a • (1 : Matrix ι ι ℂ) + b • Uᴴ := by
    simp only [X, conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_one]
  have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
  have hU'U : U * Uᴴ = 1 := (mem_unitaryGroup_iff).mp hU
  have hnormal : X * Xᴴ = Xᴴ * X := by
    rw [hstar]
    simp only [X, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, Matrix.one_mul, Matrix.mul_one, hUU, hU'U, mul_comm b a]
    abel
  have hlinear (A : Matrix ι ι ℂ) (hA : IsDensityMatrix A) :
      (Xᴴ * A).trace.re = a + b * (Uᴴ * A).trace.re := by
    rw [hstar, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, trace_add,
      trace_smul, trace_smul, hA.trace_eq_one]
    simp [Complex.real_smul, Complex.mul_re]
  have hquad (A : Matrix ι ι ℂ) (hA : IsDensityMatrix A) :
      ((Xᴴ * X) * A).trace.re = a ^ 2 + b ^ 2 + 2 * a * b * (Uᴴ * A).trace.re := by
    rw [hstar]
    simp only [X, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, hUU, trace_add, trace_smul,
      hA.trace_eq_one, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_one, ← hA.posSemidef.isHermitian.re_trace_conjTranspose_mul U]
    ring
  have hcycle : (Xᴴ * (σ * X)).trace = ((Xᴴ * X) * σ).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm (Xᴴ * σ) X, ← Matrix.mul_assoc, hnormal]
  change 2 * (Xᴴ * ρ).trace.re - (Xᴴ * (σ * X + t • (X * ρ))).trace.re = _
  rw [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, Complex.add_re, hcycle,
    ← Matrix.mul_assoc Xᴴ X ρ, hlinear ρ hρ, hquad σ hσ]
  rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, hquad ρ hρ]

/-- **Quantum Pinsker's inequality** for finite density matrices, with logarithms in
nats and extended relative entropy. -/
theorem traceNorm_sub_sq_div_two_le_relativeEntropy {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    (((ρ - σ).traceNorm ^ 2 / 2 : ℝ) : WithTop ℝ) ≤ relativeEntropy ρ σ := by
  by_cases hsupport : SupportLE ρ σ
  · rw [relativeEntropy_of_supportLE hsupport, WithTop.coe_le_coe]
    let d := (ρ - σ).traceNorm
    obtain ⟨hi, he⟩ := relativeEntropyReal_resolventIntegral hρ.posSemidef hσ.posSemidef hsupport
    obtain ⟨U, hU, hUval, _⟩ := traceNorm_eq_max_re_trace (ρ - σ)
    have hd : (Uᴴ * ρ).trace.re - (Uᴴ * σ).trace.re = d := by
      rw [Matrix.mul_sub, trace_sub, Complex.sub_re] at hUval
      exact hUval
    have hg : IntervalIntegrable (fun s : ℝ => (1 - s) * d ^ 2) volume 0 1 :=
      (by fun_prop : Continuous (fun s : ℝ => (1 - s) * d ^ 2)).intervalIntegrable _ _
    have hval : (∫ s in (0 : ℝ)..1, (1 - s) * d ^ 2) = d ^ 2 / 2 := by
      have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
      have hl : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
        continuous_id.intervalIntegrable 0 1
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub hc hl,
        intervalIntegral.integral_const, integral_id]
      ring
    rw [← he, ← hval]
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hg hi
    intro s hs
    let a := 1 - s
    let t := s / a
    have ha : 0 < a := sub_pos.mpr hs.2
    let b := a ^ 2 * d
    let X := a • (1 : Matrix ι ι ℂ) + b • U
    have hbound := (relativeEntropyResolvent_isGreatest (div_pos hs.1 ha)
      hρ.posSemidef hσ.posSemidef).2 (Set.mem_range_self X)
    rw [resolvent_test_value hρ hσ hU a b t] at hbound
    have ht : t = (1 - a) / a := by
      change s / a = (1 - (1 - s)) / a
      congr 1
      ring
    have hanorm : ρ.trace.re = 1 := by rw [hρ.trace_eq_one, Complex.one_re]
    change a * d ^ 2 ≤ (relativeEntropyResolvent t ρ σ - a * ρ.trace.re) / a ^ 2
    rw [hanorm, mul_one, le_div_iff₀ (pow_pos ha _)]
    calc
      a * d ^ 2 * a ^ 2 = 2 * (a + b * (Uᴴ * ρ).trace.re) -
          ((a ^ 2 + b ^ 2 + 2 * a * b * (Uᴴ * σ).trace.re) +
            t * (a ^ 2 + b ^ 2 + 2 * a * b * (Uᴴ * ρ).trace.re)) - a := by
        rw [ht]
        dsimp only [b]
        rw [← hd]
        field_simp [ha.ne']
        ring
      _ ≤ relativeEntropyResolvent t ρ σ - a := sub_le_sub_right hbound _
  · rw [relativeEntropy_of_not_supportLE hsupport]
    exact le_top

end Cslib.Quantum
