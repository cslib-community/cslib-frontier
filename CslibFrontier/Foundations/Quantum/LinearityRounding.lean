/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.FourierMeasurement
public import CslibFrontier.Foundations.Quantum.LocalOrthogonalization

/-!
# Rounding approximately linear observables

Let `A(a)`, for `a ∈ {0,1}ⁿ`, be `±1` observables on `ℂ^ι` that are linear on average in a state
`φ`: `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`. Then there are observables `χ(a)` on the same
space that are unitary and **exactly linear**, `χ(a) χ(a') = χ(a + a')`, and close on average:
`E_a ‖A(a) - χ(a)‖²_φ ≤ 40δ` (`Cslib.Quantum.exists_isProjective_charObs_of_linear`). They are the
character observables of a projective measurement with outcomes in `{0,1}ⁿ`.

This is a **same-space variant with constant `40`** of
[Natarajan and Vidick, §3, Theorem 10][NatarajanVidick2017] (arXiv:1610.03574v1), not that theorem
itself. The source's conclusion is `E_a ‖A(a) - χ(a)‖² ≤ 2δ` in our normalization, for observables
on a dilated space `ℂ^ι ⊗ ℂ^{ι'}`: it dilates the Fourier measurement of `A`
(`Cslib.Quantum.fourierMeasurement`) to a projective measurement with an ancilla (Naimark). Here
the Fourier measurement, which is almost projective, is orthogonalized in place by de la Salle's
theorem, at the cost of the constant. So the rounded observables stay on `ℂ^ι`, and since the
estimate holds in every state, they stay on one party's factor in a tensor-product strategy
(`Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`).

Bounding the linearity defect `δ` of a strategy's averaged marginals by its winning probability in
the linearity test ([Natarajan and Vidick, §3, Theorem 11][NatarajanVidick2017]) is tracked in
cslib-community/cslib-frontier#6149.

## Main results

* `Cslib.Quantum.exists_isProjective_charObs_of_linear`: rounding to exactly linear unitaries.
* `Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`: the same for one party of a
  tensor-product strategy.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

variable {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
  [DecidableEq n]

/-- **Rounding approximately linear observables**, a same-space variant of
[Natarajan and Vidick, §3, Theorem 10][NatarajanVidick2017] with constant `40`. If the `±1`
observables `A(a)` on `ℂ^ι` satisfy `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`, then a projective
measurement `P` on `ℂ^ι` has unitary, exactly linear character observables with
`E_a ‖A(a) - χ_P(a)‖²_φ ≤ 40δ`. -/
theorem exists_isProjective_charObs_of_linear (φ : AlgState (Matrix ι ι ℂ))
    (A : (n → Bool) → Matrix ι ι ℂ) (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1)
    {δ : ℝ} (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (A a - P.charObs a) ^ 2 ≤ 40 * δ := by
  set B := fourierMeasurement A hA hA2
  have hB : 1 - 2 * δ ≤ ∑ u, (φ (B.effect u * B.effect u)).re :=
    one_sub_le_sum_fourierMeasurement_sq hA hA2 φ hδ
  obtain ⟨P, hP, hU, hmul, hBP⟩ := Measurement.exists_isProjective_charObs φ B hB
  refine ⟨P, hP, hU, hmul, ?_⟩
  have hAB : 𝔼 a, φ.norm (A a - B.charObs a) ^ 2 ≤ 2 * δ :=
    expect_norm_sub_walshSum_sq_le hA hA2 φ hδ
  have hpt : ∀ a, φ.norm (A a - P.charObs a) ^ 2 ≤
      2 * φ.norm (A a - B.charObs a) ^ 2 + 2 * φ.norm (B.charObs a - P.charObs a) ^ 2 := by
    intro a
    have h := φ.norm_add_le (A a - B.charObs a) (B.charObs a - P.charObs a)
    rw [sub_add_sub_cancel] at h
    nlinarith [φ.norm_nonneg (A a - P.charObs a), φ.norm_nonneg (A a - B.charObs a),
      φ.norm_nonneg (B.charObs a - P.charObs a),
      sq_nonneg (φ.norm (A a - B.charObs a) - φ.norm (B.charObs a - P.charObs a))]
  calc 𝔼 a, φ.norm (A a - P.charObs a) ^ 2
      ≤ 𝔼 a, (2 * φ.norm (A a - B.charObs a) ^ 2 + 2 * φ.norm (B.charObs a - P.charObs a) ^ 2) :=
        expect_le_expect fun a _ => hpt a
    _ = 2 * 𝔼 a, φ.norm (A a - B.charObs a) ^ 2 + 2 * 𝔼 a, φ.norm (B.charObs a - P.charObs a) ^ 2 :=
        by rw [expect_add_distrib, ← mul_expect, ← mul_expect]
    _ ≤ 40 * δ := by linarith

/-- **Rounding for one party of a tensor-product strategy.** If the first party's `±1` observables
`A(a)` on `ℂ^ι` satisfy `E_{a,b} Re φ(A(a) A(b) A(a + b) ⊗ 1) ≥ 1 - δ` in the joint state `φ`,
then a projective measurement `P` on `ℂ^ι` has unitary, exactly linear character observables with
`E_a ‖(A(a) - χ_P(a)) ⊗ 1‖²_φ ≤ 40δ`. -/
theorem exists_isProjective_charObs_kroneckerOne_of_linear
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ ((A a * A b * A (a + b)) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * δ := by
  obtain ⟨P, hP, hU, hmul, h⟩ := exists_isProjective_charObs_of_linear
    (φ.comap kroneckerOne (OrderHomClass.mono _)) A hA hA2 hδ
  refine ⟨P, hP, hU, hmul, ?_⟩
  simpa only [AlgState.norm_comap, kroneckerOne_apply] using h

end Cslib.Quantum
