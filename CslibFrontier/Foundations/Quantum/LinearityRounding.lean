/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.FourierMeasurement
public import CslibFrontier.Foundations.Quantum.LocalOrthogonalization
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Order
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Foundations.Quantum.Algebra.Expect

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

The same-space construction extends to self-adjoint contractions with error `48δ`.
The Fourier squares can have total mass below the identity. Distributing the remaining
effect equally among the outcomes gives a measurement that is still nearly projective.

## Main results

* `Cslib.Quantum.exists_isProjective_charObs_of_linear`: rounding to exactly linear unitaries.
* `Cslib.Quantum.exists_isProjective_charObs_of_linear_contractions`: rounding self-adjoint
  contractions on the original matrix space.
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
  linarith only [φ.expect_norm_sub_sq_le_through univ A B.charObs P.charObs, hAB, hBP]

open Cslib.BitString in
/-- Near-linear self-adjoint contractions on a finite complex matrix space admit a
projective character measurement on the same space. The error is independent of
the number of bit strings and the matrix dimension. -/
theorem exists_isProjective_charObs_of_linear_contractions
    (φ : AlgState (Matrix ι ι ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hcontract : ∀ a, A a * A a ≤ 1)
    {δ : ℝ} (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (A a - P.charObs a) ^ 2 ≤ 48 * δ := by
  classical
  let D (u : n → Bool) := fourierCoeff A u * fourierCoeff A u
  have hTotal : ∑ u, D u ≤ 1 := by
    dsimp only [D]
    rw [sum_fourierCoeff_mul_self_eq]
    have hscale : (((Fintype.card (n → Bool) : ℚ≥0)⁻¹ : ℚ≥0) : ℝ) =
        ((2 : ℝ) ^ Fintype.card n)⁻¹ := by
      rw [NNRat.cast_inv, Fintype.card_fun, Fintype.card_bool]
      push_cast
      rfl
    rw [← hscale, NNRat.cast_smul_eq_nnqsmul ℝ]
    change (𝔼 a, A a * A a) ≤ 1
    simpa only [Fintype.expect_const] using
      (expect_le_expect (s := (univ : Finset (n → Bool))) fun a _ => hcontract a)
  let H := ∑ u, D u
  let R := (1 : Matrix ι ι ℂ) - H
  let w : ℝ := (Fintype.card (n → Bool) : ℝ)⁻¹
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Fintype.card_pos (α := n → Bool)
  have hcount : ∑ _ : n → Bool, w = 1 := by
    simp [w]
  have hH : 0 ≤ H := sum_nonneg fun u _ => fourierCoeff_mul_self_nonneg hA u
  have hR : 0 ≤ R := sub_nonneg.mpr hTotal
  let B : Measurement (n → Bool) (Matrix ι ι ℂ) :=
    { effect := fun u => D u + w • R
      nonneg := fun u => add_nonneg (fourierCoeff_mul_self_nonneg hA u) (smul_nonneg hw0 hR)
      sum_effect := by
        change ∑ u, (D u + w • R) = 1
        rw [sum_add_distrib, ← sum_smul, hcount, one_smul]
        change H + (1 - H) = 1
        abel }
  obtain ⟨hmass, hfourth⟩ := one_sub_le_fourierCoeff_moments_of_linear hA φ hTotal hδ
  have hsq : ∑ u, B.effect u * B.effect u = (∑ u, D u * D u) + w • (1 - H * H) := by
    have he (u : n → Bool) : B.effect u * B.effect u =
        D u * D u + w • (D u * R) + w • (R * D u) + (w * w) • (R * R) := by
      simp only [B, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add,
        ← mul_smul]
      abel
    have hlast : (∑ _ : n → Bool, (w * w) • (R * R)) = w • (R * R) := by
      simp only [mul_smul]
      rw [← sum_smul, hcount, one_smul]
    simp only [he, sum_add_distrib, hlast, ← smul_sum, ← sum_mul, ← mul_sum,
      add_assoc, ← smul_add]
    have hRem : H * R + (R * H + R * R) = 1 - H * H := by
      dsimp only [R]
      noncomm_ring
    rw [hRem]
  have hB : 1 - 2 * δ ≤ ∑ u, (φ (B.effect u * B.effect u)).re := by
    rw [← Complex.re_sum, ← map_sum, hsq]
    rw [← Complex.re_sum, ← map_sum] at hfourth
    exact hfourth.trans (φ.re_apply_mono (le_add_of_nonneg_right
      (smul_nonneg hw0 (sub_nonneg.mpr ((mul_self_le_self_of_nonneg_of_le_one hH hTotal).trans
        hTotal)))))
  obtain ⟨P, hP, hU, hmul, hBP⟩ := Measurement.exists_isProjective_charObs φ B hB
  refine ⟨P, hP, hU, hmul, ?_⟩
  have hRnorm : φ.norm R ^ 2 ≤ δ := by
    rw [φ.norm_sq, hR.isSelfAdjoint.star_eq]
    refine (φ.re_apply_mono (mul_self_le_self_of_nonneg_of_le_one hR ?_)).trans ?_
    · exact sub_le_self _ hH
    · change (φ (1 - ∑ u, D u)).re ≤ δ
      rw [map_sub, AlgState.map_one, Complex.sub_re, Complex.one_re]
      linarith only [hmass]
  have hcompletion : 𝔼 a, φ.norm (walshSum D a - B.charObs a) ^ 2 ≤ δ := by
    have he (a : n → Bool) : walshSum D a - B.charObs a = walshSum (fun _ => -(w • R)) a := by
      rw [Measurement.charObs_eq_observable_map, Measurement.observable_map]
      change walshSum D a - walshSum (fun u => D u + w • R) a = _
      rw [walshSum_sub]
      congr 1
      funext u
      change D u - (D u + w • R) = _
      abel
    simp only [he, expect_norm_walshSum_sq, AlgState.norm_neg, ← Complex.coe_smul,
      AlgState.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0, mul_pow]
    rw [pow_two w, mul_assoc, ← sum_mul, hcount, one_mul]
    exact (mul_le_of_le_one_left (sq_nonneg _) hw1).trans hRnorm
  have hD := expect_norm_sub_walshSum_sq_le_of_contractions hA φ hTotal hδ
  have hAB : 𝔼 a, φ.norm (A a - B.charObs a) ^ 2 ≤ 6 * δ := by
    linarith only [φ.expect_norm_sub_sq_le_through univ A (walshSum D) B.charObs, hD, hcompletion]
  linarith only [φ.expect_norm_sub_sq_le_through univ A B.charObs P.charObs, hAB, hBP]

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
