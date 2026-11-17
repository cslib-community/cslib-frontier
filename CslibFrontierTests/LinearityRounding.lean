/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.LinearityRounding
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-! # Rounding approximately linear observables

Checked clients: Parseval for the Fourier coefficients, the two estimates for the Fourier
measurement in any state of any star-ordered algebra, and rounding, in one algebra and for one
party of a tensor-product strategy. A concrete instance: the Pauli phase flips `Z^a` are exactly
linear, so their linearity defect is `0` in every state, and rounding finds exactly linear
unitaries at zero average distance in the state's seminorm.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityRounding

open Matrix Cslib Cslib.Quantum Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

/-- **Parseval** for the Fourier coefficients of `±1` observables. -/
example {n R : Type} [Fintype n] [DecidableEq n] [Ring R] [Algebra ℂ R]
    (A : (n → Bool) → R) (hA2 : ∀ a, A a * A a = 1) :
    ∑ u, fourierCoeff A u * fourierCoeff A u = 1 :=
  sum_fourierCoeff_mul_self hA2

/-- **The Fourier measurement**, in any state of any star-ordered algebra: almost projective, and
its characters are close to the observables. -/
example {n R : Type} [Fintype n] [DecidableEq n] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [Algebra ℂ R] [StarModule ℂ R] [SelfAdjointDecompose R]
    (φ : AlgState R) (A : (n → Bool) → R) (hA : ∀ a, IsSelfAdjoint (A a))
    (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    1 - 2 * δ ≤ ∑ u, (φ ((fourierMeasurement A hA hA2).effect u *
      (fourierMeasurement A hA hA2).effect u)).re ∧
    𝔼 a, φ.norm (A a - walshSum (fourierMeasurement A hA hA2).effect a) ^ 2 ≤ 2 * δ :=
  ⟨one_sub_le_sum_fourierMeasurement_sq hA hA2 φ hδ, expect_norm_sub_walshSum_sq_le hA hA2 φ hδ⟩

/-- **Rounding** for one party of a tensor-product strategy. -/
example {ι κ n : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
    [DecidableEq n] (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ ((A a * A b * A (a + b)) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * δ :=
  exists_isProjective_charObs_kroneckerOne_of_linear φ A hA hA2 hδ

/-- **Concrete instance.** The phase flips `Z^a` have linearity defect `0` in every state, so
rounding finds exactly linear unitaries at zero average distance. -/
example {n : Type} [Fintype n] [DecidableEq n] (φ : AlgState (Matrix (n → Bool) (n → Bool) ℂ)) :
    ∃ P : Measurement (n → Bool) (Matrix (n → Bool) (n → Bool) ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix (n → Bool) (n → Bool) ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (pauliZPow a - P.charObs a) ^ 2 ≤ 0 := by
  have hδ : 1 - 0 ≤ 𝔼 a, 𝔼 b,
      (φ (pauliZPow a * pauliZPow b * pauliZPow (a + b))).re := by
    simp only [pauliZPow_mul, BitString.add_self, pauliZPow_zero, φ.map_one, Complex.one_re,
      Fintype.expect_const, sub_zero, le_refl]
  simpa using exists_isProjective_charObs_of_linear φ pauliZPow
    (fun a => (pauliZPow_isHermitian a).isSelfAdjoint) pauliZPow_mul_self hδ

end CslibFrontierTests.LinearityRounding
