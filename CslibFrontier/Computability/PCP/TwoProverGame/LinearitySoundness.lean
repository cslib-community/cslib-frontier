/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Linearity
public import CslibFrontier.Computability.PCP.TwoProverGame.Naimark
public import CslibFrontier.Foundations.Quantum.LinearityRounding

/-!
# Soundness of the linearity test for tensor-product strategies

Every tensor-product strategy that the linearity-test verifier accepts with probability `1 - ε`
(`Cslib.PCP.CommutingStrategy.linearityTestProb`, through `Cslib.PCP.QuantumStrategy.toCommuting`)
has, on the point player's factor, exactly linear unitary observables
close to its own (`Cslib.PCP.QuantumStrategy.exists_isProjective_charObs_of_linearityTest`):

`E_c ‖(A(c) - χ(c)) ⊗ 1‖²_ψ ≤ 40 (6ε + 2√(12ε))`,

where `A(c)` are the point player's observables after Naimark dilation and `χ` are the character
observables of a projective measurement on the point player's dilated space.

The proof composes three steps:

* the Naimark dilation (`Cslib.PCP.QuantumStrategy.dilate`) makes the strategy projective without
  changing its acceptance probability (`Cslib.PCP.QuantumStrategy.linearityTestProb_dilate`);
* passing the test makes the point player's observables linear on average
  (`Cslib.PCP.CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest`);
* the same-space rounding (`Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`)
  gives exactly linear observables on the point player's factor.

This combines the commuting-operator, point-player form of
[Natarajan and Vidick, §3, Theorem 11][NatarajanVidick2017] (arXiv:1610.03574v1) with the
same-space variant of their Theorem 10, for the asymmetric game of
`CslibFrontier/Computability/PCP/TwoProverGame/Linearity.lean`. As in the source, the observables
act on the dilated space with an ancilla, here the one introduced by the Naimark dilation of the
strategy. The constants are not optimized. The remaining steps toward Pauli rigidity are tracked in
cslib-community/cslib-frontier#6149.

## Main results

* `Cslib.PCP.QuantumStrategy.linearityTestProb_dilate`: the dilation is accepted with the same
  probability.
* `Cslib.PCP.QuantumStrategy.exists_isProjective_charObs_of_linearityTest`: soundness of the
  linearity test for tensor-product strategies.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.PCP

open Matrix Finset Quantum
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

namespace QuantumStrategy

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- The Naimark dilation of a strategy is accepted by the linearity-test verifier with the same
probability. -/
theorem linearityTestProb_dilate
    (S : QuantumStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) ι κ) (a₀ : Bool)
    (b₀ : Bool × Bool) :
    (S.dilate a₀ b₀).toCommuting.linearityTestProb = S.toCommuting.linearityTestProb := by
  simp only [CommutingStrategy.linearityTestProb, prob_toCommuting, prob_dilate]

/-- **Soundness of the linearity test** for tensor-product strategies. If the linearity-test
verifier accepts `S` with probability at least `1 - ε`, then after Naimark dilation a projective
measurement `P` on the point player's space has unitary, exactly linear character observables with
`E_c ‖(A(c) - χ_P(c)) ⊗ 1‖²_ψ ≤ 40 (6ε + 2√(12ε))` for the point player's observables `A(c)`. -/
theorem exists_isProjective_charObs_of_linearityTest
    (S : QuantumStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) ι κ) {ε : ℝ}
    (hε : 1 - ε ≤ S.toCommuting.linearityTestProb) :
    ∃ P : Measurement (n → Bool) (Matrix (ι × Bool) (ι × Bool) ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix (ι × Bool) (ι × Bool) ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 c, (AlgState.vector (S.dilate false (false, false)).state
          (S.dilate false (false, false)).norm_state).norm
        ((((S.dilate false (false, false)).alice c).toMeasurement.observable - P.charObs c) ⊗ₖ
          (1 : Matrix (κ × (Bool × Bool)) (κ × (Bool × Bool)) ℂ)) ^ 2 ≤
        40 * (6 * ε + 2 * √(12 * ε)) := by
  classical
  set S' := S.dilate false (false, false)
  set T := S'.toCommuting
  have hwin : 1 - ε ≤ T.linearityTestProb := by
    rw [linearityTestProb_dilate]
    exact hε
  have hA : ∀ c, (T.alice c).IsProjective := fun c a => by
    change (S'.alice c).effect a ⊗ₖ 1 * (S'.alice c).effect a ⊗ₖ 1 = (S'.alice c).effect a ⊗ₖ 1
    rw [← mul_kronecker_mul, Matrix.mul_one]
    exact congrArg (· ⊗ₖ (1 : Matrix (κ × (Bool × Bool)) _ ℂ))
      (S.isProjective_alice_dilate false (false, false) c a)
  have hB : ∀ q, (T.bob q).IsProjective := fun q r => by
    change 1 ⊗ₖ (S'.bob q).effect r * 1 ⊗ₖ (S'.bob q).effect r = 1 ⊗ₖ (S'.bob q).effect r
    rw [← mul_kronecker_mul, Matrix.mul_one]
    exact congrArg ((1 : Matrix (ι × Bool) _ ℂ) ⊗ₖ ·)
      (S.isProjective_bob_dilate false (false, false) q r)
  have hlin := CommutingStrategy.one_sub_le_expect_re_apply_mul_mul_of_linearityTest T hA hB hwin
  set O : (n → Bool) → Matrix (ι × Bool) (ι × Bool) ℂ := fun c =>
    (S'.alice c).toMeasurement.observable
  have hobs : ∀ c, (T.alice c).observable = O c ⊗ₖ 1 := fun c => by
    change (S'.alice c).effect false ⊗ₖ 1 - (S'.alice c).effect true ⊗ₖ 1 = _
    rw [← kroneckerOne_apply, ← kroneckerOne_apply, ← map_sub, kroneckerOne_apply]
    rfl
  refine exists_isProjective_charObs_kroneckerOne_of_linear T.state O
    (fun c => Measurement.isSelfAdjoint_observable _)
    (fun c => Measurement.observable_mul_self (S.isProjective_alice_dilate false (false, false) c))
    ?_
  have e : ∀ a b, (O a * O b * O (a + b)) ⊗ₖ (1 : Matrix (κ × (Bool × Bool)) _ ℂ) =
      (T.alice a).observable * (T.alice b).observable * (T.alice (a + b)).observable := by
    intro a b
    rw [hobs, hobs, hobs, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.mul_one]
  simp only [e]
  linarith

end QuantumStrategy

end Cslib.PCP
