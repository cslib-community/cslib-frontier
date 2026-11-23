/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LinearitySoundness

/-! # Soundness of the linearity test for tensor-product strategies

Checked client: every tensor-product strategy, projective or not, that the linearity-test
verifier accepts with probability `1 - ε` has exactly linear unitaries on the point player's
dilated factor, close to its observables. With `ε = 0` the bound is `0`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearitySoundness

open Cslib Cslib.PCP Cslib.Quantum Finset Matrix
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

/-- **Soundness**, for every tensor-product strategy. -/
example {n ι κ : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ]
    (S : QuantumStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) ι κ) {ε : ℝ}
    (hε : 1 - ε ≤ S.toCommuting.linearityTestProb) :
    ∃ P : Measurement (n → Bool) (Matrix (ι × Bool) (ι × Bool) ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix (ι × Bool) (ι × Bool) ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 c, (AlgState.vector (S.dilate false (false, false)).state
          (S.dilate false (false, false)).norm_state).norm
        ((((S.dilate false (false, false)).alice c).toMeasurement.observable - P.charObs c) ⊗ₖ
          (1 : Matrix (κ × (Bool × Bool)) (κ × (Bool × Bool)) ℂ)) ^ 2 ≤
        40 * (6 * ε + 2 * √(12 * ε)) :=
  QuantumStrategy.exists_isProjective_charObs_of_linearityTest S hε

/-- **Perfect strategies**: winning with probability `1` gives zero average distance. -/
example {n ι κ : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ]
    (S : QuantumStrategy (n → Bool) ((n → Bool) × (n → Bool)) Bool (Bool × Bool) ι κ)
    (h : S.toCommuting.linearityTestProb = 1) :
    ∃ P : Measurement (n → Bool) (Matrix (ι × Bool) (ι × Bool) ℂ), P.IsProjective ∧
      𝔼 c, (AlgState.vector (S.dilate false (false, false)).state
          (S.dilate false (false, false)).norm_state).norm
        ((((S.dilate false (false, false)).alice c).toMeasurement.observable - P.charObs c) ⊗ₖ
          (1 : Matrix (κ × (Bool × Bool)) (κ × (Bool × Bool)) ℂ)) ^ 2 ≤ 0 := by
  obtain ⟨P, hP, -, -, hb⟩ :=
    QuantumStrategy.exists_isProjective_charObs_of_linearityTest (ε := 0) S (by rw [h]; norm_num)
  exact ⟨P, hP, by simpa using hb⟩

end CslibFrontierTests.LinearitySoundness
