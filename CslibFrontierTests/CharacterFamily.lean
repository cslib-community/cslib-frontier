/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.CharacterFamily
import CslibFrontier.Foundations.Quantum.Orthogonalization
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-! # Character observables of measurements

Checked clients: Parseval in a state, exact linearity of the character observables of projective
measurements, the orthogonalization corollary, and a concrete instance: the character observables
of the computational-basis measurement are the Pauli phase flips `Z^a`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CharacterFamily

open Matrix Cslib Cslib.Quantum Cslib.BitString Finset
open scoped MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

/-- **Parseval in a state.** -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A] [Module ℚ≥0 A]
    (φ : AlgState A) (D : (ι → Bool) → A) :
    𝔼 a, φ.norm (walshSum D a) ^ 2 = ∑ x, φ.norm (D x) ^ 2 :=
  expect_norm_walshSum_sq φ D

/-- **Orthogonalization** gives unitary, exactly linear character observables close to those of
any measurement. -/
example {n κ : Type} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]
    (φ : AlgState (Matrix κ κ ℂ)) (M : Measurement (n → Bool) (Matrix κ κ ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ x, (φ (M.effect x * M.effect x)).re) :
    ∃ P : Measurement (n → Bool) (Matrix κ κ ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix κ κ ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (M.charObs a - P.charObs a) ^ 2 ≤ 9 * ε :=
  Measurement.exists_isProjective_charObs φ M hε

/-- The computational-basis measurement on `n` qubits. -/
noncomputable def basisMeasurement (n : Type) [Fintype n] [DecidableEq n] :
    Measurement (n → Bool) (Matrix (n → Bool) (n → Bool) ℂ) where
  effect x := diagonal (Pi.single x 1)
  nonneg x := by
    rw [nonneg_iff_posSemidef, posSemidef_diagonal_iff]
    intro y
    by_cases h : y = x
    · subst h; simp
    · simp [h]
  sum_effect := by
    ext y z
    simp only [Matrix.sum_apply, diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h; simp [Pi.single_apply]
    · simp

/-- **Concrete client.** The character observables of the computational-basis measurement are the
phase flips `Z^a`. -/
example {n : Type} [Fintype n] [DecidableEq n] (a : n → Bool) :
    (basisMeasurement n).charObs a = pauliZPow a := by
  ext y z
  simp only [Measurement.charObs, walshSum, basisMeasurement, Matrix.sum_apply, Matrix.smul_apply,
    diagonal_apply, pauliZPow_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp [Pi.single_apply]
  · simp

end CslibFrontierTests.CharacterFamily
