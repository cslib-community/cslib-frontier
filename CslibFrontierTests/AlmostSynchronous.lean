/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronous
import CslibFrontier.Foundations.Quantum.Pauli

/-! # A symmetric Pauli X strategy with nonzero synchrony defect -/

set_option linter.privateModule false

open Cslib.PCP Cslib.Quantum Matrix

private def pureSpectrum (i : Bool) : ℝ := if i then 0 else 1

private theorem pureSpectrum_nonneg (i : Bool) : 0 ≤ pureSpectrum i := by
  cases i <;> norm_num [pureSpectrum]

private theorem sum_pureSpectrum : ∑ i, pureSpectrum i = 1 := by
  norm_num [Fintype.sum_bool, pureSpectrum]

private noncomputable def pauliPOVM (_ : Unit) : POVM Bool Bool :=
  POVM.ofObservable pauliX pauliX_isHermitian pauliX_mul_self

/-- The actual quantum probabilities, summed over equal answers, give agreement one half. -/
example :
    ∑ a, (QuantumStrategy.ofSchmidt pureSpectrum pureSpectrum_nonneg sum_pureSpectrum
      pauliPOVM).prob () () a a = 1 / 2 := by
  simp_rw [QuantumStrategy.prob_ofSchmidt_same]
  rw [Fintype.sum_bool]
  norm_num [Fintype.sum_bool, pureSpectrum, pauliPOVM, Matrix.smul_apply, Matrix.one_apply,
    Matrix.add_apply, Matrix.sub_apply, Complex.norm_mul]

/-- The projective spectral mixture recovers the reduced state of this strategy exactly. -/
example :
    partialTraceRight (pureState
      (QuantumStrategy.ofSchmidt pureSpectrum pureSpectrum_nonneg sum_pureSpectrum pauliPOVM).state)
      = ∑ s : {s : Finset Bool // s.Nonempty},
        QuantumStrategy.spectralCutWeight pureSpectrum s •
          QuantumStrategy.spectralCutDensity s := by
  obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ :=
    QuantumStrategy.exists_projective_spectral_mixture pureSpectrum pureSpectrum_nonneg
      sum_pureSpectrum pauliPOVM (PMF.pure ())
  exact h
