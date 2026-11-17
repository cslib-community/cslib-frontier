/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.RotationStrategy
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Checked clients of the rotation strategy for CHSH (Arora–Barak, January 2007 draft,
Theorem 20.16): measuring after a rotation is measuring the rotated state, the correlations on
questions `(0, 0)` and `(1, 1)`, the `0.8` bound and the gap to the optimum `cos²(π/8)`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CHSHRotationStrategy

open Matrix Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open scoped Real

-- Measuring after a rotation by `θ` is measuring the rotated state: on `|0⟩` the outcome `0` has
-- probability `cos² θ`.
example (θ : ℝ) : (chshRotatedMeasurement θ).prob (ket false) false = Real.cos θ ^ 2 := by
  rw [chshRotatedMeasurement, POVM.prob_comap, POVM.prob_basis]
  simp only [mulVec, dotProduct, Fintype.univ_bool, chshRotation, Bool.false_eq,
    ↓reduceIte, ket, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_insert, Finset.mem_singleton, or_true]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

-- The answers always agree on questions `(0, 0)`, and are uncorrelated on `(1, 1)`.
example : chshRotationStrategy.correlation false false = 1 ∧
    chshRotationStrategy.correlation true true = 0 := by
  simp only [correlation_chshRotationStrategy, Bool.cond_true, Bool.cond_false]
  refine ⟨by simp, ?_⟩
  rw [show 2 * (π / 8 - -(π / 8)) = π / 2 by ring, Real.cos_pi_div_two]

-- Theorem 20.16: the strategy beats the classical value `3/4`.
example : chsh.value < chsh.quantumWinProb chshRotationStrategy := by
  rw [value_chsh]
  linarith [four_div_five_le_quantumWinProb_chsh_chshRotationStrategy]

-- The rotation strategy is not optimal: it wins with probability below `cos²(π/8)`.
example : chsh.quantumWinProb chshRotationStrategy < chsh.quantumValue := by
  rw [quantumWinProb_chsh_chshRotationStrategy, quantumValue_chsh, Real.cos_sq_pi_div_eight]
  nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

end CslibFrontierTests.CHSHRotationStrategy
