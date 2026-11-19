/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Synchronous
import CslibFrontier.Foundations.Quantum.Algebra.Involution
import CslibFrontier.Foundations.Quantum.Pauli
import CslibFrontier.Probability.PMF.Uniform

/-! # A synchronous strategy from the qubit trace and Pauli measurements -/

set_option linter.privateModule false

namespace CslibFrontierTests.Synchronous

open Cslib.PCP Cslib.Quantum Matrix Finset
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private noncomputable def qubitTrace : AlgState (Matrix Bool Bool ℂ) where
  toFun T := trace T / 2
  map_add' T U := by rw [trace_add, add_div]
  map_smul' c T := by simp [trace_smul, smul_eq_mul, mul_div_assoc]
  monotone' T U h := by
    have htr := (Matrix.le_iff.mp h).trace_nonneg
    have hhalf : (0 : ℂ) ≤ 2⁻¹ := by
      have hp : (0 : ℂ) ≤ ((2⁻¹ : ℝ) : ℂ) := Complex.nonneg_iff.mpr (by simp)
      simpa only [Complex.ofReal_inv, Complex.ofReal_ofNat] using hp
    have hpos := mul_nonneg htr hhalf
    rw [trace_sub, ← div_eq_mul_inv, sub_div, sub_nonneg] at hpos
    exact hpos
  map_one' := by simp [trace_one]

private theorem qubitTrace_isTracial : qubitTrace.IsTracial := by
  intro T U
  change trace (T * U) / 2 = trace (U * T) / 2
  rw [trace_mul_comm]

private noncomputable def pauliMeasurement : Bool → Measurement Bool (Matrix Bool Bool ℂ)
  | false => Measurement.ofInvolution pauliZ_isHermitian.isSelfAdjoint pauliZ_mul_self
  | true => Measurement.ofInvolution pauliX_isHermitian.isSelfAdjoint pauliX_mul_self

private theorem pauliMeasurement_isProjective (x : Bool) : (pauliMeasurement x).IsProjective := by
  cases x
  · exact Measurement.isProjective_ofInvolution pauliZ_isHermitian.isSelfAdjoint pauliZ_mul_self
  · exact Measurement.isProjective_ofInvolution pauliX_isHermitian.isSelfAdjoint pauliX_mul_self

private noncomputable def strategy := CommutingStrategy.ofTracial qubitTrace
  qubitTrace_isTracial pauliMeasurement

private theorem strategy_isSynchronous : strategy.IsSynchronous :=
  CommutingStrategy.ofTracial_isSynchronous _ _ _ pauliMeasurement_isProjective

/-- The two basis measurements in the same algebra do not commute. -/
example :
    ¬Commute ((pauliMeasurement false).effect false) ((pauliMeasurement true).effect false) := by
  intro hc
  have h := congrFun (congrFun hc.eq false) true
  change (signProj pauliZ false * signProj pauliX false) false true =
    (signProj pauliX false * signProj pauliZ false) false true at h
  norm_num [signProj, Cslib.BitString.signVal_false, Fintype.sum_bool,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply] at h

/-- The tracial realization gives unbiased independent outcomes on the two different
Pauli bases. The same strategy answers synchronously on each individual basis. -/
example : strategy.IsSynchronous ∧ strategy.prob false true false false = 1 / 4 := by
  refine ⟨strategy_isSynchronous, ?_⟩
  apply Complex.ofReal_injective
  rw [strategy, CommutingStrategy.ofTracial_prob]
  change trace (signProj pauliZ false * signProj pauliX false) / (2 : ℂ) = _
  norm_num [signProj, Cslib.BitString.signVal_false, Matrix.trace,
    Fintype.sum_bool, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply]

/-- The generated algebra of the realized strategy also carries a trace, so the
construction can be followed by recovery of a tracial state in the game API. -/
example : strategy.aliceState.IsTracial :=
  strategy_isSynchronous.aliceState_isTracial

/-- The projective realization can be recovered inside Alice's generated algebra. -/
example :
    ∃ P : Bool → Measurement Bool strategy.aliceAlgebra,
      (∀ x, (P x).IsProjective) ∧
      ∀ x y a b, (strategy.prob x y a b : ℂ) =
        strategy.aliceState ((P x).effect a * (P y).effect b) :=
  strategy_isSynchronous.exists_aliceState_projective fun x =>
    (CommutingStrategy.ofTracial_isProjective _ _ _ pauliMeasurement_isProjective x).1

/-- Trace recovery and the GNS constructor preserve all probabilities in a round trip. -/
example (x y a b : Bool) :
    (CommutingStrategy.ofTracial strategy.aliceState strategy_isSynchronous.aliceState_isTracial
      strategy.aliceMeasurements).prob x y a b = strategy.prob x y a b := by
  apply Complex.ofReal_injective
  rw [CommutingStrategy.ofTracial_prob, CommutingStrategy.aliceState_apply]
  change strategy.state (strategy.aliceAlgebra.subtype (_ * _)) = _
  rw [map_mul]
  simpa only [StarSubalgebra.subtype_apply, CommutingStrategy.aliceMeasurements_effect] using
    (strategy_isSynchronous.ofReal_prob_eq_state_alice x y a b).symm

private noncomputable def equalityGame : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts x y a b := x = y → a = b

/-- The tracial realization also plays a game through the existing commuting-strategy API. -/
example : equalityGame.commutingWinProb strategy = 1 := by
  classical
  have h (x y : Bool) : (∑ a, ∑ b, if equalityGame.accepts x y a b then
      strategy.prob x y a b else 0) = 1 := by
    refine (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_).trans (strategy.sum_prob x y)
    by_cases he : equalityGame.accepts x y a b
    · exact ite_eq_left he
    · have hxy : x = y := Classical.byContradiction fun hxy => he (fun h => (hxy h).elim)
      subst y
      have hab : a ≠ b := fun hab => he (fun _ => hab)
      rw [ite_eq_right he, strategy_isSynchronous x a b hab]
  rw [TwoProverGame.commutingWinProb_eq_sum]
  simp only [h, mul_one]
  norm_num [ equalityGame, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_bool]

end CslibFrontierTests.Synchronous
