/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.GameAlgebraPerfect
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
  rw [CommutingStrategy.ofTracial_prob]
  exact (strategy_isSynchronous.ofReal_prob_eq_aliceState x y a b).symm

private noncomputable def equalityGame : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts x y a b := x = y → a = b

private theorem equalityGame_isSynchronous : equalityGame.IsSynchronous :=
  fun _ _ _ hab h => hab (h rfl)

private theorem strategy_isPerfect : equalityGame.IsPerfectCommuting strategy := by
  intro x y a b hr
  by_cases hxy : x = y
  · subst y
    exact strategy_isSynchronous x a b fun hab => hr (fun _ => hab)
  · exact (hr fun h => (hxy h).elim).elim

/-- A pointwise perfect strategy has score one under the verifier's distribution. -/
example : equalityGame.commutingWinProb strategy = 1 :=
  strategy_isPerfect.commutingWinProb_eq_one equalityGame

/-- With full support, a score of one forces every rejected tuple to have probability zero. -/
example (h : equalityGame.commutingWinProb strategy = 1) :
    equalityGame.IsPerfectCommuting strategy :=
  (equalityGame.commutingWinProb_eq_one_iff_isPerfectCommuting strategy
    fun x y => Cslib.Probability.PMF.mem_support_uniformOfFintype (x, y)).mp h

/-- Recover a faithful tracial representation from the qubit strategy and use its GNS strategy
to score one in the original game. -/
example :
    ∃ (C : Type) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C),
      ∃ S : CommutingStrategy Bool Bool Bool Bool C, equalityGame.commutingWinProb S = 1 := by
  rcases (equalityGame.exists_isPerfectCommuting_iff equalityGame_isSynchronous).mp
    ⟨_, inferInstance, inferInstance, inferInstance, strategy, strategy_isPerfect⟩ with
      ⟨C, _, _, _, τ, hτ, _, ⟨π⟩⟩
  have h := TwoProverGame.GameAlgebra.isPerfectCommuting_ofTracial equalityGame π τ hτ
  exact ⟨_, inferInstance, inferInstance, inferInstance, _,
    h.commutingWinProb_eq_one equalityGame⟩

private noncomputable def rejectAll : TwoProverGame Unit Unit Unit Unit where
  questions := PMF.pure ((), ())
  accepts _ _ _ _ := False

/-- Rejecting every answer forces the lone generator to be zero and one. -/
example (π : rejectAll.GameAlgebra →⋆ₐ[ℂ] ℂ) : False := by
  let e := TwoProverGame.GameAlgebra.effect rejectAll () ()
  have hzero : e = 0 :=
    (TwoProverGame.GameAlgebra.effect_mul_self rejectAll () ()).symm.trans
      (TwoProverGame.GameAlgebra.effect_mul_eq_zero_of_rejected rejectAll () () () () id)
  have hone : e = 1 := by
    simpa only [Fintype.sum_unique] using TwoProverGame.GameAlgebra.sum_effect rejectAll ()
  exact zero_ne_one (by simpa only [map_zero, map_one] using congrArg π (hzero.symm.trans hone))

end CslibFrontierTests.Synchronous
