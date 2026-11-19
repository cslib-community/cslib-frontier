/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT

/-!
# Shared nonvacuity fixtures for prime-order group families

Exports `guessZero` (constant discrete-logarithm guesser) and `identityTest` / `not_ddh_const`
(identity-element DDH distinguisher and fixed-group DDH failure), together with their uniform
strict-PPT certificates and exact success probabilities, for both non-module and `module` test
clients.
-/

public section

namespace CslibFrontierTests.Crypto.PrimeOrderGroupFixture

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-! ### Discrete logarithm constant guesser -/

/-- Always guess the exponent `0`. -/
noncomputable def guessZero : ℕ → F.Desc × List Bool → ProbComp (List Bool) :=
  fun _ _ => pure []

/-- Guessing `0` is uniform strict PPT: it is a constant. -/
theorem guessZero_isPPT : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
    (fun input => guessZero F input.1 input.2) :=
  (ComputableInPolyTime.const _).isPPTOn

/-- Guessing `0` against a fixed group of order `q` succeeds with probability exactly `1 / q`. -/
theorem succProbability_discreteLogGame_guessZero (n : ℕ) :
    Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) (guessZero F) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  have h := PMF.uniformOfFintype_bind_decide_eq_apply_true (0 : ZMod (F.order d))
  rw [ZMod.card] at h
  simp only [discreteLogGame, guessZero, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind] at h ⊢
  simp only [ofBits, List.foldr_nil, Nat.cast_zero]
  rw [Game.succProbability, h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-! ### DDH identity test and fixed-group failure -/

/-- Accept when the first and third elements of a DDH tuple are both the identity. -/
noncomputable def identityTest : F.DDHDistinguisher :=
  fun _ _ u _ w => pure (decide (u = 0) && decide (w = 0))

/-- `identityTest` is uniform strict PPT. -/
theorem identityTest_isPPT : (identityTest F).IsPPT := by
  refine (ComputableInPolyTime.isPPTOn (f := fun x : F.DDHInput =>
    decide (F.encode x.groupParameters x.leftPublic = F.encode x.groupParameters 0) &&
      decide (F.encode x.groupParameters x.candidateShared = F.encode x.groupParameters 0))
    (by fun_prop)).congr fun x => ?_
  simp only [identityTest, (F.encode_injective _).eq_iff]

/-- In the real game, `identityTest` succeeds exactly when `α = 0`, with probability `1 / q`. -/
theorem succProbability_ddhRealGame_identityTest (n : ℕ) :
    Game.succProbability (F.ddhRealGame (fun _ => PMF.pure d) (identityTest F) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  simp only [ddhRealGame, Game.withSetup_pure, eval_ddhRealExperiment, identityTest,
    ProbComp.eval_pure, smul_eq_zero, F.generator_ne_zero, or_false,
    mul_eq_zero, ← Bool.decide_and, and_or_left, and_self, or_iff_left_of_imp And.left,
    PMF.bind_const]
  rw [Game.succProbability, PMF.bind_pure_decide_eq_apply_true', PMF.uniformOfFintype_apply,
    ZMod.card, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- In the random game, `identityTest` succeeds exactly when `α = γ = 0`, with probability
`1 / q²`. -/
theorem succProbability_ddhRandomGame_identityTest (n : ℕ) :
    Game.succProbability (F.ddhRandomGame (fun _ => PMF.pure d) (identityTest F) n) =
      (F.order d : ℝ≥0)⁻¹ ^ 2 := by
  simp only [ddhRandomGame, Game.withSetup_pure, eval_ddhRandomExperiment, identityTest,
    ProbComp.eval_pure, smul_eq_zero, F.generator_ne_zero, or_false,
    PMF.bind_const]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    Finset.sum_ite_eq', sq]

/-- Fixed-group real DDH experiment acceptance probability for `identityTest`. -/
theorem succProbability_ddhRealExperiment_identityTest (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (ddhRealExperiment (F.order d) (F.generator d) (identityTest F n d))) =
      (F.order d : ℝ≥0)⁻¹ := by
  simpa only [ddhRealGame, Game.withSetup_pure] using
    succProbability_ddhRealGame_identityTest F d n

/-- Fixed-group random DDH experiment acceptance probability for `identityTest`. -/
theorem succProbability_ddhRandomExperiment_identityTest (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (ddhRandomExperiment (F.order d) (F.generator d) (identityTest F n d))) =
      (F.order d : ℝ≥0)⁻¹ ^ 2 := by
  simpa only [ddhRandomGame, Game.withSetup_pure] using
    succProbability_ddhRandomGame_identityTest F d n

/-- **DDH fails for a fixed group.** -/
theorem not_ddh_const : ¬ F.DDH fun _ => PMF.pure d := by
  intro h
  have hneg := h (identityTest F) (identityTest_isPPT F)
  simp only [Game.advantage, succProbability_ddhRealGame_identityTest,
    succProbability_ddhRandomGame_identityTest] at hneg
  refine not_negligible_const ?_ hneg
  rw [ne_eq, nndist_eq_zero]
  intro heq
  have hq : (2 : ℝ) ≤ F.order d := by exact_mod_cast (F.prime_order d).two_le
  have hr : ((F.order d : ℝ))⁻¹ = ((F.order d : ℝ))⁻¹ ^ 2 := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  field_simp at hr
  nlinarith

end CslibFrontierTests.Crypto.PrimeOrderGroupFixture
