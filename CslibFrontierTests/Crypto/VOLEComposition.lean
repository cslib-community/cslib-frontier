/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.AnonymousToken.RandomTarget
public import CslibFrontier.Crypto.Protocols.UOV.Games
public import CslibFrontier.Crypto.Protocols.UOV.Attacks

/-!
# Top-down clients of the credential and UOV game interfaces

The MQ client concatenates the two structured target blocks into the actual vector codomain
of the ideal UOV scheme. It uses the same optional-preimage certifier as the IHAT random-target
client in `AnonymousTokenRandomTarget`. The displayed ACT bound is the generic finite extracted
certificate partition; raw-target EUF-CMA is not assumed to hold for UOV.

The second client checks an exact attack probability with signer failures. A simple certifier
refuses one of two target values. The one-query collision strategy then succeeds with probability
one quarter, so silently assuming perfect oracle correctness would give the wrong answer.
-/

public section

namespace CslibFrontierTests.Crypto.VOLEComposition

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken
open Probability
open scoped NNReal

/-- Concatenate the ACT-MQ blocks for a UOV map with `k + g` output coordinates. -/
def mqTarget {F Opening : Type} [Field F] {k g : Nat}
    (front : Opening → Fin k → F) (tail : Opening → Fin g → F)
    (message : Fin k → F) (opening : Opening) : Fin (k + g) → F :=
  let blocks := UOV.structuredTarget front tail message opening
  Fin.append blocks.1 blocks.2

/-- The structured ACT target and ideal UOV optional-preimage scheme compose through the same
finite certification reduction as other target encoders. This assumes no target hardness. -/
theorem actMq_extracted_partition {F Opening : Type} [Field F] [Fintype F] [DecidableEq F]
    {v k g : Nat}
    (derive : UOV.IdealKeyMaterial F v (k + g) → (Fin (k + g) → F) →
      ProbComp (Option (Fin (v + (k + g)) → F)))
    (front : Opening → Fin k → F) (tail : Opening → Fin g → F)
    (A : ExtractedForger
      (MultivariateQuadraticMap F (Fin (v + (k + g))) (Fin (k + g)))
      (Fin k → F) Opening (Option (Fin (v + (k + g)) → F))) :
    Experiment.succProbability
      (extractedExperiment (UOV.idealRawScheme derive) (mqTarget front tail) A) ≤
    Experiment.succProbability ((UOV.idealRawScheme derive).eufCmaExperiment
      (targetForger (mqTarget front tail) A)) +
    Experiment.succProbability
      (bindingExperiment (UOV.idealRawScheme derive) (mqTarget front tail) A) :=
  extracted_succProbability_le _ _ _

/-- A small certifier whose failure probability is observable in its game. -/
def refusesTrue : Signature.Scheme Unit Unit Bool (Option Bool) where
  keyGen := pure ((), ())
  sign _ target := pure (if target then none else some false)
  verify _ target signature := match signature with
    | none => false
    | some answer => decide (answer = target)

/-- Retaining failed replies gives success `1/4`, rather than the collision probability `1/2`. -/
theorem collisionAttack_with_failures :
    Experiment.succProbability
        (Signature.oneMoreExperiment refusesTrue
          (fun _ => ProbComp.uniform (Fin 2 → Bool)) 1 Signature.collisionAttack) =
      1 / 4 := by
  have hfunctional : ∀ pk y z s,
      refusesTrue.verify pk y s = true → refusesTrue.verify pk z s = true → y = z := by
    intro pk y z s hy hz
    cases s with
    | none => simp [refusesTrue] at hy
    | some answer =>
      simp only [refusesTrue, decide_eq_true_eq] at hy hz
      exact hy.symm.trans hz
  rw [Signature.succProbability_collisionAttack_uniform refusesTrue hfunctional]
  norm_num [Signature.signingCorrectnessExperiment, refusesTrue, Experiment.succProbability,
    Game.succProbability, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_bool, ENNReal.toNNReal_ofNat]

end CslibFrontierTests.Crypto.VOLEComposition
