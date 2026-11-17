/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.OneWay.Repeated
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Sampling.BitString
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Bind

/-!
# Tests for `Cslib.Crypto.OneWay.Repeated`

Client instantiations of `OneWay.repeatedInversion_negligible` under polynomial-time repetition
schedules, a zero-instance boundary check on `repeatedInversionGame`, and a concrete evaluation
comparison against `repeatedInverter` at `dyadicSize 2 = 4`.
-/

public section

namespace CslibFrontierTests.Crypto.OneWayRepeated

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Asymptotic clients -/

theorem repeatedInversion_negligible_two_mul {f : List Bool → List Bool} (hf : OneWay f)
    (adversary : RevealInverter)
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible fun n =>
      Game.succProbability (ProbComp.eval (repeatedInversionGame f (fun n => 2 * n) adversary n)) :=
  hf.repeatedInversion_negligible
    (ComputableInPolyTime.unary_mul' (.const 2) (by fun_prop)) adversary hadversary

theorem repeatedInversion_negligible_sq_add_one {f : List Bool → List Bool} (hf : OneWay f)
    (adversary : RevealInverter)
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible fun n =>
      Game.succProbability
        (ProbComp.eval (repeatedInversionGame f (fun n => n * n + 1) adversary n)) :=
  hf.repeatedInversion_negligible
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (by fun_prop) (by fun_prop)) (.const 1))
    adversary hadversary

/-! ### Zero-instance and concrete evaluation checks -/

theorem succProbability_repeatedInversionGame_zero (f : List Bool → List Bool)
    (adversary : RevealInverter) (n : ℕ) :
    Game.succProbability (ProbComp.eval (repeatedInversionGame f (fun _ => 0) adversary n)) =
      0 := by
  simp [repeatedInversionGame, repeatedInversionExperiment, forgeExperiment,
    OracleComp.replicate_zero, Game.succProbability]

private def guessFirstTrue : RevealInverter := fun _ _ => return ([], [true])

example :
    Game.succProbability
      (ProbComp.eval (repeatedInversionGame (fun _ => []) (fun _ => 2) guessFirstTrue 0)) = 1 := by
  simp [repeatedInversionGame, repeatedInversionExperiment, forgeExperiment, guessFirstTrue,
    RevealInverter.toTyped, requestSlot, ProbOracleComp.runLogWith, ProbOracleComp.runState_pure,
    OracleComp.replicate_succ, OracleComp.replicate_zero, ProbComp.eval_bind,
    BitString.eval_sampleList, BitString.uniformList_zero, Game.succProbability]

example :
    Game.succProbability
      (ProbComp.eval (repeatedInversionGame id (fun _ => 2) guessFirstTrue 1)) = 1 / 2 := by
  simp only [repeatedInversionGame, repeatedInversionExperiment, forgeExperiment, guessFirstTrue,
    RevealInverter.toTyped, requestSlot, ProbOracleComp.runLogWith, ProbOracleComp.runState_map,
    ProbOracleComp.runState_pure, OracleComp.replicate_succ, OracleComp.replicate_zero,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, BitString.eval_sampleList,
    BitString.uniformList_succ, BitString.uniformList_zero, PMF.bind_map, PMF.bind_bind,
    PMF.pure_bind, Game.succProbability]
  simp [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [ENNReal.toNNReal_ofNat]

example :
    Game.succProbability
      (ProbComp.eval (inversionGame id (repeatedInverter id (fun _ => 2) guessFirstTrue) 1)) =
      1 / 8 := by
  have hdy : dyadicSize 2 = 4 := by decide
  have hsum (f : Fin (dyadicSize 2) → ENNReal) :
      (∑ a : Fin (dyadicSize 2), f a) = ∑ i : Fin 4, f (Fin.cast hdy.symm i) :=
    Fintype.sum_equiv (finCongr hdy) f (fun i => f (Fin.cast hdy.symm i)) fun _ => rfl
  simp only [inversionGame, inversionExperiment, repeatedInverter, ProbComp.eval_bind,
    ProbComp.eval_sampleDyadicIndex, BitString.eval_sampleList, BitString.uniformList_succ,
    BitString.uniformList_zero, PMF.bind_map, PMF.bind_bind, PMF.pure_bind,
    ProbComp.eval_pure, Game.succProbability, PMF.bind_apply, PMF.uniformOfFintype_apply,
    Fintype.card_bool, tsum_fintype, Fintype.sum_bool, Function.comp_apply]
  rw [hsum, hsum]
  simp only [Fin.sum_univ_four, Fintype.card_fin, hdy]
  simp [slotInverter, guessFirstTrue, RevealInverter.toTyped, requestSlot,
    OracleComp.replicate_succ, OracleComp.replicate_zero]
  norm_num [ENNReal.toNNReal_ofNat]

end CslibFrontierTests.Crypto.OneWayRepeated
