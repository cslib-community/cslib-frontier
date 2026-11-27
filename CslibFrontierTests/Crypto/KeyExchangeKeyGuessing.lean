/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.KeyExchange.KeyGuessing
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontierTests.Crypto.PrimeOrderGroupFixture

/-!
# Key-guessing security for anonymous key exchange: checked instances

Checks for `CslibFrontier/Crypto/Computational/KeyExchange/KeyGuessing.lean`:

* `dhToCDHAdversary` and `cdhToDHKeyGuesser` are definitionally mutually inverse.
* For any fixed group of a `PrimeOrderGroupFamily`, both the fair-coin and ideal-sampling
  Diffie–Hellman key-exchange protocols fail `AnonKESecure` via
  `dhKeyExchangeProb_anonKESecure_iff_cdh` and `dhKeyExchange_anonKESecure_iff_cdh_ideal`,
  `CDH.discreteLog`, and the shared constant-guesser fixture `PrimeOrderGroupFixture.guessZero`.
* Over `schnorrGroups`, a concrete group-operation key guesser satisfies `KeyGuesser.IsPPT`.
* The 3-message XOR protocol `KeyExchange.xorKeyExchange` fails `AnonKESecure`: `xorKeyGuesser`
  wins with probability `1` via `KeyExchange.realGame_xorEavesdropper`.
* The half-leaking protocol `halfLeakKE` (which outputs `(x, y)` as the shared key and leaks `x` in
  its transcript) satisfies both `KeyExchange.Correct` and `KeyExchange.AnonKESecure`.
* Without `KeyExchange.Correct` (`splitKE`, where Alice outputs `true` and Bob outputs `false`),
  `anonKEGame` and comparing with Bob's key disagree.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.KeyExchangeKeyGuessing

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily
  CslibFrontierTests.Crypto.PrimeOrderGroupFixture Turing.MultiTapeTM
open scoped ENNReal NNReal

open KeyExchange

/-! ### Mutually inverse Diffie–Hellman / CDH adversary maps -/

example (F : PrimeOrderGroupFamily) (A : F.CDHAdversary) :
    F.dhToCDHAdversary (F.cdhToDHKeyGuesser A) = A :=
  rfl

example (F : PrimeOrderGroupFamily) (A : KeyGuesser F.DHTranscript F.DHKey) :
    F.cdhToDHKeyGuesser (F.dhToCDHAdversary A) = A :=
  rfl

/-! ### Fixed-group Diffie–Hellman nonvacuity and concrete PPT witness -/

example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    ¬ (F.dhKeyExchangeProb fun _ => PMF.pure d).AnonKESecure F.encDHTranscript F.encDHKey := by
  intro h
  have hdl := ((F.dhKeyExchangeProb_anonKESecure_iff_cdh _).mp h).discreteLog
    (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hdl
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hdl

example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    ¬ (F.dhKeyExchange fun _ => PMF.pure d).AnonKESecure F.encDHTranscript F.encDHKey := by
  intro h
  have hdl := ((F.dhKeyExchange_anonKESecure_iff_cdh_ideal _).mp h).discreteLog
    (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hdl
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hdl

example :
    KeyGuesser.IsPPT schnorrGroups.encDHTranscript schnorrGroups.encDHKey
      (fun _ t => pure (t.aliceShare + t.bobShare)) := by
  open scoped PrimeOrderGroupFamily in
  have hcmp : ComputableInPolyTime
      (fun input : ℕ × schnorrGroups.DHTranscript =>
        schnorrGroups.encDHKey input.2 (input.2.aliceShare + input.2.bobShare))
      (encPair encUnary schnorrGroups.encDHTranscript) encBits := by
    fun_prop
  simpa [KeyGuesser.IsPPT] using hcmp.isPPTOn

/-! ### Attacking the 3-message XOR protocol -/

private def xorKeyGuesser : KeyGuesser KeyExchange.XorTranscript fun _ => List Bool :=
  fun _ t => pure t.xorAll

private theorem isPPT_xorKeyGuesser :
    xorKeyGuesser.IsPPT KeyExchange.encXorTranscript fun _ => encBits := by
  have hrec : ComputableInPolyTime (fun input : ℕ × KeyExchange.XorTranscript =>
      input.2.xorAll) (encPair encUnary KeyExchange.encXorTranscript) encBits := by
    unfold KeyExchange.XorTranscript.xorAll
    fun_prop
  exact hrec.isPPTOn

private theorem anonKEGame_xorKeyGuesser (n : ℕ) :
    KeyExchange.xorKeyExchange.anonKEGame xorKeyGuesser n = PMF.pure true := by
  rw [← KeyExchange.realGame_xorEavesdropper n]
  simp only [anonKEGame, KeyExchange.realGame, Game.withSetup, KeyExchange.realView, xorKeyGuesser,
    KeyExchange.xorEavesdropper, ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  exact congrArg _ (funext fun outcome => congrArg PMF.pure (decide_eq_decide.mpr eq_comm))

example : ¬ KeyExchange.xorKeyExchange.AnonKESecure KeyExchange.encXorTranscript
    fun _ => encBits := by
  intro h
  have hneg := h xorKeyGuesser isPPT_xorKeyGuesser
  simp only [Game.succProbability, anonKEGame_xorKeyGuesser, PMF.pure_apply, ite_true,
    ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### Satisfying instance: half-leaking protocol -/

private noncomputable def halfLeakKE :
    KeyExchange (List Bool) fun _ => List Bool × List Bool where
  execute n := do
    let leftHalf ← BitString.uniformList n
    let rightHalf ← BitString.uniformList n
    return ⟨leftHalf, (leftHalf, rightHalf), (leftHalf, rightHalf)⟩

private theorem halfLeakKE_anonKESecure :
    halfLeakKE.AnonKESecure encBits fun _ => encPair encBits encBits := by
  intro A _
  refine negligible_of_le negligible_one_div_two_pow fun n => ?_
  have hle : halfLeakKE.anonKEGame A n true ≤ (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ENNReal) := by
    simp only [KeyExchange.anonKEGame, Game.withSetup, halfLeakKE,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_bind, PMF.pure_bind]
    rw [PMF.bind_apply]
    calc
      ∑' x : List Bool, (BitString.uniformList n x) *
          ((BitString.uniformList n).bind fun y =>
            (ProbComp.eval (A n x)).bind fun g => PMF.pure (decide (g = (x, y)))) true
          ≤ ∑' x : List Bool,
              (BitString.uniformList n x) * (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ENNReal) := by
            refine tsum_le_tsum fun x => mul_le_mul_of_nonneg_left ?_ zero_le
            rw [PMF.bind_comm, PMF.bind_apply]
            calc
              ∑' g : List Bool × List Bool, ProbComp.eval (A n x) g *
                  ((BitString.uniformList n).bind fun y => PMF.pure (decide (g = (x, y)))) true
                  ≤ ∑' g : List Bool × List Bool,
                      ProbComp.eval (A n x) g * (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ENNReal) := by
                    refine tsum_le_tsum fun g => mul_le_mul_of_nonneg_left ?_ zero_le
                    by_cases hg : g.1 = x
                    · have hsub :
                          ((BitString.uniformList n).bind fun y =>
                            PMF.pure (decide (g = (x, y)))) true =
                          (BitString.uniformList n).bind (fun y => PMF.pure (decide (g.2 = y)))
                            true := by
                        congr 1; ext y; simp [Prod.ext_iff, hg]
                      rw [hsub, PMF.bind_pure_decide_eq_apply_true]
                      simpa using BitString.uniformList_apply_le n g.2
                    · have hzero :
                          ((BitString.uniformList n).bind fun y =>
                            PMF.pure (decide (g = (x, y)))) true = 0 := by
                        simp [Prod.ext_iff, hg]
                      simp [hzero]
              _ = (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ENNReal) := by
                    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ = (((1 : ℝ≥0) / 2 ^ n : ℝ≥0) : ENNReal) := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simpa only [Game.succProbability, ENNReal.toNNReal_coe] using
    ENNReal.toNNReal_mono ENNReal.coe_ne_top hle

example :
    halfLeakKE.Correct ∧
      halfLeakKE.AnonKESecure encBits fun _ => encPair encBits encBits :=
  ⟨fun n outcome h => by
    simp only [halfLeakKE, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl,
   halfLeakKE_anonKESecure⟩

/-! ### Necessity of `Correct` for Alice-key / Bob-key equivalence -/

private noncomputable def splitKE : KeyExchange Unit fun _ => Bool where
  execute _ := PMF.pure ⟨(), true, false⟩

example : ¬ splitKE.Correct := fun h => by
  have := h 0 ⟨(), true, false⟩ (by simp [splitKE])
  simp at this

example (n : ℕ) :
    splitKE.anonKEGame (fun _ _ => pure false) n = PMF.pure false ∧
    (Game.withSetup (splitKE.execute n) fun outcome => do
        let guess ← (pure false : ProbComp Bool)
        return decide (guess = outcome.bobKey)) = PMF.pure true := by
  constructor <;> simp [splitKE, anonKEGame, Game.withSetup]

end CslibFrontierTests.Crypto.KeyExchangeKeyGuessing
