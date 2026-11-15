/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.OneTimePad
public import CslibFrontier.Crypto.Computational.Encryption.Cipher.Perfect
public import CslibFrontier.Crypto.Game.HiddenBit

/-!
# Clients and Counterexamples for `Cipher.Perfect`

Concrete `module`-boundary tests and hypothesis counterexamples for
`CslibFrontier.Crypto.Computational.Encryption.Cipher.Perfect`:

1. Equal-length admissibility is required for `variableLengthOTPCipher`: allowing unequal lengths
   yields `Experiment.advantage = 1`.
2. Matching the key sampler's law (`hgen`) is required: running `otpCipher 1` with `pure 0` yields
   `Experiment.advantage = 1`.
3. Matching the encryption law (`henc`) is required: pairing the identity cipher with `otp 1`
   yields `Experiment.advantage = 1`.
4. Positive concrete checks for `otpCipher 4`, `variableLengthOTPCipher 4`, the `L = 0` boundary,
   a `CiphertextIndist` client using `advantage_oneTimeExperiment_eq_zero` with
   `ciphertextDist_eq_encScheme`, and `Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit`
   (Boneh–Shoup Theorem 2.10).
-/

public section

namespace CslibFrontierTests.Crypto.CipherPerfect

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Cipher
open Cslib.Crypto.Protocols.PerfectSecrecy
open scoped NNReal

/-- Probe 1: dropping equal-length admissibility in `variableLengthOTPCipher 1` yields
`Experiment.advantage = 1` by distinguishing `[]` from `[false]` via ciphertext length. -/
def lenDistinguisher :
    TwoStage Unit (MessagePair {w : List Bool // w.length ≤ 1})
      {w : List Bool // w.length ≤ 1} Bool Unit where
  choose _ := pure (⟨⟨[], by decide⟩, ⟨[false], by decide⟩⟩, ())
  guess _ ct := pure (decide (ct.1.length = 0))

theorem lenDistinguisher_advantage :
    Experiment.advantage
        ((variableLengthOTPCipher 1).oneTimeExperiment (ProbComp.uniform (BitString 1))
          (fun _ _ => true) lenDistinguisher false)
        ((variableLengthOTPCipher 1).oneTimeExperiment (ProbComp.uniform (BitString 1))
          (fun _ _ => true) lenDistinguisher true) = 1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval ((variableLengthOTPCipher 1).oneTimeExperiment (ProbComp.uniform (BitString 1))
        (fun _ _ => true) lenDistinguisher b) = PMF.pure (!b) := by
    intro b
    cases b <;>
      simp only [Cipher.oneTimeExperiment, variableLengthOTPCipher, ofPure, lenDistinguisher,
        lrExperiment, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
        PMF.pure_bind, MessagePair.select_false, MessagePair.select_true, ↓reduceIte,
        length_varXor, List.length_nil, List.length_singleton, decide_true,
        Bool.not_false, Bool.not_true, PMF.bind_const]
    exact congrArg PMF.pure (by decide)
  rw [Experiment.advantage, heval false, heval true]
  simp [Game.advantage, Game.succProbability]

/-- Probe 2: running `otpCipher 1` with a non-uniform key sampler `pure 0` breaks semantic
security (`Experiment.advantage = 1`). -/
def bitVecZeroDistinguisher :
    TwoStage Unit (MessagePair (BitVec 1)) (BitVec 1) Bool Unit where
  choose _ := pure (⟨0, 1⟩, ())
  guess _ ct := pure (decide (ct = 0))

theorem bitVecZeroDistinguisher_advantage :
    Experiment.advantage
        ((otpCipher 1).oneTimeExperiment (pure 0) (fun _ _ => true)
          bitVecZeroDistinguisher false)
        ((otpCipher 1).oneTimeExperiment (pure 0) (fun _ _ => true)
          bitVecZeroDistinguisher true) = 1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval ((otpCipher 1).oneTimeExperiment (pure 0) (fun _ _ => true)
        bitVecZeroDistinguisher b) = PMF.pure (!b) := by
    intro b
    cases b <;>
      simp [Cipher.oneTimeExperiment, otpCipher, ofPure, bitVecZeroDistinguisher, lrExperiment]
  rw [Experiment.advantage, heval false, heval true]
  simp [Game.advantage, Game.succProbability]

/-- Probe 3: pairing the identity cipher with `otp 1` (which is `PerfectlySecret`) breaks
`advantage = 0` when `henc` fails, giving `Experiment.advantage = 1`. -/
def idCipherBool : Cipher Bool Bool Bool :=
  ofPure (fun _ m => m) (fun _ c => c)

def boolDistinguisher :
    TwoStage Unit (MessagePair Bool) Bool Bool Unit where
  choose _ := pure (⟨false, true⟩, ())
  guess _ ct := pure (!ct)

theorem idCipherBool_advantage :
    Experiment.advantage
        (idCipherBool.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true)
          boolDistinguisher false)
        (idCipherBool.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true)
          boolDistinguisher true) = 1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval (idCipherBool.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true)
        boolDistinguisher b) = PMF.pure (!b) := by
    intro b
    cases b <;>
      simp only [Cipher.oneTimeExperiment, idCipherBool, ofPure, boolDistinguisher, lrExperiment,
        ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind,
        MessagePair.select_false, MessagePair.select_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, PMF.bind_const]
  rw [Experiment.advantage, heval false, heval true]
  simp [Game.advantage, Game.succProbability]

/-- Concrete correctness and semantic security for `otpCipher 4`, and for a client holding
`EncScheme.CiphertextIndist` directly via `advantage_oneTimeExperiment_eq_zero` and
`ciphertextDist_eq_encScheme`. -/
example {σ : Type} (A : TwoStage Unit (MessagePair (BitVec 4)) (BitVec 4) Bool σ) :
    (otpCipher 4).Correct ∧
    Experiment.advantage
        ((otpCipher 4).oneTimeExperiment (ProbComp.uniform (BitVec 4)) (fun _ _ => true) A false)
        ((otpCipher 4).oneTimeExperiment (ProbComp.uniform (BitVec 4)) (fun _ _ => true) A true) =
      0 :=
  ⟨otpCipher_correct 4, advantage_oneTimeExperiment_otpCipher 4 _ A⟩

example {σ : Type} (S : EncScheme (BitVec 4) (BitVec 4) (BitVec 4)) (hS : S.CiphertextIndist)
    (E : Cipher (BitVec 4) (BitVec 4) (BitVec 4)) (sampleKey : ProbComp (BitVec 4))
    (hgen : S.gen = ProbComp.eval sampleKey)
    (henc : ∀ k m, ProbComp.eval (E.encrypt k m) = S.enc k m)
    (A : TwoStage Unit (MessagePair (BitVec 4)) (BitVec 4) Bool σ) :
    Experiment.advantage (E.oneTimeExperiment sampleKey (fun _ _ => true) A false)
      (E.oneTimeExperiment sampleKey (fun _ _ => true) A true) = 0 := by
  refine advantage_oneTimeExperiment_eq_zero E sampleKey _ (fun m₀ m₁ _ => ?_) A
  rw [ciphertextDist_eq_encScheme E sampleKey S hgen henc m₀,
    ciphertextDist_eq_encScheme E sampleKey S hgen henc m₁]
  exact hS m₀ m₁

/-- Concrete correctness and semantic security for `variableLengthOTPCipher` at `L = 4` and at
the `L = 0` boundary. -/
example {σ : Type}
    (A : TwoStage Unit (MessagePair {w : List Bool // w.length ≤ 4})
      {w : List Bool // w.length ≤ 4} Bool σ) :
    (variableLengthOTPCipher 4).Correct ∧
    Experiment.advantage
        ((variableLengthOTPCipher 4).oneTimeExperiment (ProbComp.uniform (BitString 4))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A false)
        ((variableLengthOTPCipher 4).oneTimeExperiment (ProbComp.uniform (BitString 4))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A true) = 0 :=
  ⟨variableLengthOTPCipher_correct 4, advantage_oneTimeExperiment_variableLengthOTPCipher 4 A⟩

example {σ : Type}
    (A : TwoStage Unit (MessagePair {w : List Bool // w.length ≤ 0})
      {w : List Bool // w.length ≤ 0} Bool σ) :
    (variableLengthOTPCipher 0).Correct ∧
    Experiment.advantage
        ((variableLengthOTPCipher 0).oneTimeExperiment (ProbComp.uniform (BitString 0))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A false)
        ((variableLengthOTPCipher 0).oneTimeExperiment (ProbComp.uniform (BitString 0))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A true) = 0 :=
  ⟨variableLengthOTPCipher_correct 0, advantage_oneTimeExperiment_variableLengthOTPCipher 0 A⟩

/-- Theorem 2.10 instance for `Cipher.oneTimeExperiment` via
`Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit`: for `idCipherBool` and
`boolDistinguisher`, `2 * guessingAdvantage = 1`. -/
example :
    2 * Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit
      (idCipherBool.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true)
        boolDistinguisher))) = 1 := by
  rw [← Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit, idCipherBool_advantage]

/-- Theorem 2.10 instance for `variableLengthOTPCipher 2`: every adversary has bit-guessing
advantage `0`. -/
example {σ : Type}
    (A : TwoStage Unit (MessagePair {w : List Bool // w.length ≤ 2})
      {w : List Bool // w.length ≤ 2} Bool σ) :
    Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit
      ((variableLengthOTPCipher 2).oneTimeExperiment (ProbComp.uniform (BitString 2))
        (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A))) = 0 := by
  have h := Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit
    ((variableLengthOTPCipher 2).oneTimeExperiment (ProbComp.uniform (BitString 2))
      (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A)
  rw [advantage_oneTimeExperiment_variableLengthOTPCipher] at h
  have hcoe : (2 : ℝ≥0) * _ = 0 := h.symm
  rcases mul_eq_zero.mp hcoe with h2 | hg
  · norm_num at h2
  · exact hg

end CslibFrontierTests.Crypto.CipherPerfect

end
