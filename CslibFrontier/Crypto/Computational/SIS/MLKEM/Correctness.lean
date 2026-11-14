/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE
import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin.Correctness
import CslibFrontier.Languages.Probabilistic.Expect
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Ring

/-!
# ML-KEM K-PKE correctness from the core-noise event

This file turns the source-shaped, message-independent K-PKE noise event into the
`ExplicitCoinPKE.DeltaCorrect` bound used by Fujisaki--Okamoto transforms. It follows
[Almeida et al., §4.2, Figure 3, pp. 10--12][AlmeidaEtAl2024]. For independently sampled
`A, s, e, r, e₁, e₂`, put

* `u = Aᵀ r + e₁`;
* `cᵤ = Decompress_du(Compress_du(u)) - u`; and
* `coreNoise = eᵀ r - sᵀ e₁ + e₂ - sᵀ cᵤ`.

If every coefficient of `coreNoise` has centered magnitude at most `T`, scalar ciphertext
compression contributes at most `roundDiv q (2^(d_v+1))`. Thus the existing deterministic
correctness theorem applies whenever their sum is within a decoding bound `B` satisfying
`4 * B + 2 < q`.

The experiment here samples the current uniform matrix and centered-binomial values. It does not
identify `cᵤ` with compression error of a uniform polynomial: Almeida et al. explicitly describe
that distributional identification as an unproved heuristic. It also does not prove a numerical
decryption-failure probability, an MLWE switch, or the seeded FIPS 203 sampling equivalence.

## Main definitions

* `Cslib.Crypto.MLKEM.coreNoise`: the message-independent K-PKE noise polynomial.
* `Cslib.Crypto.MLKEM.coreNoiseFailureExperiment`: the exact independent-draw bad-event
  experiment.
* `Cslib.Crypto.MLKEM.coreNoiseFailureProbability`: its real-valued probability.

## Main results

* `Cslib.Crypto.MLKEM.coreNoiseFailure_of_decrypt_ne`: honest decryption failure implies the
  core-noise bad event.
* `Cslib.Crypto.MLKEM.deltaCorrect_coreNoiseFailureProbability`: K-PKE is correct up to the exact
  bad-event probability.
* `Cslib.Crypto.MLKEM.deltaCorrect_of_coreNoiseFailureProbability_le`: any real upper bound on
  that probability is a valid `DeltaCorrect` bound.

## References

* [Almeida et al., *Formally Verifying Kyber, Episode V*][AlmeidaEtAl2024], §4.2, Figure 3,
  pp. 10--12.
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203], Algorithms
  13--15.
-/

public section

namespace Cslib.Crypto.MLKEM

open Probability Cslib.Crypto.Protocols

/-- The vector ciphertext compression error
`cᵤ = Decompress_du(Compress_du(Aᵀr + e₁)) - (Aᵀr + e₁)`. -/
@[expose] def vectorCompressionError (P : Params)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (r e₁ : Fin P.k → Fin P.n → ZMod P.q) : Fin P.k → Fin P.n → ZMod P.q :=
  let u := moduleSISMap A.transpose r + e₁
  (fun j => decompressPoly P.q P.du (compressPoly P.q P.du (u j))) - u

/-- The scalar ciphertext compression error `cᵥ`. Unlike `vectorCompressionError`, it may depend
on the message through the uncompressed scalar ciphertext component. -/
@[expose] def scalarCompressionError (P : Params)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q)
    (m : Fin P.n → Bool) : Fin P.n → ZMod P.q :=
  let v := (encryptRaw P (moduleLWEKeyGen A s e) r e₁ e₂ m).2
  decompressPoly P.q P.dv (compressPoly P.q P.dv v) - v

/-- The source-shaped, message-independent K-PKE core noise
`eᵀr - sᵀe₁ + e₂ - sᵀcᵤ`. -/
@[expose] def coreNoise (P : Params) (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) :
    Fin P.n → ZMod P.q :=
  innerPoly e r - innerPoly e₁ s + e₂ - innerPoly (vectorCompressionError P A r e₁) s

/-- The scalar `d_v` compression allowance `⌈q / 2^(d_v+1)⌉`. -/
@[expose] def scalarCompressionAllowance (P : Params) : ℕ :=
  roundDiv P.q (2 ^ (P.dv + 1))

/-- The source core-noise bad event: some coefficient has centered magnitude greater than `T`. -/
@[expose] def coreNoiseFailure (P : Params) (T : ℕ)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) : Prop :=
  ∃ i, T < (coreNoise P A s e r e₁ e₂ i).valMinAbs.natAbs

/-- Full decryption noise is the source core noise plus the scalar ciphertext compression error. -/
theorem decryptionNoise_eq_coreNoise_add_scalarCompressionError (P : Params)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q)
    (m : Fin P.n → Bool) :
    decryptionNoise P A s e r e₁ e₂ m =
      coreNoise P A s e r e₁ e₂ + scalarCompressionError P A s e r e₁ e₂ m := by
  funext i
  simp only [decryptionNoise, coreNoise, vectorCompressionError, scalarCompressionError,
    encryptRaw, moduleLWEKeyGen_fst, compressCiphertext, decompressCiphertext, Pi.add_apply,
    Pi.sub_apply, compressPoly_apply, decompressPoly_apply]
  ring

/-- Scalar ciphertext compression contributes at most `scalarCompressionAllowance P` to every
coefficient, uniformly over the message and all other inputs. -/
theorem scalarCompressionError_le (P : Params) [NeZero P.q]
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q)
    (m : Fin P.n → Bool) (i : Fin P.n) :
    (scalarCompressionError P A s e r e₁ e₂ m i).valMinAbs.natAbs ≤
      scalarCompressionAllowance P := by
  simpa [scalarCompressionError, scalarCompressionAllowance] using
    (natAbs_valMinAbs_decompress_compress_sub_le (q := P.q) P.dv
      ((encryptRaw P (moduleLWEKeyGen A s e) r e₁ e₂ m).2 i))

/-- A decryption failure for an honestly formed key and ciphertext implies the source core-noise
bad event, provided the remaining radius and scalar compression allowance fit inside the
deterministic decoding bound. -/
theorem coreNoiseFailure_of_decrypt_ne (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q)
    (m : Fin P.n → Bool)
    (hfail : decrypt P s (encrypt P (moduleLWEKeyGen A s e) m (r, e₁, e₂)) ≠ m) :
    coreNoiseFailure P T A s e r e₁ e₂ := by
  by_contra hgood
  apply hfail
  apply decrypt_encrypt_eq_of_noise_le P hB A s e r e₁ e₂ m
  intro i
  have hcore : (coreNoise P A s e r e₁ e₂ i).valMinAbs.natAbs ≤ T :=
    Nat.le_of_not_gt fun hi => hgood ⟨i, hi⟩
  have htriangle :
      (decryptionNoise P A s e r e₁ e₂ m i).valMinAbs.natAbs ≤
        (coreNoise P A s e r e₁ e₂ i).valMinAbs.natAbs +
          (scalarCompressionError P A s e r e₁ e₂ m i).valMinAbs.natAbs := by
    rw [congrFun (decryptionNoise_eq_coreNoise_add_scalarCompressionError
      P A s e r e₁ e₂ m) i]
    exact (ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)
  exact htriangle.trans ((Nat.add_le_add hcore
    (scalarCompressionError_le P A s e r e₁ e₂ m i)).trans hTB)

/-- The exact source-shaped experiment: independently sample `A, s, e, r, e₁, e₂` and return
whether the core noise exceeds the remaining radius `T`. -/
noncomputable def coreNoiseFailureExperiment (P : Params) [NeZero P.q] (T : ℕ) : ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
  let s ← sampleVecCBD P.k P.n P.q P.η₁
  let e ← sampleVecCBD P.k P.n P.q P.η₁
  let coins ← sampleCoins P
  return decide (coreNoiseFailure P T A s e coins.1 coins.2.1 coins.2.2)

/-- The real probability of the exact source-shaped core-noise failure experiment. -/
noncomputable def coreNoiseFailureProbability (P : Params) [NeZero P.q] (T : ℕ) : ℝ :=
  Pr[coreNoiseFailureExperiment P T]

/-- The same core-noise probability as an extended-nonnegative iterated expectation, exposing
the independent matrix, key-secret, key-error, and encryption-coin draws. -/
noncomputable def coreNoiseFailureMass (P : Params) [NeZero P.q] (T : ℕ) : ENNReal :=
  (ProbComp.uniform (Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))).expect fun A =>
    (sampleVecCBD P.k P.n P.q P.η₁).expect fun s =>
      (sampleVecCBD P.k P.n P.q P.η₁).expect fun e =>
        (ProbComp.eval (sampleCoins P)).toOuterMeasure
          {coins | coreNoiseFailure P T A s e coins.1 coins.2.1 coins.2.2}

/-- The Boolean experiment has exactly the iterated core-noise failure mass. -/
theorem eval_coreNoiseFailureExperiment_true (P : Params) [NeZero P.q] (T : ℕ) :
    ProbComp.eval (coreNoiseFailureExperiment P T) true = coreNoiseFailureMass P T := by
  classical
  simp [coreNoiseFailureExperiment, coreNoiseFailureMass, ProbComp.expect,
    PMF.toOuterMeasure_eq_tsum_mul_indicator, Set.indicator, coreNoiseFailure]

/-- The real probability notation is the real coercion of the iterated event mass. -/
theorem coreNoiseFailureProbability_eq_toReal_mass (P : Params) [NeZero P.q] (T : ℕ) :
    coreNoiseFailureProbability P T = (coreNoiseFailureMass P T).toReal := by
  rw [coreNoiseFailureProbability, ← eval_coreNoiseFailureExperiment_true]

/-- The core-noise failure probability over fresh encryption coins for fixed key-generation
witnesses `A, s, e`. -/
noncomputable def coreNoiseFailProb (P : Params) [NeZero P.q] (T : ℕ)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e : Fin P.k → Fin P.n → ZMod P.q) : ℝ :=
  ((ProbComp.eval (sampleCoins P)).toOuterMeasure
    {coins | coreNoiseFailure P T A s e coins.1 coins.2.1 coins.2.2}).toReal

/-- For an honestly formed key, every message's actual failure probability is bounded by the
same message-independent core-noise event. -/
theorem msgFailProb_le_coreNoiseFailProb (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e : Fin P.k → Fin P.n → ZMod P.q) (m : Fin P.n → Bool) :
    (toExplicitCoinPKE P).msgFailProb (moduleLWEKeyGen A s e) s m ≤
      coreNoiseFailProb P T A s e := by
  rw [coreNoiseFailProb]
  apply ExplicitCoinPKE.msgFailProb_le_event
  intro coins hfail
  apply coreNoiseFailure_of_decrypt_ne P hTB hB A s e coins.1 coins.2.1 coins.2.2 m
  intro hdecrypt
  apply hfail
  change some (decrypt P s (encrypt P (moduleLWEKeyGen A s e) m coins)) = some m
  rw [hdecrypt]

/-- For an honestly formed key, the worst-message failure probability is bounded by the same
message-independent core-noise event. -/
theorem keyPairMaxFailProb_le_coreNoiseFailProb (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q)
    (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (s e : Fin P.k → Fin P.n → ZMod P.q) :
    (toExplicitCoinPKE P).keyPairMaxFailProb (moduleLWEKeyGen A s e) s ≤
      coreNoiseFailProb P T A s e := by
  apply ExplicitCoinPKE.keyPairMaxFailProb_le_of_msgFailProb_le
  intro m
  exact msgFailProb_le_coreNoiseFailProb P hTB hB A s e m

/-- Expands K-PKE key-generation expectation into the independent source draws `A, s, e`. -/
theorem keyGen_expect (P : Params) [NeZero P.q] (f : PublicKey P × SecretKey P → ENNReal) :
    (keyGen P).expect f =
      (ProbComp.uniform (Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))).expect fun A =>
        (sampleVecCBD P.k P.n P.q P.η₁).expect fun s =>
          (sampleVecCBD P.k P.n P.q P.η₁).expect fun e =>
            f (moduleLWEKeyGen A s e, s) := by
  simp [keyGen]

/-- Averaging the worst-message failure probability over K-PKE key generation is bounded by the
iterated source core-noise failure mass. -/
theorem keyGen_expect_maxFail_le_coreNoiseMass (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q) :
    (keyGen P).expect (fun keys => ENNReal.ofReal
      ((toExplicitCoinPKE P).keyPairMaxFailProb keys.1 keys.2)) ≤ coreNoiseFailureMass P T := by
  rw [keyGen_expect]
  simp only [coreNoiseFailureMass]
  apply ProbComp.expect_mono
  intro A
  apply ProbComp.expect_mono
  intro s
  apply ProbComp.expect_mono
  intro e
  calc
    ENNReal.ofReal ((toExplicitCoinPKE P).keyPairMaxFailProb
        (moduleLWEKeyGen A s e) s) ≤ ENNReal.ofReal (coreNoiseFailProb P T A s e) :=
      ENNReal.ofReal_le_ofReal
        (keyPairMaxFailProb_le_coreNoiseFailProb P hTB hB A s e)
    _ = (ProbComp.eval (sampleCoins P)).toOuterMeasure
        {coins | coreNoiseFailure P T A s e coins.1 coins.2.1 coins.2.2} := by
      rw [coreNoiseFailProb, ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _)]

/-- K-PKE is `δ`-correct for the exact source-shaped core-noise failure probability. The left
side retains the expectation over generated keys and maximum over all messages. -/
theorem deltaCorrect_coreNoiseFailureProbability (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q) :
    (toExplicitCoinPKE P).DeltaCorrect (coreNoiseFailureProbability P T) := by
  rw [coreNoiseFailureProbability_eq_toReal_mass]
  apply ExplicitCoinPKE.deltaCorrect_of_keyGen_expect_le
  · exact keyGen_expect_maxFail_le_coreNoiseMass P hTB hB
  · rw [← eval_coreNoiseFailureExperiment_true]
    exact PMF.apply_ne_top _ _

/-- Any real upper bound on the source-shaped core-noise failure probability is a valid
`DeltaCorrect` bound for K-PKE. -/
theorem deltaCorrect_of_coreNoiseFailureProbability_le (P : Params) [NeZero P.q] {T B : ℕ}
    (hTB : T + scalarCompressionAllowance P ≤ B) (hB : 4 * B + 2 < P.q) {δ : ℝ}
    (hδ : coreNoiseFailureProbability P T ≤ δ) :
    (toExplicitCoinPKE P).DeltaCorrect δ :=
  (deltaCorrect_coreNoiseFailureProbability P hTB hB).mono hδ

end Cslib.Crypto.MLKEM
