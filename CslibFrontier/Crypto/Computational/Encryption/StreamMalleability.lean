/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
public import CslibFrontier.Crypto.Computational.Encryption.IVStream.Malleability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT

/-!
# The one-block PRF cipher is not CCA-secure

Boneh and Shoup open Section 9.2.1 ([BonehShoup2023], printed pp. 360–361) with an attack on
randomized counter mode: from an encryption `c` of `u ‖ m` an attacker builds `ĉ`, "the same as
`c` except that `ĉ[1] := c[1] ⊕ u ⊕ v`", which decrypts to `v ‖ m`, so that "by querying for the
decryption of `ĉ`, Mel was able to deduce the decryption of `c`". They conclude: "We proved that
both encryption modes are CPA secure, and yet we just showed how to break them."

This file proves that conclusion in the chosen-ciphertext game for the one-block cipher
`prfCipher`, which `PseudorandomFunction.indcpa_prfCipher` proves CPA-secure for a pseudorandom
family. `prfCipher` encrypts
as the stream envelope `ivStreamEncrypt` with one block, so `ivStreamXorBody` turns an encryption
of `msg` into one of `msg ⊕ delta` (`ivStreamXorBody_mem_support_ivStreamEncrypt`). The adversary
`prfCipherCCAAdversary` asks for the challenge encryption of `0ⁿ` or `1ⁿ`, flips every bit after
the initial value and asks the decryption oracle for the result, which is a different ciphertext
when `1 ≤ n`; it decrypts to the other message, and the adversary wins with probability `1`
(`eval_ccaOneTimeGame_prfCipher`).

Differences from the book: the attack is carried out in a game only against the one-block cipher
`prfCipher`, since the library has no chosen-ciphertext game for multi-block modes; for counter
mode and output feedback mode `ivStreamDecrypt_ivStreamXorBody` says what the modified ciphertext
decrypts to. The randomized CBC half of Section 9.2.1 is not covered. The attack needs `1 ≤ n`:
at `n = 0` the modified ciphertext is the challenge itself, which the oracle refuses to decrypt.

## Main definitions

* `Cslib.Crypto.prfCipherCCAAdversary`: the two-query chosen-ciphertext adversary.

## Main results

* `Cslib.Crypto.isOraclePPT_prfCipherCCAAdversary`: the adversary is efficient.
* `Cslib.Crypto.eval_ccaOneTimeGame_prfCipher`: it guesses the challenge bit with probability `1`
  for every `1 ≤ n`.
* `Cslib.Crypto.not_oneTimeINDCCA_prfCipher`, `Cslib.Crypto.not_indcca_prfCipher`: `prfCipher`
  is neither one-time nor many-time CCA-secure, for every family.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 9.2.1 (printed pp. 360–361).
-/

public section

namespace Cslib.Crypto

open Probability OracleComp Turing.MultiTapeTM
open scoped NNReal

/-- XORing a mask into an encryption under `prfCipher` gives a ciphertext that decrypts to the
masked message, and that differs from the original whenever the masked message does. -/
private theorem prfCipher_decrypt_ivStreamXorBody (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k msg delta ct : List Bool}
    (hk : k ∈ (ProbComp.eval ((prfCipher family hpoly hlen).keyGen n)).support)
    (hmsg : msg.length = n) (hdelta : delta.length = n)
    (hct : ct ∈ (ProbComp.eval ((prfCipher family hpoly hlen).encrypt n k msg)).support) :
    (prfCipher family hpoly hlen).decrypt n k (ivStreamXorBody n delta ct) =
        some (List.zipWith xor msg delta) ∧
      (List.zipWith xor msg delta ≠ msg → ivStreamXorBody n delta ct ≠ ct) := by
  have hdec : (prfCipher family hpoly hlen).decrypt n k (ivStreamXorBody n delta ct) =
      some (List.zipWith xor msg delta) :=
    (prfCipher family hpoly hlen).decrypt_encrypt n k hk _ (by simp [hmsg, hdelta]) _
      (ivStreamXorBody_mem_support_ivStreamEncrypt (keystream := fun _ k iv _ => family k iv)
        (hmsg.trans hdelta.symm).le hct)
  refine ⟨hdec, fun hne heq => hne ?_⟩
  rw [heq, (prfCipher family hpoly hlen).decrypt_encrypt n k hk msg hmsg ct hct] at hdec
  exact (Option.some.inj hdec).symm

/-- Two-query chosen-ciphertext adversary against `prfCipher` ([BonehShoup2023], Section 9.2.1):
ask for the challenge encryption of `(0ⁿ, 1ⁿ)`, XOR `1ⁿ` into the ciphertext after its `n`-bit
initial value, ask the decryption oracle for the result, and output `true` iff it decrypts
to `0ⁿ`. -/
@[expose]
def prfCipherCCAAdversary : CCAAdversary :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let ct ← List.take (2 * n) <$>
      ProbOracleComp.query (false, encPair encBits encBits (m0, m1))
    let dec ← List.take (n + 1) <$> ProbOracleComp.query (true, ivStreamXorBody n m1 ct)
    return (dec == encSilentOption encBits (some m0))

/-- `prfCipherCCAAdversary` is an efficient oracle adversary. -/
theorem isOraclePPT_prfCipherCCAAdversary : IsOraclePPT encBool prfCipherCCAAdversary := by
  ppt [prfCipherCCAAdversary]

/-- `prfCipherCCAAdversary` guesses the challenge bit of the one-time chosen-ciphertext game
against `prfCipher` with probability `1`, for every family and every `1 ≤ n`
([BonehShoup2023], Section 9.2.1). -/
theorem eval_ccaOneTimeGame_prfCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (bit : Bool) {n : ℕ} (hn : 1 ≤ n) :
    ProbComp.eval ((prfCipher family hpoly hlen).ccaOneTimeGame prfCipherCCAAdversary bit n) =
      PMF.pure bit := by
  have hbit : (if bit then List.replicate n true else List.replicate n false) =
      List.replicate n bit := by
    cases bit <;> rfl
  simp only [SymmetricCipher.ccaOneTimeGame, prfCipherCCAAdversary,
    SymmetricCipher.oneTimeCCAOracle, unframe_encPair_encBits, dropFrame_encPair_encBits, hbit,
    List.isEmpty_nil, List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true,
    ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain ⟨hdec, hne⟩ := prfCipher_decrypt_ivStreamXorBody family hpoly hlen hk
    List.length_replicate (List.length_replicate (a := true)) hct
  have hflip : List.zipWith xor (List.replicate n bit) (List.replicate n true) =
      List.replicate n !bit := by
    simp
  rw [hflip] at hdec hne
  have hnc : [ct].contains (ivStreamXorBody n (List.replicate n true) ct) = false := by
    simpa using hne (by cases bit <;> simp [List.replicate_inj] <;> omega)
  rw [List.take_of_length_le
    (prfCipher_ciphertext_length family hpoly hlen n k hk _ List.length_replicate ct hct).le]
  simp only [hnc, Bool.false_eq_true, ↓reduceIte, hdec, ProbComp.eval_pure, PMF.pure_bind]
  rw [List.take_of_length_le (by simp)]
  cases bit with
  | true => simp
  | false => simp [beq_eq_false_iff_ne.mpr (Nat.one_le_iff_ne_zero.mp hn)]

/-- The one-block PRF cipher `prfCipher` is not one-time CCA-secure, for any family
([BonehShoup2023], Section 9.2.1), although it is CPA-secure for a pseudorandom family
(`PseudorandomFunction.indcpa_prfCipher`). -/
theorem not_oneTimeINDCCA_prfCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    ¬ (prfCipher family hpoly hlen).OneTimeINDCCA := by
  intro hcca
  have hcomp := (hcca prfCipherCCAAdversary isOraclePPT_prfCipherCCAAdversary).shift 1
  refine not_negligible_const (one_ne_zero (α := ℝ≥0)) (hcomp.congr fun n => ?_)
  dsimp only
  rw [eval_ccaOneTimeGame_prfCipher family hpoly hlen false (Nat.le_add_left 1 n),
    eval_ccaOneTimeGame_prfCipher family hpoly hlen true (Nat.le_add_left 1 n)]
  simp [Game.advantage, Game.succProbability]

/-- The one-block PRF cipher `prfCipher` is not CCA-secure, for any family ([BonehShoup2023],
Section 9.2.1). -/
theorem not_indcca_prfCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    ¬ (prfCipher family hpoly hlen).INDCCA :=
  fun hcca => not_oneTimeINDCCA_prfCipher family hpoly hlen hcca.oneTimeINDCCA

end Cslib.Crypto
