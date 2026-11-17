/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
public import CslibFrontier.Crypto.Computational.Encryption.IVStream.Malleability
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT

/-!
# A stream cipher with a linear checksum has no ciphertext integrity

Boneh and Shoup's Attack 3 on WEP in Section 9.10 ([BonehShoup2023], printed pp. 390–391)
encrypts a message together with its CRC checksum by a stream cipher,
`c = (m, CRC(m)) ⊕ RC4(IV ‖ k)`, and uses that "there is a public function `L` such that for any
`m` and `Δ` … `CRC(m ⊕ Δ) = CRC(m) ⊕ L(Δ)`". An attacker who XORs `(Δ, L(Δ))` into `c` gets a
ciphertext that "decrypts without errors to `m ⊕ Δ`", so "given the encryption of `m`, an
attacker can create a valid encryption of `m ⊕ Δ` for any `Δ` of his choice."

`prfChecksumCipher` encrypts `msg ++ checksum msg` under the one-block PRF cipher `prfCipher` at
parameter `n + csLen n`, and decryption rejects unless the checksum matches. When `checksum` is
linear with a public `L`, XORing `delta ++ L delta` into the ciphertext after its initial value
gives an encryption of `msg ⊕ delta`, for every `delta` of length `n`
(`ivStreamXorBody_mem_support_encrypt_prfChecksumCipher`). The adversary `prfChecksumCIAdversary`
asks for an encryption of `0ⁿ` and outputs it modified by `1ⁿ ++ L 1ⁿ`, which decrypts to `1ⁿ`;
it wins the one-time ciphertext-integrity game with probability `1` for every `1 ≤ n`
(`eval_ciOneTimeGame_prfChecksumCipher`).

Differences from the book: `prfCipher` stands for RC4 and any checksum with the stated linearity
for CRC-32; WEP itself is not modelled, and nothing is proved about the chosen-plaintext security
of `prfChecksumCipher`. The book says that WEP, in a sense, uses MAC-then-encrypt with a CRC
instead of a MAC; `prfChecksumCipher` is not an instance of `macThenEncrypt`, which frames its
plaintext with `encPair`. The attack needs `1 ≤ n`: at `n = 0` the adversary's output can be the
ciphertext it was given.

## Main definitions

* `Cslib.Crypto.prfChecksumCipher`: the PRF stream cipher over message ‖ checksum.
* `Cslib.Crypto.prfChecksumCIAdversary`: the one-query ciphertext-integrity adversary.

## Main results

* `Cslib.Crypto.ivStreamXorBody_mem_support_encrypt_prfChecksumCipher`: from an encryption of
  `msg`, a valid encryption of `msg ⊕ delta` for any `delta`.
* `Cslib.Crypto.isOraclePPT_prfChecksumCIAdversary`: the adversary is efficient.
* `Cslib.Crypto.eval_ciOneTimeGame_prfChecksumCipher`: it wins with probability `1`.
* `Cslib.Crypto.not_oneTimeCiphertextIntegrity_prfChecksumCipher`,
  `Cslib.Crypto.not_ciphertextIntegrity_prfChecksumCipher`: no ciphertext integrity.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 9.10, Attack 3 (printed pp. 390–391).
-/

public section

namespace Cslib.Crypto

open Probability OracleComp Turing.MultiTapeTM
open scoped NNReal

/-- The PRF stream cipher over message ‖ checksum, modelling WEP's
`c = (m, CRC(m)) ⊕ RC4(IV ‖ k)` ([BonehShoup2023], Section 9.10, Attack 3): encrypt
`msg ++ checksum msg` with `prfCipher` at parameter `n + csLen n`, where `csLen` gives the
checksum length, and on decryption return the first `n` bits only if the rest is their
checksum. -/
@[expose]
noncomputable def prfChecksumCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (checksum : List Bool → List Bool)
    (hcsPoly : ComputableInPolyTime checksum encBits encBits)
    (csLen : ℕ → ℕ)
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hcsLen : ∀ m, (checksum m).length = csLen m.length) : SymmetricCipher where
  keyGen n := (prfCipher family hpoly hlen).keyGen (n + csLen n)
  encrypt n k msg := (prfCipher family hpoly hlen).encrypt (n + csLen n) k (msg ++ checksum msg)
  decrypt n k ct :=
    ((prfCipher family hpoly hlen).decrypt (n + csLen n) k ct).elim none fun p =>
      if p.drop n == checksum (p.take n) then some (p.take n) else none
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by
    refine ComputableInPolyTime.optionElimWithInput
      (encB := encBits) (encO := encSilentOption encBits)
      (value := fun x : ℕ × List Bool × List Bool =>
        (prfCipher family hpoly hlen).decrypt (x.1 + csLen x.1) x.2.1 x.2.2)
      (body := fun (x : ℕ × List Bool × List Bool) p => if p.drop x.1 == checksum (p.take x.1)
        then some (p.take x.1) else none) ?_ (ComputableInPolyTime.const none) ?_
    · have hargs : ComputableInPolyTime
          (fun x : ℕ × List Bool × List Bool => (x.1 + csLen x.1, x.2.1, x.2.2))
          (encPair encUnary (encPair encBits encBits))
          (encPair encUnary (encPair encBits encBits)) := by fun_prop
      exact (prfCipher family hpoly hlen).decrypt_polyTime.comp hargs
    · polytime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    have hmlen : (msg ++ checksum msg).length = n + csLen n := by
      rw [List.length_append, hmsg, hcsLen, hmsg]
    rw [(prfCipher family hpoly hlen).decrypt_encrypt (n + csLen n) k hk
      (msg ++ checksum msg) hmlen ct hct, Option.elim_some, ← hmsg, List.take_left,
      List.drop_left]
    simp

/-- **Malleability of a stream cipher with a linear checksum** ([BonehShoup2023], Section 9.10,
Attack 3): if `checksum (m ⊕ d) = checksum m ⊕ L d` whenever `m` and `d` have the same length,
then XORing `delta ++ L delta` into an encryption of an `n`-bit `msg` after its initial value
gives an encryption of `msg ⊕ delta`, for every `n`-bit `delta`. -/
theorem ivStreamXorBody_mem_support_encrypt_prfChecksumCipher
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (checksum : List Bool → List Bool)
    (hcsPoly : ComputableInPolyTime checksum encBits encBits)
    (csLen : ℕ → ℕ)
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hcsLen : ∀ m, (checksum m).length = csLen m.length)
    (L : List Bool → List Bool)
    (hlinear : ∀ m d, m.length = d.length →
      checksum (List.zipWith xor m d) = List.zipWith xor (checksum m) (L d))
    {n : ℕ} {k msg delta ct : List Bool} (hmsg : msg.length = n) (hdelta : delta.length = n)
    (hct : ct ∈ (ProbComp.eval ((prfChecksumCipher family hpoly hlen checksum hcsPoly csLen
      hcsLenPoly hcsLen).encrypt n k msg)).support) :
    ivStreamXorBody (n + csLen n) (delta ++ L delta) ct ∈
      (ProbComp.eval ((prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly
        hcsLen).encrypt n k (List.zipWith xor msg delta))).support := by
  have hmd : msg.length = delta.length := hmsg.trans hdelta.symm
  have hL : csLen n ≤ (L delta).length := by
    have h := congrArg List.length (hlinear msg delta hmd)
    simp only [hcsLen, List.length_zipWith, hmsg, hdelta, min_self] at h
    omega
  have h := ivStreamXorBody_mem_support_ivStreamEncrypt
    (keystream := fun _ k iv _ => family k iv) (n := n + csLen n) (k := k)
    (msg := msg ++ checksum msg) (delta := delta ++ L delta) (ct := ct)
    (by simp only [List.length_append, hmsg, hdelta, hcsLen]; omega) hct
  rwa [List.zipWith_append hmd, ← hlinear msg delta hmd] at h

/-- One-query ciphertext-integrity adversary against `prfChecksumCipher` ([BonehShoup2023],
Section 9.10, Attack 3): ask for an encryption of `0ⁿ` and output it with `1ⁿ ++ L 1ⁿ` XORed in
after its initial value. -/
@[expose]
def prfChecksumCIAdversary (csLen : ℕ → ℕ) (L : List Bool → List Bool) : CIAdversary :=
  fun n _ => do
    let delta := List.replicate n true
    let ct ← List.take (2 * (n + csLen n)) <$> ProbOracleComp.query ((), List.replicate n false)
    return ivStreamXorBody (n + csLen n) (delta ++ L delta) ct

/-- `prfChecksumCIAdversary` is an efficient oracle adversary when the checksum length and `L`
are computable in polynomial time. -/
theorem isOraclePPT_prfChecksumCIAdversary {csLen : ℕ → ℕ} {L : List Bool → List Bool}
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hLPoly : ComputableInPolyTime L encBits encBits) :
    IsOraclePPT encBits (prfChecksumCIAdversary csLen L) := by
  ppt [prfChecksumCIAdversary]

/-- `prfChecksumCIAdversary` wins the one-time ciphertext-integrity game against
`prfChecksumCipher` with probability `1` for every linear checksum and every `1 ≤ n`
([BonehShoup2023], Section 9.10, Attack 3). -/
theorem eval_ciOneTimeGame_prfChecksumCipher (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (checksum : List Bool → List Bool)
    (hcsPoly : ComputableInPolyTime checksum encBits encBits)
    (csLen : ℕ → ℕ)
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hcsLen : ∀ m, (checksum m).length = csLen m.length)
    (L : List Bool → List Bool)
    (hlinear : ∀ m d, m.length = d.length →
      checksum (List.zipWith xor m d) = List.zipWith xor (checksum m) (L d))
    {n : ℕ} (hn : 1 ≤ n) :
    ProbComp.eval ((prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly
        hcsLen).ciOneTimeGame (prfChecksumCIAdversary csLen L) n) = PMF.pure true := by
  set E := prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly hcsLen
  simp only [SymmetricCipher.ciOneTimeGame, prfChecksumCIAdversary,
    SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  rw [List.take_of_length_le (prfCipher_ciphertext_length family hpoly hlen (n + csLen n) k hk _
    (by simp [hcsLen]) ct hct).le]
  have hmod := ivStreamXorBody_mem_support_encrypt_prfChecksumCipher family hpoly hlen
    checksum hcsPoly csLen hcsLenPoly hcsLen L hlinear List.length_replicate
    (List.length_replicate (a := true)) hct
  have hflip : List.zipWith xor (List.replicate n false) (List.replicate n true) =
      List.replicate n true := by
    simp
  rw [hflip] at hmod
  have hdec := E.decrypt_encrypt n k hk _ List.length_replicate _ hmod
  have hne : ivStreamXorBody (n + csLen n)
      (List.replicate n true ++ L (List.replicate n true)) ct ≠ ct := by
    intro heq
    rw [heq, E.decrypt_encrypt n k hk _ List.length_replicate ct hct] at hdec
    simp only [Option.some.injEq, List.replicate_inj, Bool.false_eq_true, or_false] at hdec
    omega
  simp [hne, hdec]

/-- The PRF stream cipher over message ‖ linear checksum is not one-time ciphertext-integral
([BonehShoup2023], Section 9.10, Attack 3). -/
theorem not_oneTimeCiphertextIntegrity_prfChecksumCipher
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (checksum : List Bool → List Bool)
    (hcsPoly : ComputableInPolyTime checksum encBits encBits)
    (csLen : ℕ → ℕ)
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hcsLen : ∀ m, (checksum m).length = csLen m.length)
    (L : List Bool → List Bool)
    (hLPoly : ComputableInPolyTime L encBits encBits)
    (hlinear : ∀ m d, m.length = d.length →
      checksum (List.zipWith xor m d) = List.zipWith xor (checksum m) (L d)) :
    ¬ (prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly
        hcsLen).OneTimeCiphertextIntegrity := by
  intro hci
  have hcomp := (hci.negligible (prfChecksumCIAdversary csLen L)
    (isOraclePPT_prfChecksumCIAdversary hcsLenPoly hLPoly)).shift 1
  refine not_negligible_const (one_ne_zero (α := ℝ≥0)) (hcomp.congr fun n => ?_)
  rw [eval_ciOneTimeGame_prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly
    hcsLen L hlinear (Nat.le_add_left 1 n)]
  simp [Game.succProbability]

/-- The PRF stream cipher over message ‖ linear checksum has no ciphertext integrity
([BonehShoup2023], Section 9.10, Attack 3). -/
theorem not_ciphertextIntegrity_prfChecksumCipher
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (checksum : List Bool → List Bool)
    (hcsPoly : ComputableInPolyTime checksum encBits encBits)
    (csLen : ℕ → ℕ)
    (hcsLenPoly : ComputableInPolyTime csLen encUnary encUnary)
    (hcsLen : ∀ m, (checksum m).length = csLen m.length)
    (L : List Bool → List Bool)
    (hLPoly : ComputableInPolyTime L encBits encBits)
    (hlinear : ∀ m d, m.length = d.length →
      checksum (List.zipWith xor m d) = List.zipWith xor (checksum m) (L d)) :
    ¬ (prfChecksumCipher family hpoly hlen checksum hcsPoly csLen hcsLenPoly
        hcsLen).CiphertextIntegrity :=
  fun hci => not_oneTimeCiphertextIntegrity_prfChecksumCipher family hpoly hlen checksum hcsPoly
    csLen hcsLenPoly hcsLen L hLPoly hlinear hci.oneTimeCiphertextIntegrity

end Cslib.Crypto
