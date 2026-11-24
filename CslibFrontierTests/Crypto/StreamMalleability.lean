/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
public import CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform
public import CslibFrontier.Crypto.Computational.Encryption.StreamMalleability
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Probability.BitString
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support

/-!
# Tests for the malleability of stream encryption

Checks of `CslibFrontier/Crypto/Computational/Encryption/IVStream/Malleability.lean` and
`CslibFrontier/Crypto/Computational/Encryption/StreamMalleability.lean` as an ordinary `module`
client: the counter-mode step of Boneh–Shoup Section 9.2.1 as an instance of
`ivStreamDecrypt_ivStreamXorBody`, a mask shorter than the message for which the conclusion of
`ivStreamXorBody_mem_support_ivStreamEncrypt` fails, the advantage-`1` corollary and the
CPA-but-not-CCA separation for `prfCipher`, and `n = 0`, where the CCA attack fails.
-/

public section

namespace CslibFrontierTests.Crypto.StreamMalleability

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-! ### Counter mode: `ĉ[1] := c[1] ⊕ u ⊕ v` -/

/-- The book's counter-mode step is the mask `(u ⊕ v) ‖ 0`: from an encryption of `u ‖ m` under
randomized counter mode (`ctrWordEncrypt family` is `ivStreamEncrypt (ctrWordKeystream family)`)
it gives a ciphertext that decrypts to `v ‖ m`, for `n`-bit `u`, `v` and whole-block `m`. -/
example {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k u v m ct : List Bool}
    (hk : k.length = n) (hu : u.length = n) (hv : v.length = n) (hm : m.length % n = 0)
    (hct : ct ∈ (ProbComp.eval (ivStreamEncrypt (ctrWordKeystream family) n k (u ++ m))).support) :
    ivStreamDecrypt (ctrWordKeystream family) n k
        (ivStreamXorBody n (List.zipWith xor u v ++ List.replicate m.length false) ct) =
      some (v ++ m) := by
  have hmask : List.zipWith xor (u ++ m)
      (List.zipWith xor u v ++ List.replicate m.length false) = v ++ m := by
    rw [List.zipWith_append (by simp [hu, hv]),
      BitString.zipWith_xor_self_left u v (hu.trans hv.symm)]
    congr 1
    exact List.ext_getElem (by simp) fun i _ _ => by simp
  rw [← hmask]
  exact ivStreamDecrypt_ivStreamXorBody (fun iv _ => length_ctrWordKeystream hlen hk iv _)
    (by simp [hu, hm]) (by simp [hu, hv]) hct

/-! ### The mask must be at least as long as the message -/

/-- A keystream whose bits depend on the number of blocks. -/
def blockCountKeystream (_ : ℕ) (_ _ : List Bool) (blocks : ℕ) : List Bool :=
  if blocks = 1 then [true] else List.replicate blocks false

/-- Without `msg.length ≤ delta.length` the conclusion of
`ivStreamXorBody_mem_support_ivStreamEncrypt` fails: for `msg = [false, false]` and the one-bit
mask `[false]`, the modified ciphertext `[false, false]` is not an encryption of `[false]`, whose
encryptions end in `true`. -/
example : ∃ ct ∈ (ProbComp.eval (ivStreamEncrypt blockCountKeystream 1 [] [false, false])).support,
    ivStreamXorBody 1 [false] ct ∉ (ProbComp.eval (ivStreamEncrypt blockCountKeystream 1 []
      (List.zipWith xor [false, false] [false]))).support := by
  simp only [ivStreamEncrypt, ivModeEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    BitString.mem_support_uniformList_iff]
  refine ⟨[false, false, false], ⟨[false], rfl, rfl⟩, ?_⟩
  rintro ⟨iv, -, h⟩
  simp only [ivStreamXorBody, blockCountKeystream] at h
  rcases iv with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at h

/-! ### `prfCipher` -/

/-- A length-preserving family, computable in polynomial time. -/
def xorFamily (key query : List Bool) : List Bool :=
  List.zipWith xor key query

theorem xorFamily_polyTime :
    ComputableInPolyTime (fun pair : List Bool × List Bool => xorFamily pair.1 pair.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.bitsZipWithInput xor (by fun_prop) (by fun_prop)

theorem xorFamily_length (key query : List Bool) (h : query.length = key.length) :
    (xorFamily key query).length = key.length := by
  simp [xorFamily, h]

/-- The adversary's advantage is exactly `1` for every family and every `1 ≤ n`. -/
example (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} (hn : 1 ≤ n) :
    Game.advantage
      (ProbComp.eval ((prfCipher family hpoly hlen).ccaOneTimeGame prfCipherCCAAdversary false n))
      (ProbComp.eval ((prfCipher family hpoly hlen).ccaOneTimeGame prfCipherCCAAdversary true n)) =
      1 := by
  rw [eval_ccaOneTimeGame_prfCipher family hpoly hlen false hn,
    eval_ccaOneTimeGame_prfCipher family hpoly hlen true hn]
  simp [Game.advantage, Game.succProbability]

/-- Boneh–Shoup's conclusion in Section 9.2.1 for the one-block cipher: CPA-secure for a
pseudorandom family, and yet not CCA-secure. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfCipher family hprf.polyTime hprf.length_eq).INDCPA ∧
      ¬ (prfCipher family hprf.polyTime hprf.length_eq).INDCCA :=
  ⟨hprf.indcpa_prfCipher, not_indcca_prfCipher family hprf.polyTime hprf.length_eq⟩

/-- At `n = 0` the modified ciphertext is the challenge ciphertext, which the oracle refuses to
decrypt, so the adversary always outputs `false`. -/
theorem eval_ccaOneTimeGame_prfCipher_zero (bit : Bool) :
    ProbComp.eval ((prfCipher xorFamily xorFamily_polyTime xorFamily_length).ccaOneTimeGame
      prfCipherCCAAdversary bit 0) = PMF.pure false := by
  simp only [SymmetricCipher.ccaOneTimeGame, prfCipherCCAAdversary,
    SymmetricCipher.maulCCAAdversary, SymmetricCipher.oneTimeCCAOracle, unframe_encPair_encBits,
    dropFrame_encPair_encBits,
    List.replicate_zero, ite_self, List.isEmpty_nil, List.length_nil, beq_self_eq_true,
    Bool.and_self, Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  obtain rfl : ct = [] := List.eq_nil_of_length_eq_zero
    (prfCipher_ciphertext_length xorFamily xorFamily_polyTime xorFamily_length 0 k hk _ rfl ct
      hct)
  simp [ivStreamXorBody]

/-- So `1 ≤ n` is needed in `eval_ccaOneTimeGame_prfCipher`: at `n = 0` the advantage is `0`. -/
example : Game.advantage
    (ProbComp.eval ((prfCipher xorFamily xorFamily_polyTime xorFamily_length).ccaOneTimeGame
      prfCipherCCAAdversary false 0))
    (ProbComp.eval ((prfCipher xorFamily xorFamily_polyTime xorFamily_length).ccaOneTimeGame
      prfCipherCCAAdversary true 0)) = 0 := by
  rw [eval_ccaOneTimeGame_prfCipher_zero false, eval_ccaOneTimeGame_prfCipher_zero true]
  simp [Game.advantage]

end CslibFrontierTests.Crypto.StreamMalleability
