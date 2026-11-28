/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Finite
public import CslibFrontier.Crypto.Computational.Encryption.LinearChecksum
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Tests for the stream cipher with a linear checksum

Checks of `CslibFrontier/Crypto/Computational/Encryption/LinearChecksum.lean` as an ordinary
`module` client: a one-bit parity checksum, which is linear with `L` the parity itself, makes
`prfChecksumCipher` lose ciphertext integrity; with the constant checksum `[false]`, which is
linear for the constant-zero `L` but not for the adversary's `L = parity`, the same adversary
loses; and at `n = 0` it loses too, so `1 ≤ n` is needed.
-/

public section

namespace CslibFrontierTests.Crypto.LinearChecksum

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

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

/-- The one-bit parity checksum. -/
def parity (m : List Bool) : List Bool :=
  [m.foldl xor false]

theorem parity_polyTime : ComputableInPolyTime parity encBits encBits := by
  have hfold : ComputableInPolyTime (fun m : List Bool => m.foldl xor false) encBits encBool :=
    ComputableInPolyTime.bitsFoldlWithInput xor
      (ComputableInPolyTime.id' (encIn := encBits)) (ComputableInPolyTime.const false)
  have hsingleton : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
    ComputableInPolyTime.of_finite (fun b => [b])
  exact hsingleton.comp hfold

/-- Parity is linear, with `L` the parity itself. -/
theorem parity_linear (m d : List Bool) (h : m.length = d.length) :
    parity (List.zipWith xor m d) = List.zipWith xor (parity m) (parity d) := by
  have hsum := (List.sum_add_sum_eq_sum_zipWith_of_length_eq m d h).symm
  simp only [List.sum_eq_foldl, Bool.add_eq_xor] at hsum
  exact congrArg (fun b => [b]) hsum

/-- With the parity checksum, `prfChecksumCipher` has no ciphertext integrity. -/
example : ¬ (prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length parity
    parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl)).CiphertextIntegrity :=
  not_ciphertextIntegrity_prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length
    parity parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl) parity parity_polyTime
    parity_linear

/-- The book's sentence for the parity instance: from an encryption of `[false, true]`, an
encryption of `[true, true]`, by the mask `[true, false] ++ parity [true, false]`. -/
example {k ct : List Bool}
    (hct : ct ∈ (ProbComp.eval ((prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length
      parity parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl)).encrypt 2 k
        [false, true])).support) :
    ivStreamXorBody 3 ([true, false] ++ parity [true, false]) ct ∈
      (ProbComp.eval ((prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length
        parity parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl)).encrypt 2 k
          [true, true])).support := by
  simpa using ivStreamXorBody_mem_support_encrypt_prfChecksumCipher xorFamily
    xorFamily_polyTime xorFamily_length parity parity_polyTime (fun _ => 1) (by fun_prop)
    (fun _ => rfl) parity parity_linear (msg := [false, true]) (delta := [true, false]) rfl rfl
    hct

/-- The constant checksum `[false]`. It is linear for the constant-zero `L`, but not for
`L = parity`. -/
def constChecksum (_ : List Bool) : List Bool := [false]

/-- Without the linearity relation for the adversary's `L` the attack fails: with the constant
checksum and `L = parity`, which do not satisfy it, the modified ciphertext carries checksum
`[true]` and is rejected, so the adversary never wins at `n = 1`. -/
example : ProbComp.eval ((prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length
      constChecksum (ComputableInPolyTime.const [false]) (fun _ => 1) (by fun_prop)
      (fun _ => rfl)).ciOneTimeGame (prfChecksumCIAdversary (fun _ => 1) parity) 1) =
    PMF.pure false := by
  set E := prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length constChecksum
    (ComputableInPolyTime.const [false]) (fun _ => 1) (by fun_prop) (fun _ => rfl)
  simp only [SymmetricCipher.ciOneTimeGame, prfChecksumCIAdversary, SymmetricCipher.maulCIAdversary,
    SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  let P := prfCipher xorFamily xorFamily_polyTime xorFamily_length
  have hk' : k ∈ (ProbComp.eval (P.keyGen 2)).support := hk
  have hct' : ct ∈ (ProbComp.eval (P.encrypt 2 k [false, false])).support := hct
  have hctLen : ct.length = 2 * 2 :=
    prfCipher_ciphertext_length xorFamily xorFamily_polyTime xorFamily_length 2 k hk' _ rfl
      ct hct'
  rw [List.take_of_length_le hctLen.le]
  have hdec : P.decrypt 2 k (ivStreamXorBody 2 [true, true] ct) = some [true, true] :=
    P.decrypt_encrypt 2 k hk' _ rfl _
      (ivStreamXorBody_mem_support_ivStreamEncrypt (keystream := fun _ k iv _ =>
        xorFamily k iv) (msg := [false, false]) (delta := [true, true]) le_rfl hct')
  have hdecE : E.decrypt 1 k (ivStreamXorBody 2 [true, true] ct) = none := by
    change (P.decrypt 2 k _).elim none _ = none
    rw [hdec]
    decide
  change (PMF.pure (!_ && (E.decrypt 1 k (ivStreamXorBody 2 [true, true] ct)).isSome)) = _
  rw [hdecE]
  simp

/-- At `n = 0` the mask is `[] ++ parity [] = [false]`, so the adversary outputs the ciphertext
it was given, and it never wins: `1 ≤ n` is needed. -/
example : ProbComp.eval ((prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length
      parity parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl)).ciOneTimeGame
      (prfChecksumCIAdversary (fun _ => 1) parity) 0) = PMF.pure false := by
  set E := prfChecksumCipher xorFamily xorFamily_polyTime xorFamily_length parity
    parity_polyTime (fun _ => 1) (by fun_prop) (fun _ => rfl)
  simp only [SymmetricCipher.ciOneTimeGame, prfChecksumCIAdversary, SymmetricCipher.maulCIAdversary,
    SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil, List.length_replicate,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk =>
    PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  let P := prfCipher xorFamily xorFamily_polyTime xorFamily_length
  have hk' : k ∈ (ProbComp.eval (P.keyGen 1)).support := hk
  have hct' : ct ∈ (ProbComp.eval (P.encrypt 1 k [false])).support := hct
  have hctLen : ct.length = 2 * 1 :=
    prfCipher_ciphertext_length xorFamily xorFamily_polyTime xorFamily_length 1 k hk' _ rfl
      ct hct'
  rw [List.take_of_length_le hctLen.le]
  rcases ct with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hctLen
  simp [ivStreamXorBody, parity]

end CslibFrontierTests.Crypto.LinearChecksum
