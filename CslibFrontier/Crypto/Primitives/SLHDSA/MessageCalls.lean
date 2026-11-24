/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.HMAC
public import CslibFrontier.Crypto.Primitives.Hash.MGF1
public import CslibFrontier.Crypto.Primitives.SLHDSA.HashCalls

/-!
# SLH-DSA message hash and pseudorandom function calls

This module implements the two FIPS 205 hash calls that process an arbitrary-length message:
`PRF_msg` and `H_msg`. The inputs retain the exact `n`-byte seed, root, randomizer, and optional
randomness boundaries. The output of `H_msg` uses the six Table 2 digest lengths derived in
`ParameterShape.digestBytes`.

The SHAKE parameter sets use the specified direct SHAKE256 packages. The SHA2 category 1 sets
use HMAC-SHA-256 and SHA-256 followed by MGF1-SHA-256; categories 3 and 5 use the corresponding
SHA-512 functions. `prfMessage` and `hMessage` are total functions. `ValidPRFMessageInput` and
`ValidHMessageInput` state the SHA-2 source domains separately, as the HMAC and MGF1 modules do.
These two calls do not choose the optional randomness and cannot abort.

This module is definitions only: its theorems are the length equations of the byte packages. It
supplies no counts of hash, compression or permutation calls and no machine, program-size, gate,
qubit or query costs (#4987). It does not prove PRF or ITSR security, correctness of digest
slicing, signing or verification, constant-time behavior, FIPS validation, or an EUF-CMA/QROM
reduction. The test module `CslibFrontierTests.Crypto.SLHDSAMessageCalls` evaluates both calls
against values computed outside Lean.

## Main definitions

* `Cslib.Crypto.SLHDSA.prfMessage`, `hMessage`: the exact FIPS 205 calls.
* `Cslib.Crypto.SLHDSA.ValidPRFMessageInput`, `ValidHMessageInput`: inherited SHA-2 domains.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Section 4.1, Section 9,
  Table 2, Algorithm 19, and Sections 11.1--11.2.2][NISTFIPS205]
* [A. Hülsing and M. Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  Theorem 3 and Equations (5)--(6)][HulsingKudinov2022]
-/

public section

namespace Cslib.Crypto.SLHDSA

open Cslib.Crypto

/-- One standardized `m`-byte message digest. -/
abbrev MessageDigestBytes (p : SecurityBytes) (shape : ParameterShape) :=
  FixedBytes (ParameterShape.digestBytes p shape)

/-- The HMAC text `opt_rand || M` used by the SHA2 `PRF_msg` calls. -/
def prfMessageText {p : SecurityBytes} (optionalRandomness : NBytes p)
    (message : List Byte) : List Byte :=
  optionalRandomness.toList ++ message

/-- The SHAKE input `SK.prf || opt_rand || M` used by `PRF_msg`. -/
def shakePRFMessageInput {p : SecurityBytes} (secretPRF optionalRandomness : NBytes p)
    (message : List Byte) : List Byte :=
  secretPRF.toList ++ prfMessageText optionalRandomness message

/-- The common `H_msg` digest input `R || PK.seed || PK.root || M`. -/
def hMessageDigestInput {p : SecurityBytes} (randomizer publicSeed publicRoot : NBytes p)
    (message : List Byte) : List Byte :=
  randomizer.toList ++ publicSeed.toList ++ publicRoot.toList ++ message

/-- The SHA2 MGF1 seed `R || PK.seed || D`, where `D` is the inner SHA-2 digest. -/
def hMessageMGFSeed {p : SecurityBytes} {digestBytes : ℕ}
    (randomizer publicSeed : NBytes p) (digest : FixedBytes digestBytes) : List Byte :=
  randomizer.toList ++ publicSeed.toList ++ digest.toList

@[simp] theorem length_prfMessageText {p : SecurityBytes} (optionalRandomness : NBytes p)
    (message : List Byte) :
    (prfMessageText optionalRandomness message).length = p.count + message.length := by
  simp [prfMessageText]

@[simp] theorem length_shakePRFMessageInput {p : SecurityBytes}
    (secretPRF optionalRandomness : NBytes p) (message : List Byte) :
    (shakePRFMessageInput secretPRF optionalRandomness message).length =
      2 * p.count + message.length := by
  simp only [shakePRFMessageInput, List.length_append, FixedBytes.length_toList,
    length_prfMessageText]
  omega

@[simp] theorem length_hMessageDigestInput {p : SecurityBytes}
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte) :
    (hMessageDigestInput randomizer publicSeed publicRoot message).length =
      3 * p.count + message.length := by
  simp only [hMessageDigestInput, List.length_append, FixedBytes.length_toList]
  omega

@[simp] theorem length_hMessageMGFSeed {p : SecurityBytes} {digestBytes : ℕ}
    (randomizer publicSeed : NBytes p) (digest : FixedBytes digestBytes) :
    (hMessageMGFSeed randomizer publicSeed digest).length = 2 * p.count + digestBytes := by
  simp only [hMessageMGFSeed, List.length_append, FixedBytes.length_toList]
  omega

/-- The source domain of `PRF_msg`.

SHAKE256 accepts every finite byte message. The SHA2 branches are exactly the HMAC input
predicate selected by FIPS 205. `prfMessage` is total and does not take this as an argument. -/
@[expose]
def ValidPRFMessageInput (family : HashFamily) {p : SecurityBytes}
    (secretPRF optionalRandomness : NBytes p) (message : List Byte) : Prop :=
  match family, p with
  | .shake, _ => True
  | .sha2, .bytes16 =>
      HMAC.ValidHMACSHA256Input secretPRF.toList
        (prfMessageText optionalRandomness message)
  | .sha2, .bytes24 =>
      HMAC.ValidHMACSHA512Input secretPRF.toList
        (prfMessageText optionalRandomness message)
  | .sha2, .bytes32 =>
      HMAC.ValidHMACSHA512Input secretPRF.toList
        (prfMessageText optionalRandomness message)

instance (family : HashFamily) {p : SecurityBytes}
    (secretPRF optionalRandomness : NBytes p) (message : List Byte) :
    Decidable (ValidPRFMessageInput family secretPRF optionalRandomness message) := by
  unfold ValidPRFMessageInput
  cases family <;> cases p <;> infer_instance

/-- FIPS 205 `PRF_msg(SK.prf, opt_rand, M)` from Sections 11.1--11.2.2. -/
def prfMessage (family : HashFamily) {p : SecurityBytes}
    (secretPRF optionalRandomness : NBytes p) (message : List Byte) : NBytes p :=
  match family with
  | .shake =>
      FixedBytes.ofListExact
        (Keccak.shake256 (shakePRFMessageInput secretPRF optionalRandomness message) p.count)
        (Keccak.length_shake256 _ _)
  | .sha2 =>
      match p with
      | .bytes16 =>
          Fin.take 16 (by decide)
            (HMAC.hmacSHA256 secretPRF.toList (prfMessageText optionalRandomness message))
      | .bytes24 =>
          Fin.take 24 (by decide)
            (HMAC.hmacSHA512 secretPRF.toList (prfMessageText optionalRandomness message))
      | .bytes32 =>
          Fin.take 32 (by decide)
            (HMAC.hmacSHA512 secretPRF.toList (prfMessageText optionalRandomness message))

/-- The source domain of `H_msg`.

The first conjunct is the inner SHA-2 digest domain. The remaining conjuncts are the MGF1 seed and
output bounds after substituting the fixed seed length. `hMessage` is total and does not take this
as an argument. -/
@[expose]
def ValidHMessageInput (family : HashFamily) {p : SecurityBytes} (shape : ParameterShape)
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte) : Prop :=
  match family, p with
  | .shake, _ => True
  | .sha2, .bytes16 =>
      SHA2.ValidSHA256Input
          (hMessageDigestInput randomizer publicSeed publicRoot message) ∧
        (ParameterShape.digestBytes p shape = 0 ∨ 2 * p.count + 32 + 4 < 2 ^ 61) ∧
        ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 32
  | .sha2, .bytes24 =>
      SHA2.ValidSHA512Input
          (hMessageDigestInput randomizer publicSeed publicRoot message) ∧
        (ParameterShape.digestBytes p shape = 0 ∨ 2 * p.count + 64 + 4 < 2 ^ 125) ∧
        ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 64
  | .sha2, .bytes32 =>
      SHA2.ValidSHA512Input
          (hMessageDigestInput randomizer publicSeed publicRoot message) ∧
        (ParameterShape.digestBytes p shape = 0 ∨ 2 * p.count + 64 + 4 < 2 ^ 125) ∧
        ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 64

instance (family : HashFamily) {p : SecurityBytes} (shape : ParameterShape)
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte) :
    Decidable (ValidHMessageInput family shape randomizer publicSeed publicRoot message) := by
  unfold ValidHMessageInput
  cases family <;> cases p <;> infer_instance

/-- FIPS 205 `H_msg(R, PK.seed, PK.root, M)` from Sections 11.1--11.2.2. -/
def hMessage (family : HashFamily) {p : SecurityBytes} (shape : ParameterShape)
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte) :
    MessageDigestBytes p shape :=
  match family with
  | .shake =>
      FixedBytes.ofListExact
        (Keccak.shake256 (hMessageDigestInput randomizer publicSeed publicRoot message)
          (ParameterShape.digestBytes p shape))
        (Keccak.length_shake256 _ _)
  | .sha2 =>
      match p with
      | .bytes16 =>
          let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
          let digest := SHA2.sha256 digestInput
          let seed := hMessageMGFSeed randomizer publicSeed digest
          MGF1.mgf1SHA256 seed (ParameterShape.digestBytes .bytes16 shape)
      | .bytes24 =>
          let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
          let digest := SHA2.sha512 digestInput
          let seed := hMessageMGFSeed randomizer publicSeed digest
          MGF1.mgf1SHA512 seed (ParameterShape.digestBytes .bytes24 shape)
      | .bytes32 =>
          let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
          let digest := SHA2.sha512 digestInput
          let seed := hMessageMGFSeed randomizer publicSeed digest
          MGF1.mgf1SHA512 seed (ParameterShape.digestBytes .bytes32 shape)

end Cslib.Crypto.SLHDSA
