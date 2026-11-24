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
SHA-512 functions. `prfMessage` and `hMessage` are total functions. FIPS 180-4 defines SHA-2 only
below a message-length limit, and the docstring of each call states the resulting bound on `M`.
These two calls do not choose the optional randomness and cannot abort.

This module is definitions only: its theorems are the length equations of the byte packages. It
supplies no counts of hash, compression or permutation calls and no machine, program-size, gate,
qubit or query costs (#4987). It does not prove PRF or ITSR security, correctness of digest
slicing, signing or verification, constant-time behavior, FIPS validation, or an EUF-CMA/QROM
reduction. The test module `CslibFrontierTests.Crypto.SLHDSAMessageCalls` evaluates both calls
against values computed outside Lean.

## Main definitions

* `Cslib.Crypto.SLHDSA.prfMessage`, `hMessage`: the exact FIPS 205 calls.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Section 4.1, Section 9,
  Table 2, Algorithm 19, and Sections 11.1--11.2.2][NISTFIPS205]
* [A. Hülsing and M. Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  Theorem 3 and Equations (5)--(6)][HulsingKudinov2022], cited for the security properties the
  SPHINCS+ proof requires of these two calls; no declaration here states or proves them.
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

/-- FIPS 205 `PRF_msg(SK.prf, opt_rand, M)` from Sections 11.1--11.2.2.

The SHAKE branch is the FIPS 205 value for every message. In the SHA2 branch the inner HMAC hash
reads one padded key block followed by `opt_rand ‖ M`, and FIPS 180-4 defines SHA-256 only below
`2 ^ 61` input bytes and SHA-512 only below `2 ^ 125`. The SHA2 branch is therefore the FIPS 205
value when `64 + n + |M| < 2 ^ 61` at `n = 16` and when `128 + n + |M| < 2 ^ 125` at
`n = 24, 32`. For a longer message the standards define no value, and this function returns what
the total evaluators `HMAC.hmacSHA256` and `HMAC.hmacSHA512` return. -/
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
      | .bytes24 | .bytes32 =>
          Fin.take _ (by decide)
            (HMAC.hmacSHA512 secretPRF.toList (prfMessageText optionalRandomness message))

/-- FIPS 205 `H_msg(R, PK.seed, PK.root, M)` from Sections 11.1--11.2.2.

The SHAKE branch is the FIPS 205 value for every message. In the SHA2 branch the inner digest
hashes `R ‖ PK.seed ‖ PK.root ‖ M`, and FIPS 180-4 defines SHA-256 only below `2 ^ 61` input bytes
and SHA-512 only below `2 ^ 125`. The SHA2 branch is therefore the FIPS 205 value when
`3 * n + |M| < 2 ^ 61` at `n = 16` and when `3 * n + |M| < 2 ^ 125` at `n = 24, 32`. For a longer
message the standards define no value, and this function returns what the total evaluators
`SHA2.sha256` and `SHA2.sha512` return. The MGF1 step adds no condition: its seed has the fixed
length `2 * n + 32` or `2 * n + 64` and its output has at most 49 bytes. -/
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
      | .bytes24 | .bytes32 =>
          let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
          let digest := SHA2.sha512 digestInput
          let seed := hMessageMGFSeed randomizer publicSeed digest
          MGF1.mgf1SHA512 seed (ParameterShape.digestBytes _ shape)

end Cslib.Crypto.SLHDSA
