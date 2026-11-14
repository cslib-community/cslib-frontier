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
import Mathlib.Tactic

/-!
# SLH-DSA message hash and pseudorandom function calls

This module implements the two FIPS 205 hash calls that process an arbitrary-length message:
`PRF_msg` and `H_msg`. The inputs retain the exact `n`-byte seed, root, randomizer, and optional
randomness boundaries. The output of `H_msg` uses the six Table 2 digest lengths derived in
`ParameterShape.digestBytes`.

The SHAKE parameter sets use the specified direct SHAKE256 packages. The SHA2 category 1 sets
use HMAC-SHA-256 and SHA-256 followed by MGF1-SHA-256; categories 3 and 5 use the corresponding
SHA-512 functions. The SHA-2 source domains are erased proof preconditions, not runtime failure
branches. These two calls do not choose the optional randomness and cannot abort.

The source-cost definitions count exact byte packages, SHA-2 compression calls, and Keccak-f[1600]
evaluations in the current executable definitions. They are not a machine-cost certificate: no
compiled program, oracle handler, advice, layout, copy, interpreter, emitted-output, gate, or qubit
cost is supplied here. The pure calls use no oracle handler. With the standardized `n` and `m`,
both source counts are linear in the message length.

This module does not prove PRF or ITSR security, correctness of digest slicing, signing or
verification, constant-time behavior, FIPS validation, or an EUF-CMA/QROM reduction.

## Main definitions

* `Cslib.Crypto.SLHDSA.prfMessage`, `hMessage`: the exact FIPS 205 calls.
* `Cslib.Crypto.SLHDSA.ValidPRFMessageInput`, `ValidHMessageInput`: inherited SHA-2 domains.
* `Cslib.Crypto.SLHDSA.prfMessageCost`, `hMessageCost`: source-level component counts.

## Main results

* `Cslib.Crypto.SLHDSA.length_prfMessageText`, `length_hMessageDigestInput`: exact packages.
* `Cslib.Crypto.SLHDSA.oracleHandlerCount_eq`: the pure source functions use no oracle handler.

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
  simp [shakePRFMessageInput]
  omega

@[simp] theorem length_hMessageDigestInput {p : SecurityBytes}
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte) :
    (hMessageDigestInput randomizer publicSeed publicRoot message).length =
      3 * p.count + message.length := by
  simp [hMessageDigestInput]
  omega

@[simp] theorem length_hMessageMGFSeed {p : SecurityBytes} {digestBytes : ℕ}
    (randomizer publicSeed : NBytes p) (digest : FixedBytes digestBytes) :
    (hMessageMGFSeed randomizer publicSeed digest).length = 2 * p.count + digestBytes := by
  simp [hMessageMGFSeed]
  omega

/-- The source-domain obligation for `PRF_msg`.

SHAKE256 accepts every finite byte message. The SHA2 branches expose exactly the HMAC input
predicate selected by FIPS 205. -/
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
    (secretPRF optionalRandomness : NBytes p) (message : List Byte)
    (hinput : ValidPRFMessageInput family secretPRF optionalRandomness message) : NBytes p :=
  match family, p with
  | .shake, _ =>
      FixedBytes.ofListExact
        (Keccak.shake256 (shakePRFMessageInput secretPRF optionalRandomness message) p.count)
        (Keccak.length_shake256 _ _)
  | .sha2, .bytes16 =>
      (HMAC.hmacSHA256 secretPRF.toList (prfMessageText optionalRandomness message) (by
        simpa [ValidPRFMessageInput] using hinput)).take 16 (by decide)
  | .sha2, .bytes24 =>
      (HMAC.hmacSHA512 secretPRF.toList (prfMessageText optionalRandomness message) (by
        simpa [ValidPRFMessageInput] using hinput)).take 24 (by decide)
  | .sha2, .bytes32 =>
      (HMAC.hmacSHA512 secretPRF.toList (prfMessageText optionalRandomness message) (by
        simpa [ValidPRFMessageInput] using hinput)).take 32 (by decide)

/-- The source-domain obligation for `H_msg`.

The first conjunct is the inner SHA-2 digest domain. The remaining conjuncts are the MGF1 seed and
output bounds after substituting the fixed seed length. These are proof preconditions rather than
runtime errors. -/
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
    (randomizer publicSeed publicRoot : NBytes p) (message : List Byte)
    (hinput : ValidHMessageInput family shape randomizer publicSeed publicRoot message) :
    MessageDigestBytes p shape :=
  match family, p with
  | .shake, _ =>
      FixedBytes.ofListExact
        (Keccak.shake256 (hMessageDigestInput randomizer publicSeed publicRoot message)
          (ParameterShape.digestBytes p shape))
        (Keccak.length_shake256 _ _)
  | .sha2, .bytes16 =>
      let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
      let digest := SHA2.sha256 digestInput (by
        simpa [ValidHMessageInput] using hinput.1)
      let seed := hMessageMGFSeed randomizer publicSeed digest
      MGF1.mgf1SHA256 seed (ParameterShape.digestBytes p shape) (by
        change
          (ParameterShape.digestBytes p shape = 0 ∨ seed.length + 4 < 2 ^ 61) ∧
            ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 32
        simpa [seed] using hinput.2)
  | .sha2, .bytes24 =>
      let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
      let digest := SHA2.sha512 digestInput (by
        simpa [ValidHMessageInput] using hinput.1)
      let seed := hMessageMGFSeed randomizer publicSeed digest
      MGF1.mgf1SHA512 seed (ParameterShape.digestBytes p shape) (by
        change
          (ParameterShape.digestBytes p shape = 0 ∨ seed.length + 4 < 2 ^ 125) ∧
            ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 64
        simpa [seed] using hinput.2)
  | .sha2, .bytes32 =>
      let digestInput := hMessageDigestInput randomizer publicSeed publicRoot message
      let digest := SHA2.sha512 digestInput (by
        simpa [ValidHMessageInput] using hinput.1)
      let seed := hMessageMGFSeed randomizer publicSeed digest
      MGF1.mgf1SHA512 seed (ParameterShape.digestBytes p shape) (by
        change
          (ParameterShape.digestBytes p shape = 0 ∨ seed.length + 4 < 2 ^ 125) ∧
            ParameterShape.digestBytes p shape ≤ 2 ^ 32 * 64
        simpa [seed] using hinput.2)

/-! ### Source-level component counts -/

/-- Number of padded SHAKE256 rate blocks for a byte-aligned input. The added six bits are the
four-bit SHAKE suffix and the two mandatory endpoints of `pad10*1`. -/
def shakeAbsorbBlocks (inputBytes : ℕ) : ℕ := (8 * inputBytes + 6) ⌈/⌉ 1088

/-- Number of SHAKE256 rate blocks needed for the requested bytes. -/
def shakeSqueezeBlocks (outputBytes : ℕ) : ℕ := outputBytes ⌈/⌉ 136

/-- Keccak-f evaluations in the current sponge: one per absorbed block and one between consecutive
squeezing blocks. The standardized outputs are nonempty. -/
def shakePermutationCount (inputBytes outputBytes : ℕ) : ℕ :=
  shakeAbsorbBlocks inputBytes + shakeSqueezeBlocks outputBytes - 1

/-- Number of SHA-256 compression blocks after byte-aligned FIPS 180-4 padding. -/
def sha256CompressionBlocks (inputBytes : ℕ) : ℕ := (inputBytes + 9) ⌈/⌉ 64

/-- Number of SHA-512 compression blocks after byte-aligned FIPS 180-4 padding. -/
def sha512CompressionBlocks (inputBytes : ℕ) : ℕ := (inputBytes + 17) ⌈/⌉ 128

/-- Exact dynamic component counts for one source-level message call. `packagedBytes` totals the
inputs presented to primitive hashes; `outputBytes` is the exposed call result. -/
structure MessageCallCost where
  packagedBytes : ℕ
  outputBytes : ℕ
  keccakPermutations : ℕ
  sha256Compressions : ℕ
  sha512Compressions : ℕ
  deriving DecidableEq, Repr

/-- Component counts for `PRF_msg` on a message of `messageBytes` bytes. -/
def prfMessageCost (family : HashFamily) (p : SecurityBytes) (messageBytes : ℕ) :
    MessageCallCost :=
  match family, p with
  | .shake, _ =>
      ⟨2 * p.count + messageBytes, p.count,
        shakePermutationCount (2 * p.count + messageBytes) p.count, 0, 0⟩
  | .sha2, .bytes16 =>
      ⟨64 + p.count + messageBytes + (64 + 32), p.count, 0,
        sha256CompressionBlocks (64 + p.count + messageBytes) +
          sha256CompressionBlocks (64 + 32), 0⟩
  | .sha2, .bytes24 =>
      ⟨128 + p.count + messageBytes + (128 + 64), p.count, 0, 0,
        sha512CompressionBlocks (128 + p.count + messageBytes) +
          sha512CompressionBlocks (128 + 64)⟩
  | .sha2, .bytes32 =>
      ⟨128 + p.count + messageBytes + (128 + 64), p.count, 0, 0,
        sha512CompressionBlocks (128 + p.count + messageBytes) +
          sha512CompressionBlocks (128 + 64)⟩

/-- Component counts for `H_msg` on a message of `messageBytes` bytes. -/
def hMessageCost (family : HashFamily) (p : SecurityBytes) (shape : ParameterShape)
    (messageBytes : ℕ) : MessageCallCost :=
  let m := ParameterShape.digestBytes p shape
  match family, p with
  | .shake, _ =>
      ⟨3 * p.count + messageBytes, m,
        shakePermutationCount (3 * p.count + messageBytes) m, 0, 0⟩
  | .sha2, .bytes16 =>
      ⟨3 * p.count + messageBytes + (m ⌈/⌉ 32) * (2 * p.count + 32 + 4), m, 0,
        sha256CompressionBlocks (3 * p.count + messageBytes) +
          (m ⌈/⌉ 32) * sha256CompressionBlocks (2 * p.count + 32 + 4), 0⟩
  | .sha2, .bytes24 =>
      ⟨3 * p.count + messageBytes + (m ⌈/⌉ 64) * (2 * p.count + 64 + 4), m, 0, 0,
        sha512CompressionBlocks (3 * p.count + messageBytes) +
          (m ⌈/⌉ 64) * sha512CompressionBlocks (2 * p.count + 64 + 4)⟩
  | .sha2, .bytes32 =>
      ⟨3 * p.count + messageBytes + (m ⌈/⌉ 64) * (2 * p.count + 64 + 4), m, 0, 0,
        sha512CompressionBlocks (3 * p.count + messageBytes) +
          (m ⌈/⌉ 64) * sha512CompressionBlocks (2 * p.count + 64 + 4)⟩

/-- Static Keccak rotation-offset entries reused by SHAKE256. -/
def keccakRotationTableEntries : ℕ := 25

/-- Static Keccak round constants reused by SHAKE256. -/
def keccakRoundConstantEntries : ℕ := 24

/-- Static SHA-256 round constants reused by the SHA2 calls. -/
def sha256RoundConstantEntries : ℕ := 64

/-- Static SHA-512 round constants reused by the SHA2 calls. -/
def sha512RoundConstantEntries : ℕ := 80

/-- Initial-state words in either SHA-2 branch. -/
def sha2InitialStateWords : ℕ := 8

/-- The two scalar HMAC pad values, `ipad` and `opad`. -/
def hmacPadConstants : ℕ := 2

/-- Bytes in each generated MGF1 counter; the counters are not stored in a static table. -/
def mgfCounterBytes : ℕ := 4

/-- The six Table 2 digest-length values. -/
def digestLengthTableEntries : ℕ := 6

/-- Oracle handlers installed by either pure executable message call. -/
def oracleHandlerCount : ℕ := 0

/-- These pure executable message calls install no oracle handler. -/
theorem oracleHandlerCount_eq : oracleHandlerCount = 0 := rfl

end Cslib.Crypto.SLHDSA
