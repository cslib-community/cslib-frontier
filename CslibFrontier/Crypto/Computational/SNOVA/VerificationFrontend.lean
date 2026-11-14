/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.Hash.Keccak

/-!
# SNOVA v3.0 verification frontend

This module formalizes the byte-level part of SNOVA v3.0 verification ([SNOVA2026], Algorithms 2,
12, 20 and 21). It implements the eight grouped base-`q` encodings from Table 4, including the
legality check for externally supplied signatures; computes the verification hash from the
48-byte public-key digest, 64-byte message digest and final 16-byte salt; applies Algorithm 12's
`o × l × r` reindexing; and parses Algorithm 20's signature matrices.

`verifyWithXof` exposes Algorithm 21's remaining public-map boundary as a callback. The callback
receives the original public-key bytes and decoded signature matrices, and may reject a malformed
public key. Verification accepts exactly when its result equals the complete Algorithm 12 hash.
This module does not define public-key expansion or the twisted public map, and makes no claim
about MBS, EUF-CMA, ROM/QROM security or any reductionist security theorem. Section 6.2 of the
SNOVA specification explicitly says that no general reductionist security proof is known.

## Main definitions

* `Cslib.Crypto.SNOVA.Encoding`: the eight Table 4 grouped base-`q` encodings.
* `Cslib.Crypto.SNOVA.decodeCoefficients`, `Cslib.Crypto.SNOVA.decodeExternal`: Algorithm 2
  decoding without and with the external-input legality check.
* `Cslib.Crypto.SNOVA.verificationHashWithXof`: Algorithm 12 with an explicit typed-length XOF.
* `Cslib.Crypto.SNOVA.decodeSignature`: Algorithm 20's exact signature parser.
* `Cslib.Crypto.SNOVA.verifyWithXof`: Algorithm 21's verification equation with a supplied
  public-map evaluator.

## References

* [Lih-Chung Wang et al., *SNOVA: Proposal for NIST PQC: Additional Digital Signature Schemes*,
  version 3.0][SNOVA2026], Sections 1.5.3 and 1.8, Table 4, and Algorithms 2, 10, 12, 20 and 21;
  PDF SHA-256
  `67bf2e5414001d4562f76fff77cbc72b6c997ff2cffef3b5180a886359892898`.
* SNOVA Round-3 reference implementation, commit
  `d88ef38bfa28587372f29f10482aa208c703f1aa`, `src/snova.h` and `src/snova_ref.c`.
-/

public section

namespace Cslib.Crypto.SNOVA

/-- One of the eight grouped field-element encodings in [SNOVA2026], Table 4. The constructor
name records the field order `q`. -/
inductive Encoding where
  /-- The `q = 11`, `Nq = 16`, `Nb = 7` encoding. -/
  | q11
  /-- The `q = 13`, `Nq = 15`, `Nb = 7` encoding. -/
  | q13
  /-- The `q = 16`, `Nq = 2`, `Nb = 1` encoding. -/
  | q16
  /-- The `q = 17`, `Nq = 15`, `Nb = 8` encoding. -/
  | q17
  /-- The `q = 19`, `Nq = 15`, `Nb = 8` encoding. -/
  | q19
  /-- The `q = 23`, `Nq = 7`, `Nb = 4` encoding. -/
  | q23
  /-- The `q = 29`, `Nq = 13`, `Nb = 8` encoding. -/
  | q29
  /-- The `q = 31`, `Nq = 8`, `Nb = 5` encoding. -/
  | q31
  deriving DecidableEq, Repr

namespace Encoding

/-- The field order `q` selected by a Table 4 encoding. -/
@[expose] def modulus : Encoding → ℕ
  | .q11 => 11
  | .q13 => 13
  | .q16 => 16
  | .q17 => 17
  | .q19 => 19
  | .q23 => 23
  | .q29 => 29
  | .q31 => 31

/-- The number `Nq` of base-`q` digits in a full encoded group. -/
@[expose] def elementsPerGroup : Encoding → ℕ
  | .q11 => 16
  | .q13 => 15
  | .q16 => 2
  | .q17 => 15
  | .q19 => 15
  | .q23 => 7
  | .q29 => 13
  | .q31 => 8

/-- The number `Nb` of little-endian bytes in a full encoded group. -/
@[expose] def bytesPerGroup : Encoding → ℕ
  | .q11 => 7
  | .q13 => 7
  | .q16 => 1
  | .q17 => 8
  | .q19 => 8
  | .q23 => 4
  | .q29 => 8
  | .q31 => 5

/-- Every supported field order is positive. -/
@[simp] theorem modulus_pos (encoding : Encoding) : 0 < encoding.modulus := by
  cases encoding <;> decide

/-- Every supported encoding has a positive number of elements per group. -/
@[simp] theorem elementsPerGroup_pos (encoding : Encoding) : 0 < encoding.elementsPerGroup := by
  cases encoding <;> decide

end Encoding

/-- The dimensions needed by SNOVA's byte-level verification frontend. The source dimension
`n` is derived as `v + o`. -/
structure VerificationParams where
  /-- Table 4 field-element encoding. -/
  encoding : Encoding
  /-- Number `v` of vinegar matrix variables. -/
  v : ℕ
  /-- Number `o` of oil matrix variables and hash blocks. -/
  o : ℕ
  /-- Number `l` of rows in each signature matrix. -/
  l : ℕ
  /-- Number `r` of columns in each signature matrix. -/
  r : ℕ
  deriving DecidableEq, Repr

namespace VerificationParams

/-- The number `n = v + o` of signature matrices. -/
@[expose] def n (P : VerificationParams) : ℕ := P.v + P.o

/-- The number `n·l·r` of field elements in Algorithm 20's encoded signature payload. -/
@[expose] def signatureCoefficientCount (P : VerificationParams) : ℕ := P.n * P.l * P.r

/-- The number `o·l·r` of field elements in Algorithm 12's verification hash. -/
@[expose] def hashCoefficientCount (P : VerificationParams) : ℕ := P.o * P.l * P.r

end VerificationParams

/-- One field element represented by its canonical integer in `0,...,q-1`. This frontend uses
only the representation; field operations belong to the separate public-map development. -/
abbrev FieldElement (P : VerificationParams) := Fin P.encoding.modulus

instance (P : VerificationParams) : NeZero P.encoding.modulus :=
  ⟨(Encoding.modulus_pos P.encoding).ne'⟩

/-- Number of bytes used for `count` field elements. This is the specification/reference formula
`ceil(Nb * count / Nq)`, so a final partial group need not occupy all `Nb` bytes. -/
@[expose] def encodedByteCount (encoding : Encoding) (count : ℕ) : ℕ :=
  (encoding.bytesPerGroup * count + encoding.elementsPerGroup - 1) /
    encoding.elementsPerGroup

/-- Number of base-`q` groups needed for `count` field elements. -/
private def groupCount (encoding : Encoding) (count : ℕ) : ℕ :=
  (count + encoding.elementsPerGroup - 1) / encoding.elementsPerGroup

/-- Number of requested digits in one group, including a possibly partial final group. -/
private def groupDigitCount (encoding : Encoding) (count group : ℕ) : ℕ :=
  min encoding.elementsPerGroup (count - group * encoding.elementsPerGroup)

/-- Interpret bytes in the little-endian order of Algorithms 1 and 2. -/
private def littleEndianNat : List Byte → ℕ
  | [] => 0
  | byte :: bytes => byte.val + 256 * littleEndianNat bytes

/-- The bytes occupied by a numbered conversion group. -/
private def encodedGroup (encoding : Encoding) (encoded : List Byte) (group : ℕ) : List Byte :=
  (encoded.drop (group * encoding.bytesPerGroup)).take encoding.bytesPerGroup

/-- Decode one little-endian integer into its requested low base-`q` digits. -/
private def decodeGroup (P : VerificationParams) (count : ℕ)
    (encoded : List Byte) : List (FieldElement P) :=
  (List.range count).map fun i =>
    ⟨littleEndianNat encoded / P.encoding.modulus ^ i % P.encoding.modulus,
      Nat.mod_lt _ (Encoding.modulus_pos P.encoding)⟩

/-- Decode `count` coefficients by [SNOVA2026], Algorithm 2, without applying the legality check.

Algorithm 12 uses this conversion for SHAKE256 output without rejecting unused quotient digits.
Externally supplied public keys and signatures must instead use `decodeExternal`. -/
@[expose] def decodeCoefficients (P : VerificationParams) (count : ℕ)
    (encoded : List Byte) : List (FieldElement P) :=
  (List.range (groupCount P.encoding count)).flatMap fun group =>
    decodeGroup P (groupDigitCount P.encoding count group)
      (encodedGroup P.encoding encoded group)

/-- Whether an external byte string is the exact source length and every group has zero quotient
after all requested base-`q` digits have been removed. This is Algorithm 2's public-key/signature
legality check. -/
@[expose] def legalExternalEncoding (encoding : Encoding) (count : ℕ)
    (encoded : List Byte) : Bool :=
  encoded.length == encodedByteCount encoding count &&
    (List.range (groupCount encoding count)).all fun group =>
      let digits := groupDigitCount encoding count group
      littleEndianNat (encodedGroup encoding encoded group) /
          encoding.modulus ^ digits == 0

/-- Decode an externally supplied public-key or signature coefficient string, rejecting a wrong
length or nonzero unused quotient as required by Algorithm 2. -/
@[expose] def decodeExternal (P : VerificationParams) (count : ℕ)
    (encoded : List Byte) : Option (List (FieldElement P)) :=
  if legalExternalEncoding P.encoding count encoded then
    some (decodeCoefficients P count encoded)
  else
    none

/-- Number of bytes in Algorithm 20's compressed matrix payload, excluding the 16-byte salt. -/
@[expose] def VerificationParams.signaturePayloadBytes (P : VerificationParams) : ℕ :=
  encodedByteCount P.encoding P.signatureCoefficientCount

/-- Exact byte length of an Algorithm 20 signature, including its final 16-byte salt. -/
@[expose] def VerificationParams.signatureBytes (P : VerificationParams) : ℕ :=
  P.signaturePayloadBytes + 16

/-- Number of SHAKE256 output bytes consumed by Algorithm 12's verification hash. -/
@[expose] def VerificationParams.hashBytes (P : VerificationParams) : ℕ :=
  encodedByteCount P.encoding P.hashCoefficientCount

/-- Algorithm 20's matrix view `U[i][i1][j1]` of the signature coefficients. -/
abbrev SignatureMatrices (P : VerificationParams) :=
  Fin P.n → Fin P.l → Fin P.r → FieldElement P

/-- A successfully parsed Algorithm 20 signature. -/
structure DecodedSignature (P : VerificationParams) where
  /-- The `n` decoded `l × r` matrices in source order. -/
  matrices : SignatureMatrices P
  /-- The final 16 signature bytes, used by Algorithm 12 as the salt. -/
  salt : FixedBytes 16

/-- Parse [SNOVA2026], Algorithm 20. The input must have the exact parameter-dependent signature
length; its coefficient payload must pass Algorithm 2's external-input legality check; and its
final 16 bytes become the salt. -/
@[expose] def decodeSignature (P : VerificationParams)
    (signature : List Byte) : Option (DecodedSignature P) :=
  if signature.length = P.signatureBytes then
    match decodeExternal P P.signatureCoefficientCount
        (signature.take P.signaturePayloadBytes) with
    | none => none
    | some coefficients =>
        some {
          matrices := fun i i1 j1 =>
            coefficients.getD (i.val * P.l * P.r + i1.val * P.r + j1.val) 0
          salt := fun i => signature.getD (P.signaturePayloadBytes + i.val) 0
        }
  else
    none

/-- A typed-length extendable-output function interface. The second argument is the exact number
of requested output bytes. It records only the deterministic byte interface, not any cryptographic
property. -/
abbrev XOF := (input : List Byte) → (outputBytes : ℕ) → FixedBytes outputBytes

/-- The concrete FIPS 202 SHAKE256 implementation at the typed-length XOF interface. -/
@[expose] def shake256XOF : XOF := fun input outputBytes i =>
  (Keccak.shake256 input outputBytes).getD i.val 0

/-- Algorithm 12's exact SHAKE256 input: the 48-byte public-key digest, then the 64-byte message
digest, then the 16-byte salt. -/
@[expose] def verificationHashInputWithXof (xof : XOF) (publicKey message : List Byte)
    (salt : FixedBytes 16) : List Byte :=
  (xof publicKey 48).toList ++ (xof message 64).toList ++ salt.toList

/-- Reindex Algorithm 12's decoded `d[i][j1][i1]` coefficients into the flattened
`mh[i][i1][j1]` order used by the public map. -/
@[expose] def reorderVerificationHash (P : VerificationParams)
    (decoded : List (FieldElement P)) : List (FieldElement P) :=
  (List.range P.o).flatMap fun i =>
    (List.range P.l).flatMap fun i1 =>
      (List.range P.r).map fun j1 =>
        decoded.getD (i * P.r * P.l + j1 * P.l + i1) 0

/-- [SNOVA2026], Algorithm 12 with an explicit typed-length XOF. XOF output is decoded without
Algorithm 2's external-input legality rejection, then transposed into public-map order. -/
@[expose] def verificationHashWithXof (P : VerificationParams) (xof : XOF)
    (publicKey message : List Byte) (salt : FixedBytes 16) : List (FieldElement P) :=
  let hashBytes := (xof (verificationHashInputWithXof xof publicKey message salt) P.hashBytes).toList
  reorderVerificationHash P (decodeCoefficients P P.hashCoefficientCount hashBytes)

/-- Algorithm 12 instantiated with the concrete FIPS 202 SHAKE256 implementation. -/
@[expose] def verificationHash (P : VerificationParams) (publicKey message : List Byte)
    (salt : FixedBytes 16) : List (FieldElement P) :=
  verificationHashWithXof P shake256XOF publicKey message salt

/-- The separately supplied Algorithm 21 boundary for public-key expansion and public-map
evaluation. Returning `none` rejects a malformed or unsupported public key. -/
abbrev PublicMapEvaluator (P : VerificationParams) :=
  List Byte → SignatureMatrices P → Option (List (FieldElement P))

/-- [SNOVA2026], Algorithm 21 with an explicit typed-length XOF and public-map evaluator.

Malformed signatures and public keys are rejected. Otherwise this checks the complete source
equation `P*(U) = Hash(SHAKE256(pk, 48) || SHAKE256(message, 64) || salt)`. -/
@[expose] def verifyWithXof (P : VerificationParams) (xof : XOF)
    (evaluatePublic : PublicMapEvaluator P)
    (publicKey message signature : List Byte) : Bool :=
  match decodeSignature P signature with
  | none => false
  | some decoded =>
      match evaluatePublic publicKey decoded.matrices with
      | none => false
      | some evaluated =>
          evaluated == verificationHashWithXof P xof publicKey message decoded.salt

/-- Algorithm 21 instantiated with the concrete FIPS 202 SHAKE256 implementation. -/
@[expose] def verify (P : VerificationParams) (evaluatePublic : PublicMapEvaluator P)
    (publicKey message signature : List Byte) : Bool :=
  verifyWithXof P shake256XOF evaluatePublic publicKey message signature

end Cslib.Crypto.SNOVA
