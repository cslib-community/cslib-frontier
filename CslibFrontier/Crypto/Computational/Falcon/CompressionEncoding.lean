/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.Compression
public import CslibFrontier.Crypto.Computational.Falcon.VerificationFrontend

/-!
# Falcon v1.2 reference compression encoding

This module emits the minimal byte string produced by the Falcon v1.2 reference
`codec.c::comp_encode` after the coefficient-range and output-capacity checks formalized in
`Cslib.Crypto.Falcon.ReferenceCompressible`. It serializes Algorithm 17's coefficient words in
most-significant-first order and adds only the zero bits needed to complete the final byte.

This minimal reference encoding is deliberately distinct from Algorithm 17's fixed-`slen` bit
string, which may contain additional whole zero bytes. The existing variable-length decoder
rejects such redundant bytes. Concrete clients exercise the encoder with that decoder; a general
codec round-trip theorem awaits a stable proof interface for the decoder's currently nested
coefficient loop and is not claimed here.

## Main definitions

* `Cslib.Crypto.Falcon.compressedPaddingLength`: the number of low zero bits in the final byte.
* `Cslib.Crypto.Falcon.paddedCompressedBits`: the exact minimal byte-aligned bit string.
* `Cslib.Crypto.Falcon.referenceCompressedBytes`: the corresponding big-endian byte string.
* `Cslib.Crypto.Falcon.referenceCompress`: the reference encoder with its exact failure boundary.

## Main results

* `Cslib.Crypto.Falcon.length_paddedCompressedBits`: minimal padding reaches the next byte.
* `Cslib.Crypto.Falcon.compressedPaddingLength_lt_eight`: no whole padding byte is emitted.
* `Cslib.Crypto.Falcon.bytesToBitsBE_referenceCompressedBytes`: byte serialization preserves the
  coefficient bits and minimal zero padding exactly.
* `Cslib.Crypto.Falcon.referenceCompress_eq_none_iff`: failure is exactly the previously stated
  reference coefficient-range or capacity failure.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Algorithms 17–18 and the paragraph following Algorithm 17.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/codec.c::comp_encode` and `comp_decode`.
-/

public section

namespace Cslib.Crypto.Falcon

/-- The number of low zero bits needed to complete the final byte of the minimal reference
encoding. -/
@[expose] def compressedPaddingLength (P : VerificationParams) (s : IntegerPolynomial P) : ℕ :=
  8 * compressedByteLength P s - compressedBitLength P s

/-- The unpadded coefficient words followed by the low zero bits needed to complete their final
byte. Unlike Algorithm 17's fixed-`slen` output, this contains no redundant whole zero byte. -/
@[expose] def paddedCompressedBits (P : VerificationParams)
    (s : IntegerPolynomial P) : List Bool :=
  compressedBits P s ++ List.replicate (compressedPaddingLength P s) false

/-- The unpadded coefficient bits fit in the byte length obtained by rounding up. -/
theorem compressedBitLength_le_eight_mul_compressedByteLength
    (P : VerificationParams) (s : IntegerPolynomial P) :
    compressedBitLength P s ≤ 8 * compressedByteLength P s := by
  unfold compressedByteLength
  omega

/-- Minimal padding reaches exactly the next byte boundary. -/
@[simp] theorem length_paddedCompressedBits (P : VerificationParams)
    (s : IntegerPolynomial P) :
    (paddedCompressedBits P s).length = 8 * compressedByteLength P s := by
  rw [paddedCompressedBits, List.length_append, List.length_replicate, length_compressedBits,
    compressedPaddingLength, Nat.add_sub_of_le
      (compressedBitLength_le_eight_mul_compressedByteLength P s)]

/-- The minimal reference encoding pads with fewer than eight zero bits. -/
theorem compressedPaddingLength_lt_eight (P : VerificationParams)
    (s : IntegerPolynomial P) : compressedPaddingLength P s < 8 := by
  unfold compressedPaddingLength compressedByteLength
  omega

/-- The minimal big-endian byte string emitted by the reference coefficient encoder after its
range and capacity checks succeed. -/
@[expose] def referenceCompressedBytes (P : VerificationParams)
    (s : IntegerPolynomial P) : ByteString :=
  (bitsToFixedBytesBE (compressedByteLength P s) (paddedCompressedBits P s)).toList

/-- The minimal reference byte string has the rounded-up coefficient-word length. -/
@[simp] theorem length_referenceCompressedBytes (P : VerificationParams)
    (s : IntegerPolynomial P) :
    (referenceCompressedBytes P s).length = compressedByteLength P s := by
  simp [referenceCompressedBytes]

/-- Reading the emitted bytes as big-endian bits recovers the coefficient words followed by their
exact minimal low zero padding. -/
@[simp] theorem bytesToBitsBE_referenceCompressedBytes (P : VerificationParams)
    (s : IntegerPolynomial P) :
    bytesToBitsBE (referenceCompressedBytes P s) = paddedCompressedBits P s := by
  exact bytesToBitsBE_bitsToFixedBytesBE (compressedByteLength P s)
    (paddedCompressedBits P s) (length_paddedCompressedBits P s)

/-- Run the minimal reference coefficient encoder with an output capacity in bytes. Success uses
the exact predicate already formalized by `ReferenceCompressible`; no second validity notion is
introduced. -/
@[expose] def referenceCompress (capacityBytes : ℕ) (P : VerificationParams)
    (s : IntegerPolynomial P) : Option ByteString :=
  if ReferenceCompressible capacityBytes P s then
    some (referenceCompressedBytes P s)
  else
    none

/-- The reference encoder fails exactly outside the coefficient-range and byte-capacity boundary
from `ReferenceCompressible`. -/
@[simp] theorem referenceCompress_eq_none_iff (capacityBytes : ℕ)
    (P : VerificationParams) (s : IntegerPolynomial P) :
    referenceCompress capacityBytes P s = none ↔
      ¬ReferenceCompressible capacityBytes P s := by
  by_cases h : ReferenceCompressible capacityBytes P s <;>
    simp [referenceCompress, h]

/-- A particular byte string is returned exactly when the reference boundary holds and it is the
minimal serialization defined above. -/
theorem referenceCompress_eq_some_iff (capacityBytes : ℕ)
    (P : VerificationParams) (s : IntegerPolynomial P) (encoded : ByteString) :
    referenceCompress capacityBytes P s = some encoded ↔
      ReferenceCompressible capacityBytes P s ∧ encoded = referenceCompressedBytes P s := by
  by_cases h : ReferenceCompressible capacityBytes P s <;>
    simp [referenceCompress, h, eq_comm]

/-- Every successful output has the exact rounded-up length and fits the supplied byte capacity. -/
theorem length_of_referenceCompress_eq_some {capacityBytes : ℕ}
    {P : VerificationParams} {s : IntegerPolynomial P} {encoded : ByteString}
    (h : referenceCompress capacityBytes P s = some encoded) :
    encoded.length = compressedByteLength P s ∧ encoded.length ≤ capacityBytes := by
  rw [referenceCompress_eq_some_iff] at h
  rcases h with ⟨hvalid, rfl⟩
  exact ⟨length_referenceCompressedBytes P s, by
    simpa only [length_referenceCompressedBytes] using hvalid.2⟩

/-- Every successful output serializes precisely the unpadded coefficient words followed by the
minimal low zero padding. -/
theorem bytesToBitsBE_of_referenceCompress_eq_some {capacityBytes : ℕ}
    {P : VerificationParams} {s : IntegerPolynomial P} {encoded : ByteString}
    (h : referenceCompress capacityBytes P s = some encoded) :
    bytesToBitsBE encoded = paddedCompressedBits P s := by
  rw [referenceCompress_eq_some_iff] at h
  exact h.2.symm ▸ bytesToBitsBE_referenceCompressedBytes P s

end Cslib.Crypto.Falcon
