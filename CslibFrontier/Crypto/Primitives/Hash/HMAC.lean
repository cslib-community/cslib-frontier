/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.SHA2
import Mathlib.Data.List.GetD

/-!
# HMAC with SHA-256 and SHA-512

This module implements the two SHA-2 HMAC functions incorporated by FIPS 205. Keys shorter than
the hash block are padded on the right with zero bytes, block-sized keys are used unchanged, and
longer keys are first hashed and then padded. The inner and outer pad bytes are respectively
`0x36` and `0x5c`, repeated to the SHA-2 block size.

The public validity predicates record the input domains prescribed by the underlying SHA-256 and
SHA-512 standards separately from the total executable functions. HMAC returns the full 32-byte or
64-byte digest; applications that prescribe truncation, such as FIPS 205 `PRF_msg`, apply it at
their own boundary.

This is an executable specification. It is not a constant-time implementation, a machine-costed
program, a validation claim, or a proof that HMAC is a pseudorandom function or a secure MAC.

## Main definitions

* `Cslib.Crypto.HMAC.ValidHMACSHA256Input`, `ValidHMACSHA512Input`: SHA-2 input domains.
* `Cslib.Crypto.HMAC.hmacSHA256`, `hmacSHA512`: full-length SHA-2 HMAC functions.

## Main results

* `Cslib.Crypto.HMAC.hmacSHA256_append_zeros`, `hmacSHA512_append_zeros`: adding zero bytes
  to a key that remains at most one hash block does not change HMAC.

## References

* [NIST, *The Keyed-Hash Message Authentication Code (HMAC)*, Sections 2.3--4][NISTFIPS1981]
-/

public section

namespace Cslib.Crypto.HMAC

open Cslib.Crypto

/-- The SHA-256 HMAC source domain: a long key must be hashable, and the inner hash input must be
inside SHA-256's byte-aligned input domain. -/
@[expose] def ValidHMACSHA256Input (key text : List Byte) : Prop :=
  (64 < key.length → SHA2.ValidSHA256Input key) ∧ 64 + text.length < 2 ^ 61

/-- The SHA-512 HMAC source domain: a long key must be hashable, and the inner hash input must be
inside SHA-512's byte-aligned input domain. -/
@[expose] def ValidHMACSHA512Input (key text : List Byte) : Prop :=
  (128 < key.length → SHA2.ValidSHA512Input key) ∧ 128 + text.length < 2 ^ 125

instance (key text : List Byte) : Decidable (ValidHMACSHA256Input key text) := by
  unfold ValidHMACSHA256Input
  infer_instance

instance (key text : List Byte) : Decidable (ValidHMACSHA512Input key text) := by
  unfold ValidHMACSHA512Input
  infer_instance

/-- Turn HMAC key material into an exact block, padding absent trailing bytes with zero. -/
private def keyBlock (blockBytes : ℕ) (keyMaterial : List Byte) : FixedBytes blockBytes :=
  fun i => keyMaterial.getD i.val 0

/-- The FIPS 198-1 SHA-256 key preprocessing branches, producing a 64-byte `K0`. -/
private def sha256KeyBlock (key : List Byte) : FixedBytes 64 :=
  if 64 < key.length then
    keyBlock 64 (SHA2.sha256 key).toList
  else
    keyBlock 64 key

/-- The FIPS 198-1 SHA-512 key preprocessing branches, producing a 128-byte `K0`. -/
private def sha512KeyBlock (key : List Byte) : FixedBytes 128 :=
  if 128 < key.length then
    keyBlock 128 (SHA2.sha512 key).toList
  else
    keyBlock 128 key

/-- XOR an exact key block with one repeated HMAC pad byte. -/
private def xorPad {blockBytes : ℕ} (key : FixedBytes blockBytes) (pad : Byte) :
    FixedBytes blockBytes := fun i =>
  ⟨(key i).val ^^^ pad.val, Nat.xor_lt_two_pow (key i).isLt pad.isLt⟩

/-- The exact HMAC hash input `(K0 xor pad) || text`. -/
private def input {blockBytes : ℕ} (key : FixedBytes blockBytes) (pad : Byte)
    (text : List Byte) : List Byte :=
  (xorPad key pad).toList ++ text

/-- HMAC hash packaging has one full key block followed by the supplied text. -/
@[simp] private theorem length_input {blockBytes : ℕ} (key : FixedBytes blockBytes) (pad : Byte)
    (text : List Byte) : (input key pad text).length = blockBytes + text.length := by
  simp [input]

/-- FIPS 198-1 HMAC instantiated with SHA-256, returning all 32 digest bytes. -/
def hmacSHA256 (key text : List Byte) : FixedBytes 32 :=
  let keyBlock := sha256KeyBlock key
  let innerDigest := SHA2.sha256 (input keyBlock 0x36 text)
  SHA2.sha256 (input keyBlock 0x5c innerDigest.toList)

/-- FIPS 198-1 HMAC instantiated with SHA-512, returning all 64 digest bytes. -/
def hmacSHA512 (key text : List Byte) : FixedBytes 64 :=
  let keyBlock := sha512KeyBlock key
  let innerDigest := SHA2.sha512 (input keyBlock 0x36 text)
  SHA2.sha512 (input keyBlock 0x5c innerDigest.toList)

private theorem keyBlock_append_zeros (blockBytes padding : ℕ) (key : List Byte) :
    keyBlock blockBytes (key ++ List.replicate padding 0) = keyBlock blockBytes key := by
  funext i
  unfold keyBlock
  by_cases hi : i.val < key.length
  · exact List.getD_append key (List.replicate padding 0) 0 i.val hi
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq,
      List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]

private theorem sha256KeyBlock_append_zeros (key : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 64) :
    sha256KeyBlock (key ++ List.replicate padding 0) = sha256KeyBlock key := by
  rw [sha256KeyBlock, sha256KeyBlock]
  simp only [List.length_append, List.length_replicate]
  split
  · omega
  split
  · omega
  exact keyBlock_append_zeros 64 padding key

private theorem sha512KeyBlock_append_zeros (key : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 128) :
    sha512KeyBlock (key ++ List.replicate padding 0) = sha512KeyBlock key := by
  rw [sha512KeyBlock, sha512KeyBlock]
  simp only [List.length_append, List.length_replicate]
  split
  · omega
  split
  · omega
  exact keyBlock_append_zeros 128 padding key

/-- Appending zero bytes to a SHA-256 HMAC key does not change the result while the extended key
still fits in one 64-byte SHA-256 block. -/
theorem hmacSHA256_append_zeros (key text : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 64) :
    hmacSHA256 (key ++ List.replicate padding 0) text = hmacSHA256 key text := by
  rw [hmacSHA256, hmacSHA256, sha256KeyBlock_append_zeros key padding h]

/-- Appending zero bytes to a SHA-512 HMAC key does not change the result while the extended key
still fits in one 128-byte SHA-512 block. -/
theorem hmacSHA512_append_zeros (key text : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 128) :
    hmacSHA512 (key ++ List.replicate padding 0) text = hmacSHA512 key text := by
  rw [hmacSHA512, hmacSHA512, sha512KeyBlock_append_zeros key padding h]

end Cslib.Crypto.HMAC
