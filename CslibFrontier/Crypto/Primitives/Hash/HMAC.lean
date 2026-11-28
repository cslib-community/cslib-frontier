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

This module transcribes the keyed-hash message authentication code of FIPS 198-1 (July 2008)
[NISTFIPS1981], instantiated with the SHA-256 and SHA-512 functions of
`CslibFrontier.Crypto.Primitives.Hash.SHA2`. With `B` the block size of the hash in bytes (64 for
SHA-256 and 128 for SHA-512), the source reads as follows.

* Section 2.3: `ipad` is the byte `0x36` repeated `B` times, and `opad` is the byte `0x5c`
  repeated `B` times.
* Section 3 and Table 1, steps 1--3: the `B`-byte key `K0` is the key itself when it has `B`
  bytes, the key followed by zero bytes when it is shorter, and the digest of the key followed
  by zero bytes when it is longer.
* Section 4 and Table 1, steps 4--9: the result is
  `H((K0 xor opad) || H((K0 xor ipad) || text))`.

`hmacSHA256` and `hmacSHA512` return the full 32-byte or 64-byte digest. Section 5 of the source,
on truncation, is not transcribed: an application that prescribes truncation applies it to the
result.

The functions are total, as the SHA-2 functions are. The source's computation is defined when its
hash inputs are inside the SHA-2 message-length domain, fewer than `2^61` bytes for SHA-256 and
fewer than `2^125` bytes for SHA-512. That is two conditions: a key longer than `B` bytes, which
is hashed, is inside the domain, and so is the inner hash input of `B + text.length` bytes. The
second is the bound of Section 2.3 on the text, fewer than `2^B - 8B` bits. On such inputs the
functions are the source's HMAC. On all others they are the same expression over the total SHA-2
functions, which write the bit length of their input modulo `2^64` or `2^128` into the padding.

The first property beyond the transcription is the zero-padding rule of Table 1, step 3, proved
as a law of the final functions: appending zero bytes to a key does not change the result while
the extended key still fits in one block, including when it fills the block exactly. Nothing else
is proved about these functions. In particular there is no proof of agreement with an independent
model of FIPS 198-1, and no statement that HMAC is a pseudorandom function or a secure message
authentication code. The definitions are executable specifications, not constant-time or
machine-costed implementations.

The test module `CslibFrontierTests.Crypto.HMACMGF1` evaluates both functions on test cases 1 and
6 of RFC 4231, Sections 4.2 and 4.7 [RFC4231] (a 20-byte key and a 131-byte key), and on a key of
exactly one block for each hash.

## Main definitions

* `Cslib.Crypto.HMAC.hmacSHA256`, `hmacSHA512`: full-length SHA-2 HMAC functions.

## Main results

* `Cslib.Crypto.HMAC.hmacSHA256_append_zeros`, `hmacSHA512_append_zeros`: adding zero bytes
  to a key that remains at most one hash block does not change HMAC.

## References

* [National Institute of Standards and Technology, *The Keyed-Hash Message Authentication Code
  (HMAC)*, FIPS PUB 198-1, July 2008][NISTFIPS1981], Sections 2.3, 3 and 4 and Table 1.
* [M. Nystrom, *Identifiers and Test Vectors for HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384, and
  HMAC-SHA-512*, RFC 4231, December 2005][RFC4231], Sections 4.2 and 4.7.
-/

public section

namespace Cslib.Crypto.HMAC

open Cslib.Crypto

/-- The bytes that FIPS 198-1 pads with zeros to form `K0`: the key itself, or its digest when the
key is longer than one block. -/
private def keyMaterial (hash : List Byte → List Byte) (blockBytes : ℕ) (key : List Byte) :
    List Byte :=
  if blockBytes < key.length then hash key else key

/-- The block-sized key `K0`: the key material followed by zero bytes. -/
private def keyBlock (blockBytes : ℕ) (keyMaterial : List Byte) : FixedBytes blockBytes :=
  fun i => keyMaterial.getD i.val 0

/-- XOR an exact key block with one repeated HMAC pad byte. -/
private def xorPad {blockBytes : ℕ} (key : FixedBytes blockBytes) (pad : Byte) :
    FixedBytes blockBytes := fun i =>
  ⟨(key i).val ^^^ pad.val, Nat.xor_lt_two_pow (key i).isLt pad.isLt⟩

/-- The exact HMAC hash input `(K0 xor pad) || text`. -/
private def input {blockBytes : ℕ} (key : FixedBytes blockBytes) (pad : Byte)
    (text : List Byte) : List Byte :=
  (xorPad key pad).toList ++ text

/-- HMAC of FIPS 198-1 with SHA-256, returning all 32 digest bytes. This is the source's function
when both hash inputs that depend on the arguments are inside the SHA-256 domain
`SHA2.ValidSHA256Input`: a key longer than 64 bytes, which is hashed, has `key.length < 2^61`, and
the inner hash input has `64 + text.length < 2^61`. On all other inputs it is the same expression
over the total `SHA2.sha256`, which writes the bit length of its input modulo `2^64` into the
padding. The key digest and the inner digest are the byte lists `SHA2.sha256Bytes`, which are the
bytes of `SHA2.sha256` (`SHA2.sha256Bytes_eq_toList`). -/
def hmacSHA256 (key text : List Byte) : FixedBytes 32 :=
  let k0 := keyBlock 64 (keyMaterial SHA2.sha256Bytes 64 key)
  SHA2.sha256 (input k0 0x5c (SHA2.sha256Bytes (input k0 0x36 text)))

/-- HMAC of FIPS 198-1 with SHA-512, returning all 64 digest bytes. This is the source's function
when both hash inputs that depend on the arguments are inside the SHA-512 domain
`SHA2.ValidSHA512Input`: a key longer than 128 bytes, which is hashed, has `key.length < 2^125`,
and the inner hash input has `128 + text.length < 2^125`. On all other inputs it is the same
expression over the total `SHA2.sha512`, which writes the bit length of its input modulo `2^128`
into the padding. The key digest and the inner digest are the byte lists `SHA2.sha512Bytes`, which
are the bytes of `SHA2.sha512` (`SHA2.sha512Bytes_eq_toList`). -/
def hmacSHA512 (key text : List Byte) : FixedBytes 64 :=
  let k0 := keyBlock 128 (keyMaterial SHA2.sha512Bytes 128 key)
  SHA2.sha512 (input k0 0x5c (SHA2.sha512Bytes (input k0 0x36 text)))

/-- Zero bytes appended to a key that still fits in one block do not change `K0`. -/
private theorem keyBlock_keyMaterial_append_zeros (hash : List Byte → List Byte)
    {blockBytes : ℕ} (key : List Byte) (padding : ℕ) (h : key.length + padding ≤ blockBytes) :
    keyBlock blockBytes (keyMaterial hash blockBytes (key ++ List.replicate padding 0)) =
      keyBlock blockBytes (keyMaterial hash blockBytes key) := by
  have hkey : ¬ blockBytes < key.length := by omega
  have hextended : ¬ blockBytes < (key ++ List.replicate padding 0).length := by simp; omega
  simp only [keyMaterial, hkey, hextended, ↓reduceIte]
  funext i
  by_cases hi : i.val < key.length
  · exact List.getD_append key (List.replicate padding 0) 0 i.val hi
  · rw [keyBlock, keyBlock, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq,
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]

/-- Appending zero bytes to a SHA-256 HMAC key does not change the result while the extended key
still fits in one 64-byte SHA-256 block. -/
theorem hmacSHA256_append_zeros (key text : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 64) :
    hmacSHA256 (key ++ List.replicate padding 0) text = hmacSHA256 key text := by
  rw [hmacSHA256, hmacSHA256, keyBlock_keyMaterial_append_zeros SHA2.sha256Bytes key padding h]

/-- Appending zero bytes to a SHA-512 HMAC key does not change the result while the extended key
still fits in one 128-byte SHA-512 block. -/
theorem hmacSHA512_append_zeros (key text : List Byte) (padding : ℕ)
    (h : key.length + padding ≤ 128) :
    hmacSHA512 (key ++ List.replicate padding 0) text = hmacSHA512 key text := by
  rw [hmacSHA512, hmacSHA512, keyBlock_keyMaterial_append_zeros SHA2.sha512Bytes key padding h]

end Cslib.Crypto.HMAC
