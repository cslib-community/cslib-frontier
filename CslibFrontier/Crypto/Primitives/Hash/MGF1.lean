/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.SHA2
import CslibFrontier.Foundations.Data.Nat.CeilDiv
import Mathlib.Data.List.GetD

/-!
# MGF1 with SHA-256 and SHA-512

This module transcribes the mask generation function MGF1 of RFC 8017 (PKCS #1 v2.2, November
2016), Appendix B.2.1 [RFC8017], instantiated with the SHA-256 and SHA-512 functions of
`CslibFrontier.Crypto.Primitives.Hash.SHA2`. With `hLen` the digest length in bytes (32 for
SHA-256 and 64 for SHA-512), the source reads as follows.

* Step 1: a requested length `maskLen > 2^32 * hLen` is rejected as `mask too long`.
* Step 3: for `counter` from `0` to `⌈maskLen / hLen⌉ - 1`, the digest of
  `mgfSeed || I2OSP(counter, 4)` is appended to an initially empty string `T`. Section 4.1 defines
  `I2OSP(counter, 4)` as the four-byte big-endian encoding of `counter`.
* Step 4: the result is the leading `maskLen` bytes of `T`.

`mgf1SHA256` and `mgf1SHA512` are total functions of the seed and the requested length, and the
length is recorded in the type of the result. For `maskLen ≤ 2^32 * hLen`, the bound of step 1,
every counter is below `2^32`, so `natToFixedBytesBE 4` is `I2OSP(·, 4)` and the functions are the
source's MGF1. Beyond the bound, where the source has no output, they reduce the counter modulo
`2^32`.

The first property beyond the transcription is prefix consistency: a mask is the corresponding
prefix of every longer mask from the same seed. Nothing else is proved about these functions. In
particular there is no proof of agreement with an independent model of RFC 8017 and no
pseudorandomness statement. The definitions are executable specifications, not constant-time or
machine-costed implementations, and evaluating them at a large length is not efficient.

RFC 8017 gives no test vectors for MGF1. The test module `CslibFrontierTests.Crypto.HMACMGF1`
evaluates both functions at the lengths `0`, `hLen - 1`, `hLen` and `hLen + 1` against values
computed outside Lean from the steps above.

## Main definitions

* `Cslib.Crypto.MGF1.mgf1SHA256`, `mgf1SHA512`: masks of the requested length.

## Main results

* `Cslib.Crypto.MGF1.mgf1SHA256_prefix`, `mgf1SHA512_prefix`: a shorter mask is the corresponding
  prefix of a longer one.

## References

* [K. Moriarty, B. Kaliski, J. Jonsson and A. Rusch, *PKCS #1: RSA Cryptography Specifications
  Version 2.2*, RFC 8017, November 2016][RFC8017], Section 4.1 and Appendix B.2.1.
-/

public section

namespace Cslib.Crypto.MGF1

open Cslib.Crypto

/-- The string `T` of RFC 8017 after `blockCount` counters: the digests of
`seed || I2OSP(counter, 4)` in increasing counter order. -/
private def counterBytes (hash : List Byte → List Byte) (seed : List Byte) (blockCount : ℕ) :
    List Byte :=
  (List.range blockCount).flatMap fun counter =>
    hash (seed ++ (natToFixedBytesBE 4 counter).toList)

/-- The leading `maskLen` bytes of the string `T` built from `⌈maskLen / hLen⌉` counters. -/
private def mask (hash : List Byte → List Byte) (hLen : ℕ) (seed : List Byte) (maskLen : ℕ) :
    FixedBytes maskLen :=
  let stream := counterBytes hash seed (maskLen ⌈/⌉ hLen)
  fun i => stream.getD i.val 0

private theorem length_counterBytes {hash : List Byte → List Byte} {hLen : ℕ}
    (hhash : ∀ input, (hash input).length = hLen) (seed : List Byte) (blockCount : ℕ) :
    (counterBytes hash seed blockCount).length = blockCount * hLen := by
  simp [counterBytes, List.length_flatMap, hhash]

/-- More counters extend the string `T` on the right. -/
private theorem counterBytes_eq_append (hash : List Byte → List Byte) (seed : List Byte)
    {smaller larger : ℕ} (h : smaller ≤ larger) :
    ∃ rest, counterBytes hash seed larger = counterBytes hash seed smaller ++ rest := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold counterBytes
  rw [List.range_add, List.flatMap_append]
  exact ⟨_, rfl⟩

/-- A shorter mask is the corresponding prefix of a longer one, for any hash with digests of
length `hLen`. -/
private theorem take_mask {hash : List Byte → List Byte} {hLen : ℕ} (hpos : 0 < hLen)
    (hhash : ∀ input, (hash input).length = hLen) (seed : List Byte) {shorter longer : ℕ}
    (h : shorter ≤ longer) :
    Fin.take shorter h (mask hash hLen seed longer) = mask hash hLen seed shorter := by
  have hblocks : shorter ⌈/⌉ hLen ≤ longer ⌈/⌉ hLen :=
    (Nat.ceilDiv_le_iff hpos).2 (h.trans (Nat.le_ceilDiv_mul hpos))
  obtain ⟨rest, hrest⟩ := counterBytes_eq_append hash seed hblocks
  funext i
  have hi : i.val < (counterBytes hash seed (shorter ⌈/⌉ hLen)).length := by
    rw [length_counterBytes hhash]
    exact i.isLt.trans_le (Nat.le_ceilDiv_mul hpos)
  simp only [Fin.take_apply, mask, Fin.val_castLE, hrest]
  exact List.getD_append _ _ _ _ hi

/-- MGF1 of RFC 8017, Appendix B.2.1, with SHA-256: the leading `maskLen` bytes of the
concatenated SHA-256 digests of `seed || C` for the counters `0, 1, …`, where `C` is the counter
as four big-endian bytes (the source's `I2OSP(counter, 4)`). For `maskLen ≤ 2^32 * 32` this is the
source's function. For larger `maskLen`, where the source outputs `mask too long`, the counter is
reduced modulo `2^32`. -/
def mgf1SHA256 (seed : List Byte) (maskLen : ℕ) : FixedBytes maskLen :=
  mask SHA2.sha256Bytes 32 seed maskLen

/-- MGF1 of RFC 8017, Appendix B.2.1, with SHA-512: the leading `maskLen` bytes of the
concatenated SHA-512 digests of `seed || C` for the counters `0, 1, …`, where `C` is the counter
as four big-endian bytes (the source's `I2OSP(counter, 4)`). For `maskLen ≤ 2^32 * 64` this is the
source's function. For larger `maskLen`, where the source outputs `mask too long`, the counter is
reduced modulo `2^32`. -/
def mgf1SHA512 (seed : List Byte) (maskLen : ℕ) : FixedBytes maskLen :=
  mask SHA2.sha512Bytes 64 seed maskLen

/-- A shorter SHA-256 MGF1 mask is the corresponding prefix of any longer mask from the same
seed. -/
theorem mgf1SHA256_prefix (seed : List Byte) {shorter longer : ℕ} (h : shorter ≤ longer) :
    Fin.take shorter h (mgf1SHA256 seed longer) = mgf1SHA256 seed shorter :=
  take_mask (by decide)
    (fun input => by rw [SHA2.sha256Bytes_eq_toList, FixedBytes.length_toList]) seed h

/-- A shorter SHA-512 MGF1 mask is the corresponding prefix of any longer mask from the same
seed. -/
theorem mgf1SHA512_prefix (seed : List Byte) {shorter longer : ℕ} (h : shorter ≤ longer) :
    Fin.take shorter h (mgf1SHA512 seed longer) = mgf1SHA512 seed shorter :=
  take_mask (by decide)
    (fun input => by rw [SHA2.sha512Bytes_eq_toList, FixedBytes.length_toList]) seed h

end Cslib.Crypto.MGF1
