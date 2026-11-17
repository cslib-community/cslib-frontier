/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.SHA2
public import CslibFrontier.Foundations.Data.Nat.CeilDiv
import CslibFrontier.Foundations.Data.List.OfFnGetD

/-!
# MGF1 with SHA-256 and SHA-512

This module implements RFC 8017's MGF1 with the concrete SHA-256 and SHA-512 functions. Each
counter is encoded as four big-endian bytes, hashes are concatenated for consecutive counters
starting at zero, and the result is the requested leading number of bytes.

The validity predicates expose RFC 8017's inclusive `maskLen <= 2^32 * hLen` bound. SHA-256 and
SHA-512 are total executable functions, so the seed is unrestricted. At the inclusive boundary
there are exactly `2^32` digest blocks, and the final counter is still accepted by four-byte
`I2OSP`.

This is an executable specification. It does not claim pseudorandomness, constant-time execution,
efficient evaluation at enormous output lengths, FIPS validation, or machine/resource bounds.
The materialized list views evaluate each counter digest once. The existing function-valued
`FixedBytes` views do not promise runtime caching between index applications.

## Main definitions

* `Cslib.Crypto.MGF1.ValidMGF1SHA256Input`, `ValidMGF1SHA512Input`: source domains.
* `Cslib.Crypto.MGF1.mgf1SHA256`, `mgf1SHA512`: exact-length leading-byte masks.
* `Cslib.Crypto.MGF1.mgf1SHA256Bytes`, `mgf1SHA512Bytes`: materialized list views that evaluate
  each required counter digest once.

## Main results

* `Cslib.Crypto.MGF1.mgf1SHA256_prefix`, `mgf1SHA512_prefix`: a shorter valid mask is the
  corresponding prefix of a longer one.

## References

* [Moriarty et al., *PKCS #1: RSA Cryptography Specifications Version 2.2*, Section 4.1 and
  Appendix B.2.1][RFC8017]
-/

public section

namespace Cslib.Crypto.MGF1

open Cslib.Crypto

/-- The SHA-256 MGF1 domain from RFC 8017: its inclusive output-length bound. -/
@[expose] def ValidMGF1SHA256Input (maskLen : ℕ) : Prop := maskLen ≤ 2 ^ 32 * 32

/-- The SHA-512 MGF1 domain from RFC 8017: its inclusive output-length bound. -/
@[expose] def ValidMGF1SHA512Input (maskLen : ℕ) : Prop := maskLen ≤ 2 ^ 32 * 64

instance (maskLen : ℕ) : Decidable (ValidMGF1SHA256Input maskLen) := by
  unfold ValidMGF1SHA256Input
  infer_instance

instance (maskLen : ℕ) : Decidable (ValidMGF1SHA512Input maskLen) := by
  unfold ValidMGF1SHA512Input
  infer_instance

/-- SHA-256 of `seed || I2OSP(counter, 4)`. Accepted MGF1 lengths ensure every generated
counter is below `2^32`; the executable hash remains total outside that source domain. -/
private def sha256CounterDigest (seed : List Byte) (counter : ℕ) : List Byte :=
  SHA2.sha256Bytes (seed ++ (natToFixedBytesBE 4 counter).toList)

/-- SHA-512 of `seed || I2OSP(counter, 4)`. Accepted MGF1 lengths ensure every generated
counter is below `2^32`; the executable hash remains total outside that source domain. -/
private def sha512CounterDigest (seed : List Byte) (counter : ℕ) : List Byte :=
  SHA2.sha512Bytes (seed ++ (natToFixedBytesBE 4 counter).toList)

/-- Materialize each SHA-256 counter digest once, in increasing counter order. -/
private def sha256CounterBytes (seed : List Byte) (blockCount : ℕ) : List Byte :=
  (List.range blockCount).flatMap fun counter => sha256CounterDigest seed counter

/-- Materialize each SHA-512 counter digest once, in increasing counter order. -/
private def sha512CounterBytes (seed : List Byte) (blockCount : ℕ) : List Byte :=
  (List.range blockCount).flatMap fun counter => sha512CounterDigest seed counter

@[simp] private theorem length_sha256CounterBytes (seed : List Byte) (blockCount : ℕ) :
    (sha256CounterBytes seed blockCount).length = blockCount * 32 := by
  simp [sha256CounterBytes, sha256CounterDigest, SHA2.sha256Bytes_eq_toList]

@[simp] private theorem length_sha512CounterBytes (seed : List Byte) (blockCount : ℕ) :
    (sha512CounterBytes seed blockCount).length = blockCount * 64 := by
  simp [sha512CounterBytes, sha512CounterDigest, SHA2.sha512Bytes_eq_toList]

private theorem sha256CounterBytes_eq_append (seed : List Byte) {smaller larger : ℕ}
    (h : smaller ≤ larger) :
    sha256CounterBytes seed larger = sha256CounterBytes seed smaller ++
      (List.range (larger - smaller)).flatMap fun counter =>
        sha256CounterDigest seed (smaller + counter) := by
  rw [show larger = smaller + (larger - smaller) by omega]
  simp only [sha256CounterBytes, List.range_add, List.flatMap_append, List.flatMap_map,
    Nat.add_sub_cancel_left]

private theorem sha512CounterBytes_eq_append (seed : List Byte) {smaller larger : ℕ}
    (h : smaller ≤ larger) :
    sha512CounterBytes seed larger = sha512CounterBytes seed smaller ++
      (List.range (larger - smaller)).flatMap fun counter =>
        sha512CounterDigest seed (smaller + counter) := by
  rw [show larger = smaller + (larger - smaller) by omega]
  simp only [sha512CounterBytes, List.range_add, List.flatMap_append, List.flatMap_map,
    Nat.add_sub_cancel_left]

private def sha256Output (seed : List Byte) (maskLen : ℕ) : List Byte :=
  (sha256CounterBytes seed (maskLen ⌈/⌉ 32)).take maskLen

private def sha512Output (seed : List Byte) (maskLen : ℕ) : List Byte :=
  (sha512CounterBytes seed (maskLen ⌈/⌉ 64)).take maskLen

@[simp] private theorem length_sha256Output (seed : List Byte) (maskLen : ℕ) :
    (sha256Output seed maskLen).length = maskLen := by
  rw [sha256Output, List.length_take, length_sha256CounterBytes,
    Nat.min_eq_left (Nat.le_ceilDiv_mul (by decide))]

@[simp] private theorem length_sha512Output (seed : List Byte) (maskLen : ℕ) :
    (sha512Output seed maskLen).length = maskLen := by
  rw [sha512Output, List.length_take, length_sha512CounterBytes,
    Nat.min_eq_left (Nat.le_ceilDiv_mul (by decide))]

private theorem sha256Output_prefix (seed : List Byte) {shorter longer : ℕ}
    (h : shorter ≤ longer) :
    (sha256Output seed longer).take shorter = sha256Output seed shorter := by
  have hblocks : shorter ⌈/⌉ 32 ≤ longer ⌈/⌉ 32 :=
    (Nat.ceilDiv_le_iff (by decide)).2
      (h.trans (Nat.le_ceilDiv_mul (a := longer) (by decide)))
  rw [sha256Output, sha256Output, List.take_take, Nat.min_eq_left h,
    sha256CounterBytes_eq_append seed hblocks,
    List.take_append_of_le_length (by
      rw [length_sha256CounterBytes]
      exact Nat.le_ceilDiv_mul (a := shorter) (by decide))]

private theorem sha512Output_prefix (seed : List Byte) {shorter longer : ℕ}
    (h : shorter ≤ longer) :
    (sha512Output seed longer).take shorter = sha512Output seed shorter := by
  have hblocks : shorter ⌈/⌉ 64 ≤ longer ⌈/⌉ 64 :=
    (Nat.ceilDiv_le_iff (by decide)).2
      (h.trans (Nat.le_ceilDiv_mul (a := longer) (by decide)))
  rw [sha512Output, sha512Output, List.take_take, Nat.min_eq_left h,
    sha512CounterBytes_eq_append seed hblocks,
    List.take_append_of_le_length (by
      rw [length_sha512CounterBytes]
      exact Nat.le_ceilDiv_mul (a := shorter) (by decide))]

/-- Materialize the requested SHA-256 MGF1 bytes, evaluating each counter digest once. -/
def mgf1SHA256Bytes (seed : List Byte) (maskLen : ℕ)
    (_hinput : ValidMGF1SHA256Input maskLen) : List Byte :=
  sha256Output seed maskLen

/-- Materialize the requested SHA-512 MGF1 bytes, evaluating each counter digest once. -/
def mgf1SHA512Bytes (seed : List Byte) (maskLen : ℕ)
    (_hinput : ValidMGF1SHA512Input maskLen) : List Byte :=
  sha512Output seed maskLen

/-- RFC 8017 MGF1 instantiated with SHA-256, returning the existing typed view of the
`mgf1SHA256Bytes` output. -/
def mgf1SHA256 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) : FixedBytes maskLen :=
  let output := mgf1SHA256Bytes seed maskLen hinput
  fun i => output.getD i.val 0

/-- RFC 8017 MGF1 instantiated with SHA-512, returning the existing typed view of the
`mgf1SHA512Bytes` output. -/
def mgf1SHA512 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) : FixedBytes maskLen :=
  let output := mgf1SHA512Bytes seed maskLen hinput
  fun i => output.getD i.val 0

/-- Enumerating the typed SHA-256 MGF1 output gives the materialized bytes exactly. -/
theorem ofFn_mgf1SHA256 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) :
    List.ofFn (mgf1SHA256 seed maskLen hinput) = mgf1SHA256Bytes seed maskLen hinput := by
  unfold mgf1SHA256 mgf1SHA256Bytes
  exact List.ofFn_getD_eq_of_length 0 (length_sha256Output seed maskLen)

/-- Enumerating the typed SHA-512 MGF1 output gives the materialized bytes exactly. -/
theorem ofFn_mgf1SHA512 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) :
    List.ofFn (mgf1SHA512 seed maskLen hinput) = mgf1SHA512Bytes seed maskLen hinput := by
  unfold mgf1SHA512 mgf1SHA512Bytes
  exact List.ofFn_getD_eq_of_length 0 (length_sha512Output seed maskLen)

/-- A shorter valid SHA-256 MGF1 mask is the corresponding prefix of any longer valid mask. -/
theorem mgf1SHA256_prefix (seed : List Byte) {shorter longer : ℕ}
    (hshorter : ValidMGF1SHA256Input shorter) (hlonger : ValidMGF1SHA256Input longer)
    (h : shorter ≤ longer) :
    Fin.take shorter h (mgf1SHA256 seed longer hlonger) =
      mgf1SHA256 seed shorter hshorter := by
  apply List.ofFn_injective
  rw [Fin.ofFn_take_eq_take_ofFn, ofFn_mgf1SHA256, ofFn_mgf1SHA256,
    mgf1SHA256Bytes, mgf1SHA256Bytes,
    sha256Output_prefix seed h]

/-- A shorter valid SHA-512 MGF1 mask is the corresponding prefix of any longer valid mask. -/
theorem mgf1SHA512_prefix (seed : List Byte) {shorter longer : ℕ}
    (hshorter : ValidMGF1SHA512Input shorter) (hlonger : ValidMGF1SHA512Input longer)
    (h : shorter ≤ longer) :
    Fin.take shorter h (mgf1SHA512 seed longer hlonger) =
      mgf1SHA512 seed shorter hshorter := by
  apply List.ofFn_injective
  rw [Fin.ofFn_take_eq_take_ofFn, ofFn_mgf1SHA512, ofFn_mgf1SHA512,
    mgf1SHA512Bytes, mgf1SHA512Bytes,
    sha512Output_prefix seed h]

end Cslib.Crypto.MGF1
