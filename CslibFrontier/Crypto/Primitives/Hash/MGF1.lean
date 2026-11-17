/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.SHA2
public import CslibFrontier.Foundations.Data.Nat.CeilDiv
import CslibFrontier.Foundations.Data.BitString.Block

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

## Main definitions

* `Cslib.Crypto.MGF1.ValidMGF1SHA256Input`, `ValidMGF1SHA512Input`: source domains.
* `Cslib.Crypto.MGF1.sha256CounterDigest`, `sha512CounterDigest`: one typed counter hash.
* `Cslib.Crypto.MGF1.sha256Blocks`, `sha512Blocks`: digests in increasing counter order.
* `Cslib.Crypto.MGF1.sha256Stream`, `sha512Stream`: typed complete counter-hash streams.
* `Cslib.Crypto.MGF1.mgf1SHA256`, `mgf1SHA512`: exact-length leading-byte masks.

## Main results

* `Cslib.Crypto.MGF1.sha256Counter_lt_two_pow_32`, `sha512Counter_lt_two_pow_32`: every
  generated counter fits the four-byte encoding.
* `Cslib.Crypto.MGF1.ofFn_sha256Stream`, `ofFn_sha512Stream`: the stream concatenates
  counter digests in order.

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

/-- SHA-256 of `seed || I2OSP(counter, 4)` for an RFC 8017 four-byte counter. -/
def sha256CounterDigest (seed : List Byte) (counter : Fin (2 ^ 32)) : FixedBytes 32 :=
  SHA2.sha256 (seed ++ (natToFixedBytesBE 4 counter.val).toList)

/-- SHA-512 of `seed || I2OSP(counter, 4)` for an RFC 8017 four-byte counter. -/
def sha512CounterDigest (seed : List Byte) (counter : Fin (2 ^ 32)) : FixedBytes 64 :=
  SHA2.sha512 (seed ++ (natToFixedBytesBE 4 counter.val).toList)

/-- Every SHA-256 MGF1 counter generated at an accepted output length fits four bytes. -/
theorem sha256Counter_lt_two_pow_32 (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) (counter : Fin (maskLen ⌈/⌉ 32)) :
    counter.val < 2 ^ 32 :=
  counter.isLt.trans_le ((Nat.ceilDiv_le_iff (by decide)).2 hinput)

/-- Every SHA-512 MGF1 counter generated at an accepted output length fits four bytes. -/
theorem sha512Counter_lt_two_pow_32 (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) (counter : Fin (maskLen ⌈/⌉ 64)) :
    counter.val < 2 ^ 32 :=
  counter.isLt.trans_le ((Nat.ceilDiv_le_iff (by decide)).2 hinput)

/-- SHA-256 MGF1 digest blocks indexed by their consecutive counters. -/
def sha256Blocks (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) :
    Fin (maskLen ⌈/⌉ 32) → FixedBytes 32 := fun counter =>
  sha256CounterDigest seed
    ⟨counter.val, sha256Counter_lt_two_pow_32 maskLen hinput counter⟩

/-- SHA-512 MGF1 digest blocks indexed by their consecutive counters. -/
def sha512Blocks (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) :
    Fin (maskLen ⌈/⌉ 64) → FixedBytes 64 := fun counter =>
  sha512CounterDigest seed
    ⟨counter.val, sha512Counter_lt_two_pow_32 maskLen hinput counter⟩

/-- The typed concatenation of the required SHA-256 counter digests before MGF1 truncation. -/
def sha256Stream (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) :
    FixedBytes ((maskLen ⌈/⌉ 32) * 32) :=
  Cslib.BitString.blocksEquiv.symm (sha256Blocks seed maskLen hinput)

/-- The typed concatenation of the required SHA-512 counter digests before MGF1 truncation. -/
def sha512Stream (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) :
    FixedBytes ((maskLen ⌈/⌉ 64) * 64) :=
  Cslib.BitString.blocksEquiv.symm (sha512Blocks seed maskLen hinput)

/-- The SHA-256 stream concatenates the counter digests in increasing counter order. -/
theorem ofFn_sha256Stream (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) :
    List.ofFn (sha256Stream seed maskLen hinput) =
      (List.ofFn fun counter => List.ofFn (sha256Blocks seed maskLen hinput counter)).flatten := by
  simpa only [sha256Stream] using
    (Cslib.BitString.ofFn_blocksEquiv_symm (sha256Blocks seed maskLen hinput))

/-- The SHA-512 stream concatenates the counter digests in increasing counter order. -/
theorem ofFn_sha512Stream (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) :
    List.ofFn (sha512Stream seed maskLen hinput) =
      (List.ofFn fun counter => List.ofFn (sha512Blocks seed maskLen hinput counter)).flatten := by
  simpa only [sha512Stream] using
    (Cslib.BitString.ofFn_blocksEquiv_symm (sha512Blocks seed maskLen hinput))

/-- RFC 8017 MGF1 instantiated with SHA-256, returning exactly `maskLen` leading bytes. -/
def mgf1SHA256 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA256Input maskLen) : FixedBytes maskLen :=
  Fin.take maskLen (Nat.le_ceilDiv_mul (by decide)) (sha256Stream seed maskLen hinput)

/-- RFC 8017 MGF1 instantiated with SHA-512, returning exactly `maskLen` leading bytes. -/
def mgf1SHA512 (seed : List Byte) (maskLen : ℕ)
    (hinput : ValidMGF1SHA512Input maskLen) : FixedBytes maskLen :=
  Fin.take maskLen (Nat.le_ceilDiv_mul (by decide)) (sha512Stream seed maskLen hinput)

end Cslib.Crypto.MGF1
