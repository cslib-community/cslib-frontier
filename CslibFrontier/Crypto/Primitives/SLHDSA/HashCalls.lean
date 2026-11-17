/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString.Blocks
public import CslibFrontier.Crypto.Primitives.Hash.Keccak
public import CslibFrontier.Crypto.Primitives.Hash.SHA2
public import CslibFrontier.Crypto.Primitives.SLHDSA.Address
public import CslibFrontier.Crypto.Primitives.SLHDSA.Parameters
public import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Tactic

/-!
# Addressed SLH-DSA hash calls

This module implements the four FIPS 205 hash calls whose inputs are separated by an address:
`PRF`, `F`, `H`, and `T_l`. The SHAKE parameter sets use the canonical 32-byte address and
SHAKE256. The SHA2 parameter sets use the compressed 22-byte address and the precise SHA-256 or
SHA-512 branch prescribed for each call and security-element length.

The low-level calls accept every typed `Address`, as the signatures in Section 4.1 do. SHA2
applies the standard's total compressed-address projection; protocol call sites are responsible for
setting the address type and keeping the retained layer and tree fields in their standardized
ranges.

Inputs encode the source arities in their types: `F` and `PRF` consume one `n`-byte payload, `H`
consumes two consecutive `n`-byte blocks, and `T_l` consumes exactly `l * n` bytes. All outputs are
exactly `n` bytes. The hash calls use the total SHA2 functions, while `ValidTInput` separately
records the standard's SHA-2 input domain; `validTInput_of_blocks_le_67` proves that fact for every
standardized WOTS+ or FORS call.

This is executable hash plumbing, not a constant-time or machine-costed implementation, a NIST
validation, a security proof, or an asymptotic parameter family. It does not define `H_msg`,
`PRF_msg`, WOTS+, XMSS, FORS, the hypertree, signing, or verification.

## Main definitions

* `Cslib.Crypto.SLHDSA.HashFamily`: the SHAKE and SHA2 instantiation families.
* `Cslib.Crypto.SLHDSA.NBytes`, `TwoNBytes`, `LBlocksBytes`: typed call inputs.
* `Cslib.Crypto.FixedBytes.pairBlocks`: construct a two-block input without discarding its
  structure.
* `Cslib.Crypto.SLHDSA.shakeInput`, `sha256Input`, `sha512Input`: exact byte packages.
* `Cslib.Crypto.SLHDSA.prf`, `f`, `h`, `tL`: the four addressed FIPS 205 calls.
* `Cslib.Crypto.SLHDSA.ValidTInput`: the underlying SHA-2 input-domain obligation for `T_l`.

## Main results

* `Cslib.Crypto.SLHDSA.validTInput_of_blocks_le_67`: every standardized block count is valid.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Section 4.1, Section 11.1,
  Sections 11.2--11.2.2, Figure 18 and Table 3][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA

open Cslib.Crypto

/-- The two concrete hash families used by the FIPS 205 parameter sets. -/
inductive HashFamily where
  | shake
  | sha2
  deriving DecidableEq, Repr

/-- One `n`-byte SLH-DSA security element. -/
abbrev NBytes (p : SecurityBytes) := FixedBytes p.count

/-- Two consecutive `n`-byte blocks, the input shape of `H`. -/
abbrev TwoNBytes (p : SecurityBytes) := FixedBytes (2 * p.count)

/-- Exactly `l` consecutive `n`-byte blocks, the input shape of `T_l`. -/
abbrev LBlocksBytes (p : SecurityBytes) (l : ℕ) := FixedBytes (l * p.count)

/-- The exact SHAKE input `PK.seed || ADRS || X`, using the canonical 32-byte address. -/
def shakeInput {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) : List Byte :=
  publicSeed.toList ++ address.toBytes.toList ++ message.toList

/-- SHAKE call packaging has `n + 32 + m` bytes. -/
@[simp] theorem length_shakeInput {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) :
    (shakeInput publicSeed address message).length = p.count + 32 + m := by
  simp [shakeInput, Nat.add_assoc]

/-- The exact SHA2 input `PK.seed || toByte(0, b - n) || ADRS^c || X`.

FIPS 205 uses `b = 64` for SHA-256 and `b = 128` for SHA-512. -/
private def sha2Input (blockBytes : ℕ) {p : SecurityBytes} {m : ℕ}
    (publicSeed : NBytes p) (address : Address) (message : FixedBytes m) : List Byte :=
  publicSeed.toList ++ List.replicate (blockBytes - p.count) 0 ++
    address.toCompressedBytes.toList ++ message.toList

/-- When the security element fits in the selected hash block, SHA2 packaging has
`b + 22 + m` bytes. -/
private theorem length_sha2Input (blockBytes : ℕ) {p : SecurityBytes} {m : ℕ}
    (publicSeed : NBytes p) (address : Address) (message : FixedBytes m)
    (h : p.count ≤ blockBytes) :
    (sha2Input blockBytes publicSeed address message).length = blockBytes + 22 + m := by
  simp only [sha2Input, List.length_append, FixedBytes.length_toList,
    List.length_replicate]
  omega

/-- The exact SHA-256 input `PK.seed || toByte(0, 64 - n) || ADRS^c || X`. -/
def sha256Input {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) : List Byte :=
  sha2Input 64 publicSeed address message

/-- SHA-256 call packaging has `64 + 22 + m` bytes. -/
@[simp] theorem length_sha256Input {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) :
    (sha256Input publicSeed address message).length = 64 + 22 + m := by
  exact length_sha2Input 64 publicSeed address message (p.count_le_32.trans (by decide))

/-- The exact SHA-512 input `PK.seed || toByte(0, 128 - n) || ADRS^c || X`. -/
def sha512Input {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) : List Byte :=
  sha2Input 128 publicSeed address message

/-- SHA-512 call packaging has `128 + 22 + m` bytes. -/
@[simp] theorem length_sha512Input {p : SecurityBytes} {m : ℕ} (publicSeed : NBytes p)
    (address : Address) (message : FixedBytes m) :
    (sha512Input publicSeed address message).length = 128 + 22 + m := by
  exact length_sha2Input 128 publicSeed address message (p.count_le_32.trans (by decide))

private def shakeFixed (input : List Byte) (outputBytes : ℕ) : FixedBytes outputBytes :=
  FixedBytes.ofListExact (Keccak.shake256 input outputBytes)
    (Keccak.length_shake256 input outputBytes)

private def sha256Truncated {p : SecurityBytes} (input : List Byte) : NBytes p :=
  fun i => SHA2.sha256 input (Fin.castLE p.count_le_32 i)

private def sha512Truncated {p : SecurityBytes} (input : List Byte) : NBytes p :=
  fun i => SHA2.sha512 input (Fin.castLE (p.count_le_32.trans (by decide)) i)

private def addressedOneBlock (family : HashFamily) {p : SecurityBytes}
    (publicSeed : NBytes p) (address : Address) (message : NBytes p) : NBytes p :=
  match family with
  | .shake => shakeFixed (shakeInput publicSeed address message) p.count
  | .sha2 => sha256Truncated (sha256Input publicSeed address message)

/-- FIPS 205 `PRF(PK.seed, SK.seed, ADRS)` from Sections 11.1--11.2.2. -/
def prf (family : HashFamily) {p : SecurityBytes} (publicSeed secretSeed : NBytes p)
    (address : Address) : NBytes p :=
  addressedOneBlock family publicSeed address secretSeed

/-- FIPS 205 `F(PK.seed, ADRS, M_1)` from Sections 11.1--11.2.2. -/
@[expose]
def f (family : HashFamily) {p : SecurityBytes} (publicSeed : NBytes p)
    (address : Address) (message : NBytes p) : NBytes p :=
  prf family publicSeed message address

/-- The standard's source-domain predicate for an arbitrary `T_l` call.

SHAKE256 accepts every finite byte string. For SHA2, this is exactly the input predicate of the
SHA-256 or SHA-512 branch selected by FIPS 205. The executable hash functions are total outside
this domain; this predicate records that a call is within the source domain rather than imposing a
runtime precondition. -/
@[expose] def ValidTInput (family : HashFamily) {p : SecurityBytes} {l : ℕ}
    (publicSeed : NBytes p) (address : Address) (message : LBlocksBytes p l) : Prop :=
  match family, p with
  | .shake, _ => True
  | .sha2, .bytes16 => SHA2.ValidSHA256Input (sha256Input publicSeed address message)
  | .sha2, .bytes24 => SHA2.ValidSHA512Input (sha512Input publicSeed address message)
  | .sha2, .bytes32 => SHA2.ValidSHA512Input (sha512Input publicSeed address message)

instance (family : HashFamily) {p : SecurityBytes} {l : ℕ}
    (publicSeed : NBytes p) (address : Address) (message : LBlocksBytes p l) :
    Decidable (ValidTInput family publicSeed address message) := by
  unfold ValidTInput
  cases family <;> cases p <;> infer_instance

/-- Every block count used by a standardized WOTS+ or FORS call is inside the SHA2 source domain.

The largest WOTS+ value is `len = 67`, while every standardized FORS value has `k ≤ 35`. -/
theorem validTInput_of_blocks_le_67 (family : HashFamily) {p : SecurityBytes} {l : ℕ}
    (publicSeed : NBytes p) (address : Address) (message : LBlocksBytes p l)
    (hl : l ≤ 67) : ValidTInput family publicSeed address message := by
  cases family <;> cases p <;>
    norm_num [SecurityBytes.count, ValidTInput, SHA2.ValidSHA256Input,
      SHA2.ValidSHA512Input] at * <;>
    omega

/-- FIPS 205 `T_l(PK.seed, ADRS, M_l)` from Sections 11.1--11.2.2, extended totally through the
total SHA2 functions. `ValidTInput` separately records the standard's source domain. -/
def tL (family : HashFamily) {p : SecurityBytes} (l : ℕ) (publicSeed : NBytes p)
    (address : Address) (message : LBlocksBytes p l) : NBytes p :=
  match family with
  | .shake => shakeFixed (shakeInput publicSeed address message) p.count
  | .sha2 =>
      match p with
      | .bytes16 => sha256Truncated (sha256Input publicSeed address message)
      | .bytes24 => sha512Truncated (sha512Input publicSeed address message)
      | .bytes32 => sha512Truncated (sha512Input publicSeed address message)

/-- FIPS 205 `H(PK.seed, ADRS, M_2)` from Sections 11.1--11.2.2. -/
@[expose]
def h (family : HashFamily) {p : SecurityBytes} (publicSeed : NBytes p)
    (address : Address) (message : TwoNBytes p) : NBytes p :=
  tL family 2 publicSeed address message

end Cslib.Crypto.SLHDSA
