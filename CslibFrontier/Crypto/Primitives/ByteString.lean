/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Init
public import Mathlib.Data.Fin.Tuple.Take
import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder
import CslibFrontier.Foundations.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Byte strings

This module supplies the byte boundary shared by executable cryptographic primitives. A byte is an
unsigned integer below 256, and `FixedBytes n` records a byte-string length in its type. The
big-endian bit conversion follows the byte convention used by FIPS 180-4 and FIPS 205; primitives
with a different within-byte convention, such as FIPS 202's Keccak, keep that conversion explicit.

## Main definitions

* `Cslib.Crypto.Byte`: one unsigned byte.
* `Cslib.Crypto.FixedBytes`: a byte string whose length is part of its type.
* `Cslib.Crypto.FixedBytes.ofListExact`: turn a list with a proved length into typed bytes.
* `Cslib.Crypto.bytesToBitsBE`: big-endian serialization of a list of bytes.
* `Cslib.Crypto.bitsToFixedBytesBE`: split a bit list into typed big-endian bytes.

## Main results

* `Cslib.Crypto.length_bytesToBitsBE`: byte serialization has eight bits per byte.
* `Cslib.Crypto.byteOfBitsBE_byteBitsBE`, `Cslib.Crypto.byteBitsBE_byteOfBitsBE`: converting one
  byte to bits and back is exact in either direction.
* `Cslib.Crypto.bytesToBitsBE_bitsToFixedBytesBE`: an exact-length bit string round-trips through
  typed bytes.
* `Cslib.Crypto.bytesToBitsBE_natToFixedBytesBE`: natural-number serialization retains exactly
  its low `8n` bits.
* `Cslib.Crypto.bytesToBitsBE_lt_iff_lt`: equal-length byte strings and their big-endian bit
  serializations have the same lexicographic order.
-/

public section

namespace Cslib.Crypto

open Cslib.BitString

/-- One byte, represented by its unsigned integer value. -/
abbrev Byte := Fin (2 ^ 8)

/-- A byte string whose byte length is part of its type. -/
abbrev FixedBytes (n : ℕ) := Fin n → Byte

namespace FixedBytes

/-- Turn a list whose length is known exactly into a fixed-length byte string. -/
def ofListExact {n : ℕ} (X : List Byte) (h : X.length = n) : FixedBytes n := fun i =>
  X.get ⟨i.val, by simp [h]⟩

/-- The list view of a fixed-length byte string. -/
@[expose] def toList {n : ℕ} (X : FixedBytes n) : List Byte := List.ofFn X

/-- The list view has the byte length recorded in the type. -/
@[simp] theorem length_toList {n : ℕ} (X : FixedBytes n) : X.toList.length = n := by
  simp [toList]

/-- The list view of `ofListExact X h` is the list `X` it was built from. -/
@[simp] theorem toList_ofListExact {n : ℕ} (X : List Byte) (h : X.length = n) :
    (ofListExact X h).toList = X := by
  subst h; exact List.ofFn_get X

/-- A byte string of length `n` is the list view of a fixed-length byte string. -/
theorem exists_toList {n : ℕ} {bytes : List Byte} (h : bytes.length = n) :
    ∃ v : FixedBytes n, v.toList = bytes :=
  ⟨ofListExact bytes h, toList_ofListExact bytes h⟩

end FixedBytes

/-- The eight big-endian bits of a byte. -/
@[expose]
def byteBitsBE (x : Byte) : List Bool := binaryWord 8 x

/-- The bits of a byte list in big-endian order within each byte. -/
@[expose]
def bytesToBitsBE : List Byte → List Bool
  | [] => []
  | x :: X => byteBitsBE x ++ bytesToBitsBE X

/-- A byte list has eight serialized bits per byte. -/
@[simp] theorem length_bytesToBitsBE (X : List Byte) :
    (bytesToBitsBE X).length = 8 * X.length := by
  induction X with
  | nil => simp [bytesToBitsBE]
  | cons x X ih =>
    simp only [bytesToBitsBE, byteBitsBE, List.length_append, ih, List.length_cons,
      length_binaryWord x.isLt]
    omega

/-- One byte and its eight-bit big-endian serialization have the same strict order. -/
private theorem byteBitsBE_lt_iff_lt (x y : Byte) :
    byteBitsBE x < byteBitsBE y ↔ x < y := by
  rw [← BitString.binaryValue_lt_iff_lt (by simp [byteBitsBE, length_binaryWord x.isLt,
    length_binaryWord y.isLt])]
  simp [byteBitsBE]

/-- Equal-length byte strings and their big-endian bit serializations have the same strict
lexicographic order. -/
theorem bytesToBitsBE_lt_iff_lt {X Y : List Byte} (hlength : X.length = Y.length) :
    bytesToBitsBE X < bytesToBitsBE Y ↔ X < Y := by
  induction X generalizing Y with
  | nil =>
    obtain rfl : Y = [] := List.length_eq_zero_iff.mp hlength.symm
    simp [bytesToBitsBE]
  | cons x X ih =>
    obtain ⟨y, Y, rfl⟩ := List.exists_cons_of_length_eq_add_one hlength.symm
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength
    have hlen (z : Byte) : (byteBitsBE z).length = 8 := length_binaryWord z.isLt
    have happ {a b : Byte} (h : a < b) (A B : List Bool) :
        byteBitsBE a ++ A < byteBitsBE b ++ B :=
      List.append_lt_append_of_lt_of_length_eq ((byteBitsBE_lt_iff_lt a b).2 h)
        ((hlen a).trans (hlen b).symm) A B
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact iff_of_true (happ hlt _ _) (List.Lex.rel hlt)
    · have hpre (s : List Bool) :
          s ++ bytesToBitsBE X < s ++ bytesToBitsBE Y ↔ bytesToBitsBE X < bytesToBitsBE Y := by
        induction s with
        | nil => rfl
        | cons _ _ ihs => exact List.lex_cons_iff.trans ihs
      exact (hpre (byteBitsBE x)).trans ((ih hlength).trans List.lex_cons_iff.symm)
    · exact iff_of_false (not_lt_of_gt (happ hgt _ _)) (not_lt_of_gt (List.Lex.rel hgt))

/-- Read at most eight big-endian bits as one byte. Missing low-order bits are not added; callers
that require a full byte should supply an eight-bit chunk. -/
def byteOfBitsBE (bits : List Bool) : Byte :=
  ⟨binaryValue (bits.take 8), by
    exact Nat.lt_of_lt_of_le (binaryValue_lt_two_pow (bits.take 8))
      (Nat.pow_le_pow_right (by decide) (List.length_take_le 8 bits))⟩

/-- Serializing one byte to eight big-endian bits and reading it back recovers the byte. -/
@[simp] theorem byteOfBitsBE_byteBitsBE (x : Byte) : byteOfBitsBE (byteBitsBE x) = x :=
  Fin.ext (by simp [byteOfBitsBE, byteBitsBE, List.take_of_length_le (length_binaryWord x.isLt).le])

/-- Reading an eight-bit word as a byte and serializing it recovers the word. -/
@[simp] theorem byteBitsBE_byteOfBitsBE (bits : List Bool) (h : bits.length = 8) :
    byteBitsBE (byteOfBitsBE bits) = bits :=
  binaryValue_injective_of_length_eq
    (by simpa [byteBitsBE, h] using length_binaryWord (byteOfBitsBE bits).isLt)
    (by simp [byteBitsBE, binaryValue_binaryWord, byteOfBitsBE, List.take_of_length_le h.le])

/-- Split a bit list into `n` consecutive big-endian bytes. An incomplete or absent final chunk is
read using `byteOfBitsBE`; exact-length clients avoid that fallback by construction. -/
def bitsToFixedBytesBE (n : ℕ) (bits : List Bool) : FixedBytes n := fun i =>
  byteOfBitsBE ((bits.drop (8 * i.val)).take 8)

/-- An exact `8 * n`-bit word round-trips through its `n` typed big-endian bytes. -/
@[simp] theorem bytesToBitsBE_bitsToFixedBytesBE (n : ℕ) (bits : List Bool)
    (h : bits.length = 8 * n) :
    bytesToBitsBE ((bitsToFixedBytesBE n bits).toList) = bits := by
  induction n generalizing bits with
  | zero =>
    simp [List.length_eq_zero_iff.mp (by simpa using h : bits.length = 0),
      FixedBytes.toList, bytesToBitsBE]
  | succ n ih =>
    have h8 : 8 ≤ bits.length := by omega
    have hlist : (bitsToFixedBytesBE (n + 1) bits).toList =
        byteOfBitsBE (bits.take 8) :: (bitsToFixedBytesBE n (bits.drop 8)).toList := by
      simp only [bitsToFixedBytesBE, FixedBytes.toList, List.ofFn_succ, List.cons.injEq,
        List.ofFn_inj]
      exact ⟨by simp, funext fun i => by
        simp [bitsToFixedBytesBE, List.drop_drop, Nat.mul_add, Nat.add_comm]⟩
    simp only [hlist, bytesToBitsBE]
    rw [byteBitsBE_byteOfBitsBE _ (by simp [h8]), ih _ (by simp; omega), List.take_append_drop]

/-- Encode a natural number as exactly `n` big-endian bytes, retaining its low `8n` bits. -/
def natToFixedBytesBE (n value : ℕ) : FixedBytes n := fun i =>
  ⟨value / 2 ^ (8 * (n - 1 - i.val)) % 256, Nat.mod_lt _ (by decide)⟩

private theorem natToFixedBytesBE_toList_succ (n value : ℕ) :
    (natToFixedBytesBE (n + 1) value).toList =
      ⟨value / 2 ^ (8 * n) % 256, Nat.mod_lt _ (by decide)⟩ ::
        (natToFixedBytesBE n value).toList := by
  simp only [natToFixedBytesBE, FixedBytes.toList, List.ofFn_succ, List.cons.injEq, List.ofFn_inj]
  refine ⟨rfl, funext fun i => Fin.ext ?_⟩
  simp only [Fin.val_succ]
  congr 3; omega

/-- Serializing a natural number as `n` bytes produces its low `8n` bits in big-endian order. -/
theorem bytesToBitsBE_natToFixedBytesBE (n value : ℕ) :
    bytesToBitsBE (natToFixedBytesBE n value).toList =
      binaryWord (8 * n) (value % 2 ^ (8 * n)) := by
  induction n with
  | zero => simp [Nat.mod_one]; rfl
  | succ n ih =>
    rw [natToFixedBytesBE_toList_succ]
    simp only [bytesToBitsBE, byteBitsBE, ih]
    refine binaryValue_injective_of_length_eq ?_ ?_
    · rw [List.length_append, length_binaryWord (Nat.mod_lt _ (by decide)),
        length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _)),
        length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _))]
      omega
    · rw [binaryValue_append, binaryValue_binaryWord, binaryValue_binaryWord,
        binaryValue_binaryWord, length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos _)),
        show 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 by rw [Nat.mul_add, Nat.pow_add],
        ← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_mod value (2 ^ (8 * n)) 256]
      exact Nat.div_add_mod' _ _

end Cslib.Crypto
