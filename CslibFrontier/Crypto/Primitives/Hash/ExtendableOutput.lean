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
# Extendable-output functions on raw bit strings

A request specifies an input and a byte count. Every request at the same input reads a
prefix of one stream, even if the counts or the roles of the callers differ.
-/

public section

namespace Cslib.Crypto

/-- A bit-input XOF with output lengths in bytes. -/
structure ExtendableOutput where
  /-- The requested number of bytes at this raw input. -/
  read : List Bool → ℕ → List Byte
  /-- Every request returns the specified number of bytes. -/
  length_read : ∀ x n, (read x n).length = n
  /-- Requesting more bytes preserves every byte already read. -/
  take_read : ∀ x {m n}, m ≤ n → (read x n).take m = read x m

/-- Byte input uses the FIPS 202 least-significant-bit-first convention. -/
@[expose] def ExtendableOutput.readBytes (H : ExtendableOutput) (input : List Byte) :=
  H.read (Keccak.bytesToBitsLE input)

end Cslib.Crypto
