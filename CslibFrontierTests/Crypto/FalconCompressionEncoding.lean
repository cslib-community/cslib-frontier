/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.CompressionEncoding

/-!
# Tests for Falcon v1.2 reference compression encoding

These ordinary-import clients check exact emitted bytes, the reference encoder's independent
range and capacity failures, and concrete round-trips through the existing canonical decoder.
The examples do not replace the general codec round-trip theorem still tracked separately.
-/

namespace CslibFrontierTests.Crypto.FalconCompressionEncoding

open Cslib.Crypto.Falcon

public section

private abbrev twoParams : VerificationParams where
  n := 2
  q := 12289
  squaredNormBound := 100
  q_pos := by decide

private def oneZero : IntegerPolynomial twoParams := fun i =>
  if i.val = 0 then 1 else 0

/-- The coefficient pair `(1, 0)` occupies eighteen bits and produces the same three-byte fixture
used by the existing canonical-decoder client. -/
example : referenceCompress 3 twoParams oneZero = some [1, 128, 64] := by decide

/-- The exact three-byte capacity succeeds, while a one-byte-short output buffer fails. -/
example : (referenceCompress 3 twoParams oneZero).isSome = true ∧
    referenceCompress 2 twoParams oneZero = none := by decide

/-- The exact emitted bytes round-trip through the existing canonical decoder. -/
example : (referenceCompress 3 twoParams oneZero).bind (decompress twoParams) =
    some oneZero := by decide

private abbrev mixedParams : VerificationParams where
  n := 4
  q := 12289
  squaredNormBound := 5000000
  q_pos := by decide

private def mixed : IntegerPolynomial mixedParams := fun i =>
  match i.val with
  | 0 => -5
  | 1 => 128
  | 2 => -2047
  | _ => 0

/-- Mixed signs, a unary high part and the maximal negative reference coefficient survive a
concrete codec round-trip. Their 52 coefficient bits occupy exactly seven bytes. -/
example : compressedBitLength mixedParams mixed = 52 ∧
    (referenceCompress 7 mixedParams mixed).bind (decompress mixedParams) = some mixed := by
  decide

private abbrev oneParams : VerificationParams where
  n := 1
  q := 12289
  squaredNormBound := 5000000
  q_pos := by decide

private def coefficient (x : ℤ) : IntegerPolynomial oneParams := fun _ => x

/-- Both signs at magnitude `2047` encode in three bytes; magnitudes `2048` fail the reference
range check even when the output capacity is ample. -/
example : (referenceCompress 3 oneParams (coefficient 2047)).isSome = true ∧
    (referenceCompress 3 oneParams (coefficient (-2047))).isSome = true ∧
    referenceCompress 4 oneParams (coefficient 2048) = none ∧
    referenceCompress 4 oneParams (coefficient (-2048)) = none := by decide

end

end CslibFrontierTests.Crypto.FalconCompressionEncoding
