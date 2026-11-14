/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.SNOVA.VerificationFrontend
meta import CslibFrontier.Crypto.Computational.SNOVA.VerificationFrontend

/-!
# Tests for the SNOVA v3.0 verification frontend

These source-level clients exercise Table 4/Algorithm 2 grouped decoding, Algorithm 12's digest
concatenation and non-square reindexing, Algorithm 20's exact signature parsing and Algorithm 21's
final equality boundary. They do not instantiate SNOVA's public map or make a security claim.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SNOVAVerificationFrontend

open Cslib.Crypto Cslib.Crypto.SNOVA

set_option linter.hashCommand false

private def params : VerificationParams where
  encoding := .q16
  v := 1
  o := 2
  l := 2
  r := 3

private def oddParams : VerificationParams where
  encoding := .q16
  v := 2
  o := 1
  l := 1
  r := 1

private def natToBytesLE (count value : ℕ) : List Byte :=
  (List.range count).map fun i =>
    ⟨value / 256 ^ i % 256, Nat.mod_lt _ (by decide)⟩

private def values (xs : List ℕ) : List (FieldElement params) :=
  xs.map fun x => ⟨x % 16, Nat.mod_lt _ (by decide)⟩

/-! ### Table 4 and Algorithm 2 -/

#guard encodedByteCount .q13 16 == 8
#guard encodedByteCount .q16 3 == 2

-- Within each byte, q = 16 decodes the low nibble before the high nibble.
#guard (decodeCoefficients params 2 [0xBA]).map (fun x => x.val) == [10, 11]

-- The integer 11^16 has sixteen zero low base-11 digits and a nonzero unused quotient.
private def illegalQ11 : List Byte := natToBytesLE 7 (11 ^ 16)

#guard (decodeCoefficients ({ params with encoding := .q11 }) 16 illegalQ11).map
    (fun x => x.val) == List.replicate 16 0
#guard (decodeExternal ({ params with encoding := .q11 }) 16 illegalQ11).isNone

/-! ### Algorithm 12 -/

private def salt : FixedBytes 16 := fun _ => 0xC3

private def labelledXof : XOF := fun input outputBytes _ =>
  if outputBytes = 48 then 0xA1
  else if outputBytes = 64 then 0xB2
  else input.getD 0 0

#guard verificationHashInputWithXof labelledXof [0x01] [0x02] salt ==
  List.replicate 48 0xA1 ++ List.replicate 64 0xB2 ++ List.replicate 16 0xC3

-- With o = 2, l = 2 and r = 3, this catches swapping either matrix axis or block axis.
#guard (reorderVerificationHash params (values (List.range 12))).map (fun x => x.val) ==
  [0, 2, 4, 1, 3, 5, 6, 8, 10, 7, 9, 11]

/-! ### Algorithms 20 and 21 -/

private def payload : List Byte :=
  [0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE, 0x10]

private def signature : List Byte := payload ++ List.replicate 16 0xA5

#guard params.signatureCoefficientCount == 18
#guard params.signaturePayloadBytes == 9
#guard params.signatureBytes == 25
#guard (decodeSignature params signature).isSome
#guard (decodeSignature params signature).map (fun decoded =>
    (decoded.matrices 0 0 0).val) == some 0
#guard (decodeSignature params signature).map (fun decoded =>
    (decoded.matrices 2 1 2).val) == some 1
#guard (decodeSignature params signature).map (fun decoded => decoded.salt.toList) ==
  some (List.replicate 16 0xA5)

-- Exact length is part of the Algorithm 20 boundary.
#guard (decodeSignature params signature.dropLast).isNone

-- Three q = 16 coefficients use two bytes; the unused high nibble must be zero externally.
private def illegalOddSignature : List Byte := [0x21, 0xF3] ++ List.replicate 16 0

#guard oddParams.signatureCoefficientCount == 3
#guard (decodeSignature oddParams illegalOddSignature).isNone

private def publicKey : List Byte := [0x31, 0x41]
private def wrongPublicKey : List Byte := [0x31]
private def message : List Byte := [0x59]

private def matchingEvaluator : PublicMapEvaluator params := fun pk _ =>
  if pk = publicKey then
    some (verificationHashWithXof params labelledXof publicKey message (fun _ => 0xA5))
  else
    none

#guard verifyWithXof params labelledXof matchingEvaluator publicKey message signature
-- The original key bytes reach the callback, which owns key-specific validation and rejection.
#guard !(verifyWithXof params labelledXof matchingEvaluator wrongPublicKey message signature)
#guard !(verifyWithXof params labelledXof (fun _ _ => some []) publicKey message signature)
#guard !(verifyWithXof params labelledXof (fun _ _ => none) publicKey message signature)
#guard !(verifyWithXof params labelledXof matchingEvaluator publicKey message signature.dropLast)

end CslibFrontierTests.Crypto.SNOVAVerificationFrontend
