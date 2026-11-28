/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SIS.MLKEM.CiphertextEncoding
meta import CslibFrontier.Crypto.Computational.SIS.MLKEM.CiphertextEncoding

/-!
# Tests for ML-KEM ciphertext byte encoding

These ordinary-import clients pin the FIPS 203 Algorithm 14 order: all vector polynomials are
serialized first in increasing position order, followed by the scalar polynomial. They also pin
the three standard ciphertext lengths. They do not claim key serialization, external-interface
validation, correctness, security or FIPS validation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MLKEMCiphertextEncoding

open Cslib.Crypto Cslib.Crypto.MLKEM

set_option linter.hashCommand false

private def orderingCiphertext : Ciphertext mlkem512 :=
  (fun j i =>
      if j.val = 0 ∧ i.val = 0 then 1
      else if j.val = 0 ∧ i.val = 255 then 513
      else if j.val = 1 ∧ i.val = 0 then 2
      else 0,
    fun i => if i.val = 0 then 3 else 0)

/-- Byte `i` of the ML-KEM-512 encoding of `orderingCiphertext`, or `0` past the end. -/
private def orderingByte (i : ℕ) : ℕ :=
  if h : i < ciphertextByteLength mlkem512 (by decide) then
    (encodeCiphertext (by decide) orderingCiphertext ⟨i, h⟩).val
  else 0

-- Coefficient 255 of the first polynomial is 513: its low and high bits occupy the last two
-- bytes of that polynomial. The next nonzero byte begins the second polynomial at byte 320.
#guard orderingByte 0 == 1
#guard orderingByte 318 == 0x40
#guard orderingByte 319 == 0x80
#guard orderingByte 320 == 2
#guard orderingByte 639 == 0
-- The scalar polynomial follows both 320-byte vector polynomials.
#guard orderingByte 640 == 3

#guard decide (decodeCiphertext (by decide)
  (encodeCiphertext (P := mlkem512) (by decide) orderingCiphertext) = orderingCiphertext)

example : decodeCiphertext (by decide)
    (encodeCiphertext (P := mlkem512) (by decide) orderingCiphertext) = orderingCiphertext :=
  decodeCiphertext_encodeCiphertext _ orderingCiphertext

/-- An ML-KEM-1024 ciphertext whose only nonzero coefficients are the last ones of the final
vector polynomial (width 11) and of the scalar polynomial (width 5). -/
private def lastCiphertext1024 : Ciphertext mlkem1024 :=
  (fun j i => if j.val = 3 ∧ i.val = 255 then 2047 else 0,
    fun i => if i.val = 255 then 31 else 0)

/-- Byte `i` of the ML-KEM-1024 encoding of `lastCiphertext1024`, or `0` past the end. -/
private def lastByte1024 (i : ℕ) : ℕ :=
  if h : i < ciphertextByteLength mlkem1024 (by decide) then
    (encodeCiphertext (by decide) lastCiphertext1024 ⟨i, h⟩).val
  else 0

-- The four 352-byte vector polynomials end at byte 1407; the 160-byte scalar ends at byte 1567.
#guard lastByte1024 1405 == 0
#guard lastByte1024 1406 == 0xE0
#guard lastByte1024 1407 == 0xFF
#guard lastByte1024 1408 == 0
#guard lastByte1024 1567 == 0xF8

#guard decide (decodeCiphertext (by decide)
  (encodeCiphertext (P := mlkem1024) (by decide) lastCiphertext1024) = lastCiphertext1024)

example : ciphertextByteLength mlkem512 (by decide) = 768 ∧
    ciphertextByteLength mlkem768 (by decide) = 1088 ∧
    ciphertextByteLength mlkem1024 (by decide) = 1568 := by
  decide

example : ciphertextBitLength mlkem512 (by decide) = 6144 ∧
    ciphertextBitLength mlkem768 (by decide) = 8704 ∧
    ciphertextBitLength mlkem1024 (by decide) = 12544 := by
  decide

end CslibFrontierTests.Crypto.MLKEMCiphertextEncoding
