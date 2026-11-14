/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial

/-!
# The polynomial-basis byte field used by HQC

The HQC v5.1 reference implementation represents `GF(2^8)` as binary polynomials modulo
`X^8 + X^4 + X^3 + X + 1`, whose least-significant-coefficient-first code is `0x11b`, and uses
the byte `0x03` as its primitive element [HQC2026, §3.5.2, pp. 23–31].

`Cslib.BinaryField 8` already uses the irreducible degree-eight binary polynomial of least code.
`Cslib.Crypto.HQC.hqcByteModulus_eq` identifies that polynomial with `Cslib.polyOfCode 0x11b`,
using the repository's checked trial-division search only in the proof.  Thus `HQCByte` reuses the
existing explicit binary-field implementation rather than introducing a parallel quotient.

Bytes are the eight power-basis coefficients, least significant bit first.  `hqcByteOfNat` keeps
the low eight bits of a natural number in that basis, and `hqcAlpha` is therefore exactly byte
`0x03`.  Proving `orderOf hqcAlpha = 255` remains a separate explicit obligation; no primitive-
element or decoder-correctness claim follows merely from defining the byte.

## Main definitions

* `Cslib.Crypto.HQC.HQCByte`: the exact `0x11b` polynomial-basis field.
* `Cslib.Crypto.HQC.hqcByteEquivBits`: the least-significant-bit-first byte representation.
* `Cslib.Crypto.HQC.hqcByteOfNat`: the field element represented by the low eight bits.
* `Cslib.Crypto.HQC.hqcAlpha`: the source byte `0x03`.
* `Cslib.Crypto.HQC.HQCAlphaIsPrimitive`: the outstanding order-255 obligation.

## Main results

* `Cslib.Crypto.HQC.hqcByteModulus_eq`: the reused binary-field modulus has code `0x11b`.
* `Cslib.Crypto.HQC.card_hqcByte`: the field has 256 elements.
* `Cslib.Crypto.HQC.hqcByteEquivBits_hqcByteOfNat`: the byte representation is the low-bit map.

## References

* [HQC specification, version 5.1][HQC2026], §3.5.2, pp. 23–31.
-/

@[expose] public section

namespace Cslib.Crypto.HQC

open Cslib.BitString

/-- The least-code irreducible binary polynomial of degree eight is the HQC modulus `0x11b`. -/
theorem hqcByteModulus_eq : Cslib.leastIrreducible 8 = Cslib.polyOfCode 0x11b := by
  rw [← Cslib.polyOfCode_leastIrreducibleCode
    (B := 512) (p := 8) (by decide) (by decide)]
  congr 1
  decide

/-- The exact polynomial-basis byte field used by HQC. -/
abbrev HQCByte := Cslib.BinaryField 8

/-- The source byte representation: eight power-basis coefficients, least significant bit first. -/
noncomputable def hqcByteEquivBits : HQCByte ≃+ BitString 8 :=
  Cslib.BinaryField.equivBits (by decide)

/-- The field element represented by the low eight bits of `m`, least significant bit first. -/
noncomputable def hqcByteOfNat (m : ℕ) : HQCByte :=
  hqcByteEquivBits.symm fun i => m.testBit i

/-- The primitive-element byte `0x03` used by the HQC reference tables. -/
noncomputable def hqcAlpha : HQCByte :=
  hqcByteOfNat 0x03

/-- The outstanding source obligation that byte `0x03` generates all 255 nonzero field
elements. -/
def HQCAlphaIsPrimitive : Prop :=
  orderOf hqcAlpha = 255

/-- The exact HQC byte field has 256 elements. -/
theorem card_hqcByte : Fintype.card HQCByte = 256 := by
  simpa using Cslib.BinaryField.card (w := 8) (by decide)

/-- Encoding a natural number as a byte retains exactly its low eight bits. -/
@[simp]
theorem hqcByteEquivBits_hqcByteOfNat (m : ℕ) :
    hqcByteEquivBits (hqcByteOfNat m) = fun i => m.testBit i :=
  hqcByteEquivBits.apply_symm_apply _

/-- The source element `hqcAlpha` has byte representation `0x03`. -/
theorem hqcByteEquivBits_hqcAlpha :
    hqcByteEquivBits hqcAlpha = fun i => (0x03 : ℕ).testBit i := by
  rw [hqcAlpha, hqcByteEquivBits_hqcByteOfNat]

end Cslib.Crypto.HQC
