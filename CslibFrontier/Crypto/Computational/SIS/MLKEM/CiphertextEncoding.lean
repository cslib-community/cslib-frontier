/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Encoding
public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE

/-!
# ML-KEM ciphertext byte encoding

FIPS 203 Algorithm 14 encodes the `k` polynomials of a compressed K-PKE ciphertext's vector part
at width `d_u`, encodes its scalar part at width `d_v`, and concatenates those bytes in that order.
Algorithm 15 parses the same two consecutive regions. The resulting lengths are 768, 1088 and
1568 bytes for ML-KEM-512, ML-KEM-768 and ML-KEM-1024, respectively (Section 8, Table 3).

This module connects that exact byte layout to the existing coefficient-form `Ciphertext` type for
the three standardized parameter records. Exact-length byte types make the Algorithm 15 length
boundary explicit. This does not serialize keys, identify NTT and coefficient representations,
implement the external ML-KEM interface's input checks, or prove correctness, security, execution
cost, constant-time behavior or FIPS validation.

## Main definitions

* `Cslib.Crypto.MLKEM.ciphertextByteLength`, `Cslib.Crypto.MLKEM.CiphertextBytes`: the
  `Params.IsStandard`-gated typed wire boundary.
* `Cslib.Crypto.MLKEM.encodeCiphertext`, `Cslib.Crypto.MLKEM.decodeCiphertext`: the ciphertext
  codec for a parameter record satisfying `Params.IsStandard`.

## Main results

* `Cslib.Crypto.MLKEM.decodeCiphertext_encodeCiphertext`: semantic ciphertexts round-trip for
  every standard parameter record.
* `Cslib.Crypto.MLKEM.encodeCiphertext_decodeCiphertext`: every exact-length standard ciphertext
  byte string round-trips.
* `Cslib.Crypto.MLKEM.ciphertextByteLength_mlkem512`: the standard byte lengths, with analogous
  results for ML-KEM-768 and ML-KEM-1024.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 5,
  Algorithms 14–15 and Section 8, Table 3][NISTFIPS203].
-/

public section

namespace Cslib.Crypto.MLKEM

/-- The bytes in the `k` width-`d_u` vector encodings followed by the width-`d_v` scalar
encoding for a standard parameter record. The standardness proof prevents this FIPS-specific
boundary from being applied to the library's arbitrary-degree parameter records. -/
@[expose]
def ciphertextByteLength (P : Params) (_h : P.IsStandard) : ℕ :=
  P.k * (32 * P.du) + 32 * P.dv

/-- The byte length agrees with the factored expression in FIPS 203 Algorithm 14. -/
theorem ciphertextByteLength_eq_fips (P : Params) (h : P.IsStandard) :
    ciphertextByteLength P h = 32 * (P.du * P.k + P.dv) := by
  simp only [ciphertextByteLength, Nat.mul_add]
  ac_rfl

/-- The exact serialized ciphertext boundary for a parameter record proved standard. -/
abbrev CiphertextBytes (P : Params) (h : P.IsStandard) := FixedBytes (ciphertextByteLength P h)

/-- The serialized ciphertext boundary measured in bits. This is the I/O width to charge when the
codec is later realized as a machine program; it is not a running-time or program-size bound. -/
@[expose]
def ciphertextBitLength (P : Params) (h : P.IsStandard) : ℕ :=
  8 * ciphertextByteLength P h

/-- ML-KEM-512 ciphertexts occupy 768 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem512 (h : mlkem512.IsStandard) :
    ciphertextByteLength mlkem512 h = 768 := by
  rfl

/-- ML-KEM-768 ciphertexts occupy 1088 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem768 (h : mlkem768.IsStandard) :
    ciphertextByteLength mlkem768 h = 1088 := by
  rfl

/-- ML-KEM-1024 ciphertexts occupy 1568 bytes. -/
@[simp] theorem ciphertextByteLength_mlkem1024 (h : mlkem1024.IsStandard) :
    ciphertextByteLength mlkem1024 h = 1568 := by
  rfl

/-- ML-KEM-512 ciphertexts occupy 6144 bits. -/
@[simp] theorem ciphertextBitLength_mlkem512 (h : mlkem512.IsStandard) :
    ciphertextBitLength mlkem512 h = 6144 := by
  rfl

/-- ML-KEM-768 ciphertexts occupy 8704 bits. -/
@[simp] theorem ciphertextBitLength_mlkem768 (h : mlkem768.IsStandard) :
    ciphertextBitLength mlkem768 h = 8704 := by
  rfl

/-- ML-KEM-1024 ciphertexts occupy 12544 bits. -/
@[simp] theorem ciphertextBitLength_mlkem1024 (h : mlkem1024.IsStandard) :
    ciphertextBitLength mlkem1024 h = 12544 := by
  rfl

private abbrev CiphertextParts (k : ℕ) (du dv : CodecWidth) :=
  (Fin k → Coefficients du) × Coefficients dv

private def encodeCiphertextParts (k : ℕ) (du dv : CodecWidth)
    (ct : CiphertextParts k du dv) : FixedBytes (k * (32 * du.val) + 32 * dv.val) :=
  Fin.append (byteEncodeVector du k ct.1) (byteEncode dv ct.2)

private def decodeCiphertextParts (k : ℕ) (du dv : CodecWidth)
    (B : FixedBytes (k * (32 * du.val) + 32 * dv.val)) : CiphertextParts k du dv :=
  (byteDecodeVector du k fun i => B (Fin.castAdd (32 * dv.val) i),
    byteDecode dv fun i => B (Fin.natAdd (k * (32 * du.val)) i))

@[simp] private theorem decodeCiphertextParts_encodeCiphertextParts (k : ℕ)
    (du dv : CodecWidth) (ct : CiphertextParts k du dv) :
    decodeCiphertextParts k du dv (encodeCiphertextParts k du dv ct) = ct := by
  simp [decodeCiphertextParts, encodeCiphertextParts]

private theorem encodeCiphertextParts_decodeCiphertextParts (k : ℕ)
    (du dv : CodecWidth) (hdu : du.val ≤ 11) (hdv : dv.val ≤ 11)
    (B : FixedBytes (k * (32 * du.val) + 32 * dv.val)) :
    encodeCiphertextParts k du dv (decodeCiphertextParts k du dv B) = B := by
  simp only [encodeCiphertextParts, decodeCiphertextParts]
  rw [byteEncodeVector_byteDecodeVector du hdu, byteEncode_byteDecode dv hdv]
  exact Fin.append_castAdd_natAdd

/-! ### Standard parameter records -/

/-- The vector-part width `d_u` of a standard parameter record, as a codec width below 12. -/
private def duWidth (P : Params) (h : P.IsStandard) : CodecWidth :=
  ⟨P.du, by rcases h with rfl | rfl | rfl <;> decide,
    by rcases h with rfl | rfl | rfl <;> decide⟩

/-- The scalar-part width `d_v` of a standard parameter record, as a codec width below 12. -/
private def dvWidth (P : Params) (h : P.IsStandard) : CodecWidth :=
  ⟨P.dv, by rcases h with rfl | rfl | rfl <;> decide,
    by rcases h with rfl | rfl | rfl <;> decide⟩

private theorem duWidth_le (P : Params) (h : P.IsStandard) : (duWidth P h).val ≤ 11 := by
  rcases h with rfl | rfl | rfl <;> decide

private theorem dvWidth_le (P : Params) (h : P.IsStandard) : (dvWidth P h).val ≤ 11 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- A degree-`n` polynomial with coefficients modulo `m` is a codec input once `n = 256` and `m`
is the codec modulus. -/
private def polyEquiv {n m : ℕ} (d : CodecWidth) (hn : n = 256) (hm : m = codecModulus d) :
    (Fin n → ZMod m) ≃ Coefficients d :=
  (finCongr hn).arrowCongr (ZMod.ringEquivCongr hm).toEquiv

/-- For a standard parameter record, a compressed ciphertext is a vector of `d_u`-bit codec
inputs together with one `d_v`-bit codec input. -/
private def partsEquiv (P : Params) (h : P.IsStandard) :
    Ciphertext P ≃ CiphertextParts P.k (duWidth P h) (dvWidth P h) :=
  (Equiv.piCongrRight fun _ =>
      polyEquiv _ h.bounds.1 (codecModulus_eq_two_pow (duWidth_le P h)).symm).prodCongr
    (polyEquiv _ h.bounds.1 (codecModulus_eq_two_pow (dvWidth_le P h)).symm)

/-- Serialize a ciphertext in the order of FIPS 203 Algorithm 14: the `k` vector polynomials at
width `d_u` in increasing position order, then the scalar polynomial at width `d_v`. -/
def encodeCiphertext {P : Params} (h : P.IsStandard) (ct : Ciphertext P) :
    CiphertextBytes P h :=
  encodeCiphertextParts P.k (duWidth P h) (dvWidth P h) (partsEquiv P h ct)

/-- Parse an exact-length ciphertext as in FIPS 203 Algorithm 15: the first `32 * d_u * k` bytes
are the vector part and the final `32 * d_v` bytes are the scalar part. -/
def decodeCiphertext {P : Params} (h : P.IsStandard) (B : CiphertextBytes P h) : Ciphertext P :=
  (partsEquiv P h).symm (decodeCiphertextParts P.k (duWidth P h) (dvWidth P h) B)

/-- A ciphertext for any standard parameter record survives serialization and parsing. -/
@[simp] theorem decodeCiphertext_encodeCiphertext {P : Params} (h : P.IsStandard)
    (ct : Ciphertext P) : decodeCiphertext h (encodeCiphertext h ct) = ct := by
  simp [decodeCiphertext, encodeCiphertext]

/-- Every exact-length ciphertext byte string for a standard parameter record survives parsing
and serialization. -/
@[simp] theorem encodeCiphertext_decodeCiphertext {P : Params} (h : P.IsStandard)
    (B : CiphertextBytes P h) : encodeCiphertext h (decodeCiphertext h B) = B := by
  simp only [decodeCiphertext, encodeCiphertext, Equiv.apply_symm_apply]
  exact encodeCiphertextParts_decodeCiphertextParts _ _ _ (duWidth_le P h) (dvWidth_le P h) B

end Cslib.Crypto.MLKEM
