/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.RingTheory.Polynomial.Div

/-!
# The shortened Reed–Solomon layer used by HQC

HQC uses a shortened systematic Reed–Solomon code over a polynomial-basis copy of
`GF(2^8)`.  The parity bytes precede the message bytes.  For correction capacity `t`, primitive
element `alpha`, and message polynomial `m`, the generator and encoded polynomial are

`g(X) = product (X + alpha^i), 1 <= i <= 2t`,

`c(X) = b(X) + X^(2t) m(X)`,

where `b` is the remainder of `X^(2t) m(X)` modulo `g` [HQC2026, §3.5.2, pp. 23–31].
The three parameter triples `(n1, k1, t1)` are `(46, 16, 15)`, `(56, 24, 16)`, and
`(90, 32, 29)` [HQC2026, Table 6].

The reference decoder computes `2t` syndromes, obtains an error-locator polynomial with a
constant-time Berlekamp update, performs a Chien search only on the final `k1` message positions,
and evaluates the auxiliary polynomial `Z` and the odd part of the locator there.  A message byte
is corrected only when the locator vanishes and the odd-part denominator is nonzero.  The
definitions below pin every stage except the Berlekamp update: `hqcRSDecodeWithLocator` takes
that stage as an explicit argument and implements the remaining total best-effort decoder.

The source coefficient arrays below are from the `RS_POLY_COEFS` macros in the HQC v5.1.0
reference implementation, tag commit `06567ccbad10580d78dd7863b15d23f41076d57f`.  Coefficients
and codeword coordinates are listed from constant term upward.  The implementation uses the
modulus byte `0x11b` and primitive-element byte `0x03`; identifying an explicit Lean field model
with that byte representation, implementing the Berlekamp stage, and proving bounded-error
correction remain required before this is a complete source decoder.

In particular, this module does not compose the duplicated Reed–Muller code, prove a bit-error
radius, establish the Model-2 distribution, evaluate Equation (9), or justify the numerical
failure probabilities in Table 16.

## Main definitions

* `Cslib.Crypto.HQC.HQCReedSolomonInstance`: the three HQC v5.1 parameter sets.
* `Cslib.Crypto.HQC.hqcReedSolomonParameters`: the exact `(n1, k1, t1)` triples and source
  generator-coefficient arrays.
* `Cslib.Crypto.HQC.hqcRSAssemble`, `Cslib.Crypto.HQC.hqcRSMessagePart`: the parity-first,
  message-tail codeword layout.
* `Cslib.Crypto.HQC.hqcRSGenerator`, `Cslib.Crypto.HQC.hqcRSEncode`: the polynomial generator
  and systematic encoding semantics.
* `Cslib.Crypto.HQC.hqcRSSyndromes`, `Cslib.Crypto.HQC.hqcRSMessagePoint`,
  `Cslib.Crypto.HQC.hqcRSAuxiliary`, `Cslib.Crypto.HQC.hqcRSOddLocator`: the source decoder
  stages after the locator update.
* `Cslib.Crypto.HQC.hqcRSDecodeWithLocator`: the total message-only Chien/Forney decoder,
  parameterized by the missing locator stage.
* `Cslib.Crypto.HQC.HQCRSDecoderCorrects`: the exact bounded-symbol-error obligation for a
  completed encoder and decoder.

## References

* [HQC specification, version 5.1][HQC2026], §3.5.1–3.5.2, pp. 23–31.
-/

@[expose] public section

namespace Cslib.Crypto.HQC

open Finset Polynomial

/-- The three HQC v5.1 parameter sets. -/
inductive HQCReedSolomonInstance
  | hqc1
  | hqc3
  | hqc5
  deriving DecidableEq

/-- The shortened Reed–Solomon parameters and the corresponding reference generator array.
The array is stored from the constant coefficient to the monic leading coefficient. -/
structure HQCReedSolomonParameters where
  /-- The shortened code length `n1`, in bytes. -/
  length : ℕ
  /-- The message length `k1`, in bytes. -/
  messageLength : ℕ
  /-- The symbol-error correction capacity `t1`. -/
  capacity : ℕ
  /-- Shortening retains exactly `k1 + 2 * t1` coordinates. -/
  length_eq : length = messageLength + 2 * capacity
  /-- The coefficients of the source generator polynomial, constant term first. -/
  generatorCoefficients : List ℕ
  /-- The generator array has degree `2 * t1`. -/
  generatorCoefficients_length : generatorCoefficients.length = 2 * capacity + 1

/-- The exact shortened Reed–Solomon parameters and generator arrays in HQC v5.1 Table 6 and the
matching reference implementation. -/
def hqcReedSolomonParameters : HQCReedSolomonInstance → HQCReedSolomonParameters
  | .hqc1 =>
      { length := 46
        messageLength := 16
        capacity := 15
        length_eq := by decide
        generatorCoefficients :=
          [74, 81, 224, 114, 221, 115, 110, 88, 91, 151, 139, 151, 84, 184, 21, 242,
            97, 199, 87, 113, 104, 184, 197, 111, 89, 81, 156, 71, 128, 217, 1]
        generatorCoefficients_length := by decide }
  | .hqc3 =>
      { length := 56
        messageLength := 24
        capacity := 16
        length_eq := by decide
        generatorCoefficients :=
          [56, 180, 145, 30, 131, 105, 28, 60, 107, 33, 206, 184, 155, 249, 153, 231,
            112, 11, 231, 1, 144, 201, 71, 62, 8, 150, 142, 246, 33, 214, 26, 150, 1]
        generatorCoefficients_length := by decide }
  | .hqc5 =>
      { length := 90
        messageLength := 32
        capacity := 29
        length_eq := by decide
        generatorCoefficients :=
          [35, 203, 35, 52, 165, 121, 125, 73, 136, 42, 235, 82, 232, 122, 67, 98,
            51, 188, 230, 82, 164, 117, 103, 184, 209, 218, 244, 181, 122, 10, 25, 138,
            216, 182, 225, 145, 100, 244, 5, 142, 213, 238, 15, 150, 59, 28, 244, 222,
            252, 85, 125, 59, 52, 215, 180, 34, 173, 208, 1]
        generatorCoefficients_length := by decide }

/-- A shortened Reed–Solomon message: `k1` field symbols. -/
abbrev HQCRSMessage (p : HQCReedSolomonParameters) (F : Type*) := Fin p.messageLength → F

/-- A shortened Reed–Solomon word: `n1` field symbols. -/
abbrev HQCRSWord (p : HQCReedSolomonParameters) (F : Type*) := Fin p.length → F

/-- The `2 * t1` parity symbols at the beginning of a source codeword. -/
abbrev HQCRSParity (p : HQCReedSolomonParameters) (F : Type*) := Fin (2 * p.capacity) → F

/-- The embedding of a parity index into the initial `2 * t1` codeword coordinates. -/
def hqcRSParityIndex (p : HQCReedSolomonParameters) : Fin (2 * p.capacity) ↪ Fin p.length where
  toFun i := ⟨i, by rw [p.length_eq]; omega⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg Fin.val h

/-- The embedding of a message index into the final `k1` codeword coordinates. -/
def hqcRSMessageIndex (p : HQCReedSolomonParameters) : Fin p.messageLength ↪ Fin p.length where
  toFun i := ⟨2 * p.capacity + i, by rw [p.length_eq]; omega⟩
  inj' i j h := by
    apply Fin.ext
    have := congrArg Fin.val h
    omega

/-- Assemble the source layout: parity in the first `2 * t1` positions and the message in the
final `k1` positions. -/
def hqcRSAssemble {F : Type*} (p : HQCReedSolomonParameters)
    (parity : HQCRSParity p F) (message : HQCRSMessage p F) : HQCRSWord p F := fun i =>
  if h : (i : ℕ) < 2 * p.capacity then
    parity ⟨i, h⟩
  else
    message ⟨i - 2 * p.capacity, by
      have hi := i.isLt
      rw [p.length_eq] at hi
      omega⟩

/-- Read the final `k1` message positions of a source codeword. -/
def hqcRSMessagePart {F : Type*} (p : HQCReedSolomonParameters)
    (word : HQCRSWord p F) : HQCRSMessage p F :=
  fun i => word (hqcRSMessageIndex p i)

/-- The polynomial whose coefficient vector, from the constant term upward, is `message`. -/
noncomputable def hqcRSMessagePolynomial {F : Type*} [Semiring F]
    (p : HQCReedSolomonParameters) (message : HQCRSMessage p F) : F[X] :=
  ∑ i, C (message i) * X ^ (i : ℕ)

/-- The source generator `product_(i=1)^(2t1) (X + alpha^i)`.  The plus sign is the source's
characteristic-two form of the usual root factor. -/
noncomputable def hqcRSGenerator {F : Type*} [CommRing F] [CharP F 2]
    (p : HQCReedSolomonParameters) (alpha : F) : F[X] :=
  ∏ i : Fin (2 * p.capacity), (X + C (alpha ^ ((i : ℕ) + 1)))

/-- The parity polynomial: the remainder of the shifted message polynomial modulo the generator.
Its coefficients below `2 * t1` are the source parity bytes. -/
noncomputable def hqcRSParityPolynomial {F : Type*} [Field F] [CharP F 2]
    (p : HQCReedSolomonParameters) (alpha : F) (message : HQCRSMessage p F) : F[X] :=
  (X ^ (2 * p.capacity) * hqcRSMessagePolynomial p message) % hqcRSGenerator p alpha

/-- The source's systematic polynomial encoder, with parity bytes first and the message bytes
unchanged in the tail. -/
noncomputable def hqcRSEncode {F : Type*} [Field F] [CharP F 2]
    (p : HQCReedSolomonParameters) (alpha : F)
    (message : HQCRSMessage p F) : HQCRSWord p F :=
  hqcRSAssemble p (fun i => (hqcRSParityPolynomial p alpha message).coeff i) message

/-- The `2 * t1` source syndromes `r(alpha^(i+1))`, with codeword coordinates interpreted as
polynomial coefficients from the constant term upward. -/
noncomputable def hqcRSSyndromes {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (alpha : F) (received : HQCRSWord p F) : Fin (2 * p.capacity) → F := fun i =>
  ∑ j, received j * alpha ^ (((i : ℕ) + 1) * (j : ℕ))

/-- A syndrome coefficient, extended by zero outside the source array. -/
def hqcRSSyndromeCoeff {F : Type*} [Zero F] (p : HQCReedSolomonParameters)
    (syndromes : Fin (2 * p.capacity) → F) (i : ℕ) : F :=
  if h : i < 2 * p.capacity then syndromes ⟨i, h⟩ else 0

/-- The coefficient of the source auxiliary polynomial `Z`.  At index `i + 1` this is
`S_i + sum_(j < i) sigma_(j+1) S_(i-1-j) + sigma_(i+1)`; the constant coefficient is one. -/
noncomputable def hqcRSAuxiliaryCoeff {F : Type*} [Field F]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F)
    (locator : F[X]) (i : ℕ) : F :=
  if hzero : i = 0 then
    1
  else if hbound : i ≤ p.capacity then
    let sourceIndex := i - 1
    hqcRSSyndromeCoeff p syndromes sourceIndex +
      (∑ j ∈ range sourceIndex,
        locator.coeff (j + 1) * hqcRSSyndromeCoeff p syndromes (sourceIndex - 1 - j)) +
      locator.coeff i
  else
    0

/-- The source auxiliary polynomial `Z`, truncated to its `t1 + 1` stored coefficients. -/
noncomputable def hqcRSAuxiliary {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (syndromes : Fin (2 * p.capacity) → F) (locator : F[X]) : F[X] :=
  ∑ i ∈ range (p.capacity + 1), monomial i (hqcRSAuxiliaryCoeff p syndromes locator i)

/-- The source's `sigma_odd`: retain the odd-indexed locator coefficients at their original
indices.  In characteristic two this is `X` times the formal derivative. -/
noncomputable def hqcRSOddLocator {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (locator : F[X]) : F[X] :=
  ∑ i ∈ range (p.capacity + 1),
    if Odd i then monomial i (locator.coeff i) else 0

/-- The Chien/Forney evaluation point for message byte `i`.  If its codeword position is
`pos = 2 * t1 + i`, the source table stores powers of `beta = alpha^(-pos mod 255)`. -/
def hqcRSMessagePoint {F : Type*} [Monoid F] (p : HQCReedSolomonParameters)
    (alpha : F) (i : Fin p.messageLength) : F :=
  alpha ^ ((255 - ((2 * p.capacity + (i : ℕ)) % 255)) % 255)

/-- The missing source stage: compute the error-locator polynomial from the `2 * t1`
syndromes.  The concrete HQC implementation must instantiate this with the printed/reference
Berlekamp update. -/
abbrev HQCRSErrorLocatorStage (p : HQCReedSolomonParameters) (F : Type*) :=
  (Fin (2 * p.capacity) → F) → F[X]

/-- The source-shaped total decoder after supplying the error-locator stage.  Chien search and
correction are restricted to message positions.  A correction is applied exactly when the
locator vanishes and the odd-locator denominator is nonzero; all other bytes are copied from the
received message tail. -/
noncomputable def hqcRSDecodeWithLocator {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) (alpha : F) (errorLocator : HQCRSErrorLocatorStage p F)
    (received : HQCRSWord p F) : HQCRSMessage p F :=
  let syndromes := hqcRSSyndromes p alpha received
  let locator := errorLocator syndromes
  let auxiliary := hqcRSAuxiliary p syndromes locator
  let oddLocator := hqcRSOddLocator p locator
  fun i =>
    let beta := hqcRSMessagePoint p alpha i
    if locator.eval beta = 0 ∧ oddLocator.eval beta ≠ 0 then
      hqcRSMessagePart p received i + auxiliary.eval beta / oddLocator.eval beta
    else
      hqcRSMessagePart p received i

/-- The exact symbol-error obligation for a completed shortened Reed–Solomon codec: errors may
occur in any mixture of parity and message positions. -/
def HQCRSDecoderCorrects {F : Type*} [Field F] [DecidableEq F]
    (p : HQCReedSolomonParameters) (encode : HQCRSMessage p F → HQCRSWord p F)
    (decode : HQCRSWord p F → HQCRSMessage p F) : Prop :=
  ∀ message error, hammingNorm error ≤ p.capacity → decode (encode message + error) = message

end Cslib.Crypto.HQC
