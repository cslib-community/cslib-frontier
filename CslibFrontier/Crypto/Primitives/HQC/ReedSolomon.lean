/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.ByteField
public import CslibFrontier.Foundations.Data.Code.Concatenation
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
`HQCRSErrorLocator` is the source's fixed `t1 + 1` coefficient array, so the Chien test and both
Forney inputs see the same capped polynomial.  `hqcRSBerlekampLocator` gives the mathematical
state transition of the reference's constant-time Berlekamp update, and `hqcRSDecode` composes it
with the remaining total best-effort decoder.  This functional model does not itself claim a
constant-time machine implementation.

The source coefficient arrays below are from the `RS_POLY_COEFS` macros in the HQC v5.1.0
reference implementation, tag commit `06567ccbad10580d78dd7863b15d23f41076d57f`.  Coefficients
and codeword coordinates are listed from constant term upward.  The implementation uses the
modulus byte `0x11b` and primitive-element byte `0x03`; `HQCByte` and `hqcAlpha` give that exact
polynomial-basis representation.  The LFSR encoder below is the source loop, while
`HQCRSGeneratorMatchesSource` and `HQCRSLFSRMatchesPolynomial` state the outstanding equivalence
obligations.  Proving the order of `hqcAlpha`, these equivalences, and the decoder's bounded-error
behavior remains required before this is a complete source codec.

The final definitions expose the deterministic seam used by an HQC decoding-failure reduction:
an arbitrary inner decoder first produces one byte per outer coordinate, and outer failure is
exactly the event that more than `t1` of those bytes disagree with the source RS codeword.  This
module does not identify that inner decoder with the duplicated Reed–Muller implementation, prove
a bit-error radius, establish the Model-2 distribution, evaluate Equation (9), or justify the
numerical failure probabilities in Table 16.

## Main definitions

* `Cslib.Crypto.HQC.HQCReedSolomonInstance`: the three HQC v5.1 parameter sets.
* `Cslib.Crypto.HQC.hqcReedSolomonParameters`: the exact `(n1, k1, t1)` triples and source
  generator-coefficient arrays.
* `Cslib.Crypto.HQC.hqcRSAssemble`, `Cslib.Crypto.HQC.hqcRSMessagePart`: the parity-first,
  message-tail codeword layout.
* `Cslib.Crypto.HQC.hqcRSGenerator`, `Cslib.Crypto.HQC.hqcRSEncode`: the polynomial generator
  and systematic encoding semantics.
* `Cslib.Crypto.HQC.hqcRSSourceGenerator`, `Cslib.Crypto.HQC.hqcRSLFSREncode`: the pinned source
  coefficient array and reverse-message LFSR implementation.
* `Cslib.Crypto.HQC.hqcRSSyndromes`, `Cslib.Crypto.HQC.hqcRSMessagePoint`,
  `Cslib.Crypto.HQC.hqcRSAuxiliary`, `Cslib.Crypto.HQC.hqcRSOddLocator`: the source decoder
  stages after the locator update.
* `Cslib.Crypto.HQC.HQCRSErrorLocator`, `Cslib.Crypto.HQC.hqcRSBerlekampLocator`: the fixed-size
  locator representation and the reference Berlekamp state transition.
* `Cslib.Crypto.HQC.hqcRSDecodeWithLocator`: the total message-only Chien/Forney decoder,
  parameterized by a locator stage.
* `Cslib.Crypto.HQC.hqcRSDecode`: the complete source-shaped best-effort decoder.
* `Cslib.Crypto.HQC.HQCRSDecoderCorrects`: the exact bounded-symbol-error obligation for a
  completed encoder and decoder.
* `Cslib.Crypto.HQC.hqcRSSourceCode`, `Cslib.Crypto.HQC.HQCRSHasSourceDistance`,
  `Cslib.Crypto.HQC.HQCReedSolomonCorrects`: the concrete source code and its outstanding exact
  distance and mixed-error correction obligations.
* `Cslib.Crypto.HQC.hqcRSConcatenatedEncode`,
  `Cslib.Crypto.HQC.hqcRSConcatenatedDecode`, `Cslib.Crypto.HQC.hqcRSOuterFailure`: the generic
  inner-code composition and deterministic outer-failure seam.

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

/-- The source generator coefficient at index `i`, interpreted in the exact byte field.  Indices
outside the stored array are zero. -/
noncomputable def hqcRSSourceGeneratorCoeff (p : HQCReedSolomonParameters) (i : ℕ) : HQCByte :=
  hqcByteOfNat (p.generatorCoefficients.getD i 0)

/-- The generator polynomial transcribed from the parameter set's `RS_POLY_COEFS` array. -/
noncomputable def hqcRSSourceGenerator (p : HQCReedSolomonParameters) : HQCByte[X] :=
  ∑ i ∈ range (2 * p.capacity + 1), monomial i (hqcRSSourceGeneratorCoeff p i)

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

/-- A parity-register coefficient, extended by zero outside the `2 * t1` stages. -/
def hqcRSParityCoeff {F : Type*} [Zero F] (p : HQCReedSolomonParameters)
    (parity : HQCRSParity p F) (i : ℕ) : F :=
  if h : i < 2 * p.capacity then parity ⟨i, h⟩ else 0

/-- One source LFSR step.  The gate is the next message byte plus the last parity stage;
coefficient zero receives only the feedback product, while every later stage also shifts its
predecessor. -/
noncomputable def hqcRSLFSRStep (p : HQCReedSolomonParameters)
    (parity : HQCRSParity p HQCByte) (input : HQCByte) : HQCRSParity p HQCByte :=
  let gate := input + hqcRSParityCoeff p parity (2 * p.capacity - 1)
  fun i =>
    if (i : ℕ) = 0 then
      gate * hqcRSSourceGeneratorCoeff p 0
    else
      hqcRSParityCoeff p parity ((i : ℕ) - 1) +
        gate * hqcRSSourceGeneratorCoeff p i

/-- The source encoder's parity register after processing message bytes from the last byte to the
first byte. -/
noncomputable def hqcRSLFSRParity (p : HQCReedSolomonParameters)
    (message : HQCRSMessage p HQCByte) : HQCRSParity p HQCByte :=
  (List.ofFn message).reverse.foldl (hqcRSLFSRStep p) 0

/-- The reference `reed_solomon_encode`: reverse-message LFSR parity followed by the unchanged
message bytes. -/
noncomputable def hqcRSLFSREncode (p : HQCReedSolomonParameters)
    (message : HQCRSMessage p HQCByte) : HQCRSWord p HQCByte :=
  hqcRSAssemble p (hqcRSLFSRParity p message) message

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

/-- The source coefficient array agrees with the root-product generator.  This is an explicit
outstanding proof obligation for each HQC parameter set. -/
def HQCRSGeneratorMatchesSource (p : HQCReedSolomonParameters) : Prop :=
  hqcRSGenerator p hqcAlpha = hqcRSSourceGenerator p

/-- The reference LFSR encoder agrees with the polynomial-remainder encoder.  This is an explicit
outstanding proof obligation, not an assumption of either definition. -/
def HQCRSLFSRMatchesPolynomial (p : HQCReedSolomonParameters) : Prop :=
  hqcRSLFSREncode p = hqcRSEncode p hqcAlpha

/-- The `2 * t1` source syndromes `r(alpha^(i+1))`, with codeword coordinates interpreted as
polynomial coefficients from the constant term upward. -/
noncomputable def hqcRSSyndromes {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (alpha : F) (received : HQCRSWord p F) : Fin (2 * p.capacity) → F := fun i =>
  ∑ j, received j * alpha ^ (((i : ℕ) + 1) * (j : ℕ))

/-- A syndrome coefficient, extended by zero outside the source array. -/
def hqcRSSyndromeCoeff {F : Type*} [Zero F] (p : HQCReedSolomonParameters)
    (syndromes : Fin (2 * p.capacity) → F) (i : ℕ) : F :=
  if h : i < 2 * p.capacity then syndromes ⟨i, h⟩ else 0

/-- The source error-locator array, containing exactly the coefficients of degrees
`0, ..., t1`.  Using this type prevents a coefficient invisible to the source evaluator from
affecting the Chien root test. -/
abbrev HQCRSErrorLocator (p : HQCReedSolomonParameters) (F : Type*) :=
  Fin (p.capacity + 1) → F

/-- A locator coefficient, extended by zero outside the source array. -/
def hqcRSLocatorCoeff {F : Type*} [Zero F] (p : HQCReedSolomonParameters)
    (locator : HQCRSErrorLocator p F) (i : ℕ) : F :=
  if h : i < p.capacity + 1 then locator ⟨i, h⟩ else 0

/-- The degree-at-most-`t1` polynomial represented by the source locator array. -/
noncomputable def hqcRSLocatorPolynomial {F : Type*} [Semiring F]
    (p : HQCReedSolomonParameters) (locator : HQCRSErrorLocator p F) : F[X] :=
  ((degreeLTEquiv F (p.capacity + 1)).symm locator : degreeLT F (p.capacity + 1))

/-- A locator reconstructed from the source array has no coefficient above `t1`. -/
theorem hqcRSLocatorPolynomial_coeff_eq_zero {F : Type*} [Semiring F]
    (p : HQCReedSolomonParameters) (locator : HQCRSErrorLocator p F) {i : ℕ}
    (hi : p.capacity < i) : (hqcRSLocatorPolynomial p locator).coeff i = 0 := by
  apply coeff_eq_zero_of_degree_lt
  exact (mem_degreeLT.mp
    (((degreeLTEquiv F (p.capacity + 1)).symm locator).property)).trans_le
      (by exact_mod_cast (Nat.succ_le_iff.mpr hi))

/-- Evaluation of the bounded locator reads exactly the `t1 + 1` source coefficients. -/
theorem hqcRSLocatorPolynomial_eval {F : Type*} [Semiring F]
    (p : HQCReedSolomonParameters) (locator : HQCRSErrorLocator p F) (x : F) :
    (hqcRSLocatorPolynomial p locator).eval x =
      ∑ i, locator i * x ^ (i : ℕ) := by
  simpa only [hqcRSLocatorPolynomial, LinearEquiv.apply_symm_apply] using
    eval_eq_sum_degreeLTEquiv
      (((degreeLTEquiv F (p.capacity + 1)).symm locator).property) x

/-- The coefficient of the source auxiliary polynomial `Z`.  At index `i + 1` this is
`S_i + sum_(j < i) sigma_(j+1) S_(i-1-j) + sigma_(i+1)`; the constant coefficient is one. -/
noncomputable def hqcRSAuxiliaryCoeff {F : Type*} [Field F]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F)
    (locator : HQCRSErrorLocator p F) (i : ℕ) : F :=
  if hzero : i = 0 then
    1
  else if hbound : i ≤ p.capacity then
    let sourceIndex := i - 1
    hqcRSSyndromeCoeff p syndromes sourceIndex +
      (∑ j ∈ range sourceIndex,
        hqcRSLocatorCoeff p locator (j + 1) *
          hqcRSSyndromeCoeff p syndromes (sourceIndex - 1 - j)) +
      hqcRSLocatorCoeff p locator i
  else
    0

/-- The source auxiliary polynomial `Z`, truncated to its `t1 + 1` stored coefficients. -/
noncomputable def hqcRSAuxiliary {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (syndromes : Fin (2 * p.capacity) → F) (locator : HQCRSErrorLocator p F) : F[X] :=
  ∑ i ∈ range (p.capacity + 1), monomial i (hqcRSAuxiliaryCoeff p syndromes locator i)

/-- The source's `sigma_odd`: retain the odd-indexed locator coefficients at their original
indices.  In characteristic two this is `X` times the formal derivative. -/
noncomputable def hqcRSOddLocator {F : Type*} [Field F] (p : HQCReedSolomonParameters)
    (locator : HQCRSErrorLocator p F) : F[X] :=
  ∑ i ∈ range (p.capacity + 1),
    if Odd i then monomial i (hqcRSLocatorCoeff p locator i) else 0

/-- The Chien/Forney evaluation point for message byte `i`.  If its codeword position is
`pos = 2 * t1 + i`, the source table stores powers of `beta = alpha^(-pos mod 255)`. -/
def hqcRSMessagePoint {F : Type*} [Monoid F] (p : HQCReedSolomonParameters)
    (alpha : F) (i : Fin p.messageLength) : F :=
  alpha ^ ((255 - ((2 * p.capacity + (i : ℕ)) % 255)) % 255)

/-- The source message-only Chien flags: byte `i` is marked exactly when the bounded locator
vanishes at `alpha^(-(2 * t1 + i))`. -/
noncomputable def hqcRSErrorPositions {F : Type*} [Field F] [DecidableEq F]
    (p : HQCReedSolomonParameters) (alpha : F) (locator : HQCRSErrorLocator p F) :
    Fin p.messageLength → Bool := fun i =>
  decide ((hqcRSLocatorPolynomial p locator).eval (hqcRSMessagePoint p alpha i) = 0)

/-- A source locator stage computes the fixed `t1 + 1` coefficient array from the `2 * t1`
syndromes. -/
abbrev HQCRSErrorLocatorStage (p : HQCReedSolomonParameters) (F : Type*) :=
  (Fin (2 * p.capacity) → F) → HQCRSErrorLocator p F

/-- The mathematical state of the reference Berlekamp update.  `rhoLocator` represents the
source array `x_sigma_rho`; `rhoIndex = -1` in the initial state records the source's unsigned
sentinel without relying on machine-word wraparound. -/
structure HQCRSBerlekampState (p : HQCReedSolomonParameters) (F : Type*) where
  /-- The current locator coefficient array `sigma`. -/
  locator : HQCRSErrorLocator p F
  /-- The tracked degree of `sigma`. -/
  locatorDegree : ℕ
  /-- The shifted comparison locator `x_sigma_rho`. -/
  rhoLocator : HQCRSErrorLocator p F
  /-- The tracked degree before the shift represented by `rhoLocator`. -/
  rhoLocatorDegree : ℕ
  /-- The index `rho` of the last promoted discrepancy, initially `-1`. -/
  rhoIndex : ℤ
  /-- The last promoted nonzero discrepancy `d_rho`. -/
  rhoDiscrepancy : F
  /-- The current discrepancy `d_mu`. -/
  discrepancy : F

/-- The source Berlekamp initial state: `sigma = 1`, `x_sigma_rho = X`, `rho = -1`,
`d_rho = 1`, and `d_mu = S_0`. -/
noncomputable def hqcRSBerlekampInitial {F : Type*} [Field F] [CharP F 2]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F) :
    HQCRSBerlekampState p F where
  locator := fun i => if (i : ℕ) = 0 then 1 else 0
  locatorDegree := 0
  rhoLocator := fun i => if (i : ℕ) = 1 then 1 else 0
  rhoLocatorDegree := 0
  rhoIndex := -1
  rhoDiscrepancy := 1
  discrepancy := hqcRSSyndromeCoeff p syndromes 0

/-- The discrepancy following iteration `mu`, computed with the updated locator just as in the
reference loop. -/
noncomputable def hqcRSBerlekampNextDiscrepancy {F : Type*} [Field F] [CharP F 2]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F)
    (locator : HQCRSErrorLocator p F) (mu : ℕ) : F :=
  hqcRSSyndromeCoeff p syndromes (mu + 1) +
    ∑ i ∈ range (p.capacity + 1),
      if 0 < i ∧ i ≤ mu + 1 then
        hqcRSLocatorCoeff p locator i * hqcRSSyndromeCoeff p syndromes (mu + 1 - i)
      else
        0

/-- One mathematical iteration of the reference's masked Berlekamp update.  The branch on
`promote` specifies the value selected by the C masks; this definition makes no timing claim. -/
noncomputable def hqcRSBerlekampStep {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F) (mu : ℕ)
    (state : HQCRSBerlekampState p F) : HQCRSBerlekampState p F :=
  let quotient := state.discrepancy / state.rhoDiscrepancy
  let locator : HQCRSErrorLocator p F := fun i =>
    if 0 < (i : ℕ) ∧ (i : ℕ) ≤ mu + 1 then
      state.locator i + quotient * state.rhoLocator i
    else
      state.locator i
  let shiftedDegree := (Int.ofNat mu - state.rhoIndex).toNat + state.rhoLocatorDegree
  let promote := state.discrepancy ≠ 0 ∧ state.locatorDegree < shiftedDegree
  let rhoLocator : HQCRSErrorLocator p F := fun i =>
    if 0 < (i : ℕ) then
      if promote then
        hqcRSLocatorCoeff p state.locator ((i : ℕ) - 1)
      else
        hqcRSLocatorCoeff p state.rhoLocator ((i : ℕ) - 1)
    else
      0
  { locator := locator
    locatorDegree := if promote then shiftedDegree else state.locatorDegree
    rhoLocator := rhoLocator
    rhoLocatorDegree := if promote then state.locatorDegree else state.rhoLocatorDegree
    rhoIndex := if promote then mu else state.rhoIndex
    rhoDiscrepancy := if promote then state.discrepancy else state.rhoDiscrepancy
    discrepancy :=
      if mu + 1 < 2 * p.capacity then
        hqcRSBerlekampNextDiscrepancy p syndromes locator mu
      else
        state.discrepancy }

/-- The reference Berlekamp state after `steps` iterations. -/
noncomputable def hqcRSBerlekampStateAfter {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) (syndromes : Fin (2 * p.capacity) → F) :
    ℕ → HQCRSBerlekampState p F
  | 0 => hqcRSBerlekampInitial p syndromes
  | steps + 1 =>
      hqcRSBerlekampStep p syndromes steps (hqcRSBerlekampStateAfter p syndromes steps)

/-- The source error-locator array after all `2 * t1` Berlekamp iterations. -/
noncomputable def hqcRSBerlekampLocator {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) : HQCRSErrorLocatorStage p F := fun syndromes =>
  (hqcRSBerlekampStateAfter p syndromes (2 * p.capacity)).locator

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
    if hqcRSErrorPositions p alpha locator i = true ∧ oddLocator.eval beta ≠ 0 then
      hqcRSMessagePart p received i + auxiliary.eval beta / oddLocator.eval beta
    else
      hqcRSMessagePart p received i

/-- The complete source-shaped total best-effort decoder, using the reference Berlekamp update
followed by message-only Chien search and denominator-guarded Forney correction. -/
noncomputable def hqcRSDecode {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
    (p : HQCReedSolomonParameters) (alpha : F)
    (received : HQCRSWord p F) : HQCRSMessage p F :=
  hqcRSDecodeWithLocator p alpha (hqcRSBerlekampLocator p) received

/-- The exact symbol-error obligation for a completed shortened Reed–Solomon codec: errors may
occur in any mixture of parity and message positions. -/
def HQCRSDecoderCorrects {F : Type*} [Field F] [DecidableEq F]
    (p : HQCReedSolomonParameters) (encode : HQCRSMessage p F → HQCRSWord p F)
    (decode : HQCRSWord p F → HQCRSMessage p F) : Prop :=
  ∀ message error, hammingNorm error ≤ p.capacity → decode (encode message + error) = message

/-- The concrete shortened source code: the range of the pinned reverse-message LFSR encoder. -/
noncomputable def hqcRSSourceCode (p : HQCReedSolomonParameters) :
    Set (HQCRSWord p HQCByte) :=
  Set.range (hqcRSLFSREncode p)

/-- The outstanding exact-distance obligation for the shortened source code.  Its expected
minimum distance is `2 * t1 + 1`, including after shortening. -/
def HQCRSHasSourceDistance (p : HQCReedSolomonParameters) : Prop :=
  Cslib.Code.minDist (hqcRSSourceCode p) = (2 * p.capacity + 1 : ℕ)

/-- The outstanding concrete decoder theorem: the pinned source encoder and total decoder recover
the message from every mixture of at most `t1` parity- and message-symbol errors. -/
def HQCReedSolomonCorrects (p : HQCReedSolomonParameters) : Prop :=
  HQCRSDecoderCorrects p (hqcRSLFSREncode p) (hqcRSDecode p hqcAlpha)

/-- Decode each inner block to obtain the byte word presented to the outer RS decoder. -/
def hqcRSInnerDecodedWord {K B : Type*} (p : HQCReedSolomonParameters)
    (innerDecode : (K → B) → HQCByte) (received : Fin p.length × K → B) :
    HQCRSWord p HQCByte :=
  fun i => innerDecode fun j => received (i, j)

/-- Encode with the source shortened RS layer and then an arbitrary inner byte encoder. -/
noncomputable def hqcRSConcatenatedEncode {K B : Type*} (p : HQCReedSolomonParameters)
    (innerEncode : HQCByte → K → B) (message : HQCRSMessage p HQCByte) :
    Fin p.length × K → B :=
  Cslib.Code.concat innerEncode (hqcRSLFSREncode p message)

/-- Decode every inner block and pass the resulting byte word to the source RS decoder. -/
noncomputable def hqcRSConcatenatedDecode {K B : Type*} (p : HQCReedSolomonParameters)
    (innerDecode : (K → B) → HQCByte) (received : Fin p.length × K → B) :
    HQCRSMessage p HQCByte :=
  hqcRSDecode p hqcAlpha (hqcRSInnerDecodedWord p innerDecode received)

/-- The outer-symbol error induced by an arbitrary received inner-code word. -/
noncomputable def hqcRSSymbolError {K B : Type*} (p : HQCReedSolomonParameters)
    (innerDecode : (K → B) → HQCByte) (received : Fin p.length × K → B)
    (message : HQCRSMessage p HQCByte) : HQCRSWord p HQCByte :=
  hqcRSInnerDecodedWord p innerDecode received - hqcRSLFSREncode p message

/-- The deterministic outer-failure event: more than `t1` inner blocks decode to the wrong byte.
No probability model or inner-code radius is built into this predicate. -/
noncomputable def hqcRSOuterFailure {K B : Type*} (p : HQCReedSolomonParameters)
    (innerDecode : (K → B) → HQCByte) (received : Fin p.length × K → B)
    (message : HQCRSMessage p HQCByte) : Prop :=
  p.capacity < hammingNorm (hqcRSSymbolError p innerDecode received message)

/-- Conditional deterministic composition: the concrete outer correctness theorem reduces
successful concatenated decoding to at most `t1` incorrectly decoded inner blocks. -/
theorem hqcRSConcatenatedDecode_eq_of_symbolWeight_le {K B : Type*}
    (p : HQCReedSolomonParameters) (innerDecode : (K → B) → HQCByte)
    (received : Fin p.length × K → B) (message : HQCRSMessage p HQCByte)
    (hcorrect : HQCReedSolomonCorrects p)
    (hweight : hammingNorm (hqcRSSymbolError p innerDecode received message) ≤ p.capacity) :
    hqcRSConcatenatedDecode p innerDecode received = message := by
  have hword :
      hqcRSLFSREncode p message + hqcRSSymbolError p innerDecode received message =
        hqcRSInnerDecodedWord p innerDecode received := by
    funext i
    simp only [hqcRSSymbolError, Pi.add_apply, Pi.sub_apply]
    abel
  rw [hqcRSConcatenatedDecode, ← hword]
  exact hcorrect message (hqcRSSymbolError p innerDecode received message) hweight

/-- Conditional deterministic failure reduction: if concatenated decoding fails, more than
`t1` inner blocks decoded to the wrong byte. -/
theorem hqcRSOuterFailure_of_decode_ne {K B : Type*} (p : HQCReedSolomonParameters)
    (innerDecode : (K → B) → HQCByte) (received : Fin p.length × K → B)
    (message : HQCRSMessage p HQCByte) (hcorrect : HQCReedSolomonCorrects p)
    (hfail : hqcRSConcatenatedDecode p innerDecode received ≠ message) :
    hqcRSOuterFailure p innerDecode received message := by
  by_contra hweight
  apply hfail
  apply hqcRSConcatenatedDecode_eq_of_symbolWeight_le p innerDecode received message hcorrect
  rw [hqcRSOuterFailure] at hweight
  omega

end Cslib.Crypto.HQC
