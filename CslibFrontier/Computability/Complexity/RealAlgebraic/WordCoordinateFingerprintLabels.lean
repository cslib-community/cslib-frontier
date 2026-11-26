/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CoordinateFingerprintWitness
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCoefficientSign
public import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoordinateLift
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Indexed coordinate equations and fingerprint labels

Each binary address selects a coordinate characteristic polynomial and a fingerprint from
the shared word. The controlled univariate family evaluates the resulting integer labels
at level `a + 20` from a controlled source at level `a`.
The lifted family reads these labels in the original coordinate space at the same level.
The matching equations evaluate the leading deformation coefficients in that space at
level `a + 18` and depend only on the instance and coordinate address.

Adapted from `ControlledIndexedLabels` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The leading deformation coefficient
is selected over the integers. The witness supplies only the fingerprint parameters.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

private theorem addressedCoordinate_polyTime {α : Type} {n : α → ℕ} {enc : α ↪ List Bool}
    (harity : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun q : α × ℕ => q.2 % n q.1) (encPair enc encNat) encNat :=
  binary_mod' (snd enc encNat) ((unary_to_binary.comp harity).comp (fst enc encNat))

/-- Label the roots of the leading deformation coefficient at coordinate `j % n`, using
the fingerprint at address `j` of the shared word. No range condition on `j` is needed. -/
@[expose] noncomputable def wordCoordinateFingerprintLabel {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (mass : ℕ)
    (hn : 0 < n) (word : List Bool) (j : ℕ) : Polynomial ℤ :=
  let i : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩
  let P := parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i
  let D := (d + 1) ^ n
  let b := parametricCoordinateCoeffNormExponent n (d + 1) mass
  let f := decodeCoordinateFingerprint D word j
  Polynomial.fingerprintIntegerRootLabel (Polynomial.Bivariate.swap P).leadingCoeff 1 D b
    f.modulus f.parameter f.target

/-- A polynomial-time witness word supplies one controlled univariate label per binary address
at level `a + 20`. Positive arity allows every address to select a coordinate. -/
noncomputable def Controlled.wordCoordinateFingerprintLabels {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
      (wordCoordinateFingerprintLabel (F q.1) (hF q.1) (C.massExponent q.1)
        (hn q.1) (word q.1) q.2)) (encPair enc encNat) (a + 20) := by
  have hw := fst enc encNat
  have hj := snd enc encNat
  let CQ := C.preprocess (fun q : α × ℕ => q.1) hw
  have hD := (binary_pow' (binary_add' hd (.const 1)) C.arity_computable).comp hw
  have hwords := hword.comp hw
  let f (q : α × ℕ) := decodeCoordinateFingerprint ((d q.1 + 1) ^ n q.1) (word q.1) q.2
  have hb (q : α × ℕ) : (f q).Bounded ((d q.1 + 1) ^ n q.1) :=
    decodeCoordinateFingerprint_bounded _ _ _
  exact CQ.criticalCoordinateFingerprintLabels (Decoder.pair E Decoder.nat)
    (fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩) (fun q => hdpos q.1) (fun q => hF q.1)
    (hd.comp hw) (addressedCoordinate_polyTime C.arity_computable)
    (decodeCoordinateFingerprint_modulus_polyTime hD hj hwords)
    (decodeCoordinateFingerprint_parameter_polyTime hD hj hwords)
    (decodeCoordinateFingerprint_target_polyTime hD hj hwords)
    (fun q => (by decide : 0 < 2).trans (hb q).1)
    (CoordinateFingerprint.modulusBound_polyTime hD)
    (fun q => by
      obtain ⟨_, hcap, _, _⟩ := hb q
      exact hcap) (fun q => by
      obtain ⟨_, _, _, ht⟩ := hb q
      exact ht)

/-- The fingerprint label at a binary address, placed in the addressed coordinate
of the original variable space. -/
noncomputable def wordCoordinateFingerprintTest {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (mass : ℕ)
    (hn : 0 < n) (word : List Bool) (j : ℕ) : MvPolynomial (Fin n) ℤ :=
  MvPolynomial.rename (fun _ : Fin 1 => (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n))
    ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
      (wordCoordinateFingerprintLabel F hF mass hn word j))

/-- The lifted label evaluates at the addressed coordinate. -/
theorem eval₂_wordCoordinateFingerprintTest {n d : ℕ} {R : Type*} [CommSemiring R]
    (f : ℤ →+* R) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (mass : ℕ) (hn : 0 < n) (word : List Bool) (x : Fin n → R) (j : ℕ) :
    MvPolynomial.eval₂ f x (wordCoordinateFingerprintTest F hF mass hn word j) =
      (wordCoordinateFingerprintLabel F hF mass hn word j).eval₂ f
        (x ⟨j % n, Nat.mod_lt _ hn⟩) := by
  simp only [wordCoordinateFingerprintTest, MvPolynomial.eval₂_rename,
    MvPolynomial.eval₂_uniqueAlgEquiv_symm, Function.comp_apply]

/-- Evaluate the word-indexed label at its selected coordinate in the original variable space.
The binary address is reduced modulo the positive source arity to select that coordinate. -/
noncomputable def Controlled.wordCoordinateFingerprintTests {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ =>
      wordCoordinateFingerprintTest (F q.1) (hF q.1) (C.massExponent q.1) (hn q.1) (word q.1) q.2)
      (encPair enc encNat) (a + 20) :=
  (C.wordCoordinateFingerprintLabels E hn hdpos hF hd word hword).onCoordinate
    (C.arity_computable.comp (fst enc encNat)) (fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩)
    (addressedCoordinate_polyTime C.arity_computable)

/-- The fingerprint rows share the degree bound, norm exponent and prime cutoff at row zero.
The modulus cap depends only on the instance, even when different addresses decode different
actual moduli from the shared word. -/
theorem Controlled.wordCoordinateFingerprintTests_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) (w : α) (j : ℕ) :
    let labels := C.wordCoordinateFingerprintTests E hn hdpos hF hd word hword
    labels.degreeBound (w, j) = labels.degreeBound (w, 0) ∧
      labels.massExponent (w, j) = labels.massExponent (w, 0) ∧
      labels.cutoff (w, j) = labels.cutoff (w, 0) := by
  simp only [wordCoordinateFingerprintTests, degreeBound_onCoordinate, massExponent_onCoordinate,
    cutoff_onCoordinate]
  simp only [wordCoordinateFingerprintLabels]
  apply Controlled.criticalCoordinateFingerprintLabels_bounds_eq <;> rfl

/-- Place the leading deformation coefficient at the variable selected by a binary address. -/
noncomputable def indexedCoordinateEquation {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) (j : ℕ) :
    MvPolynomial (Fin n) ℤ :=
  let i : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩
  MvPolynomial.rename (fun _ : Fin 1 => i) ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
    (Polynomial.Bivariate.swap
      (parametricCoordinatePolynomial (Nat.succ_pos d) F hF i)).leadingCoeff)

/-- The equation evaluates the leading deformation coefficient at the addressed coordinate. -/
theorem eval₂_indexedCoordinateEquation {n d : ℕ} {R : Type*} [CommSemiring R]
    (f : ℤ →+* R) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hn : 0 < n) (x : Fin n → R) (j : ℕ) :
    let i : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩
    MvPolynomial.eval₂ f x (indexedCoordinateEquation F hF hn j) =
      (Polynomial.Bivariate.swap
        (parametricCoordinatePolynomial (Nat.succ_pos d) F hF i)).leadingCoeff.eval₂ f (x i) := by
  simp only [indexedCoordinateEquation, MvPolynomial.eval₂_rename,
    MvPolynomial.eval₂_uniqueAlgEquiv_symm, Function.comp_apply]

/-- The coordinate root grid uses the zeros of the integer leading deformation coefficients.
This controlled family places each equation at the coordinate selected by its binary address.
Its evaluator uses counting level `a + 18` and needs no fingerprint word. -/
noncomputable def Controlled.indexedCoordinateEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat) :
    Controlled (fun q : α × ℕ => indexedCoordinateEquation (F q.1) (hF q.1) (hn q.1) q.2)
      (encPair enc encNat) (a + 18) := by
  let i (q : α × ℕ) : Fin (n q.1) := ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩
  have hw := fst enc encNat
  have hi := addressedCoordinate_polyTime C.arity_computable
  let CQ := C.preprocess (fun q : α × ℕ => q.1) hw
  exact (CQ.criticalCoordinateEquations (Decoder.pair E Decoder.nat) i
    (fun q => hdpos q.1) (fun q => hF q.1) (hd.comp hw) hi).onCoordinate
      (C.arity_computable.comp hw) i hi

/-- The indexed coordinate equations share bounds across all addresses of the same input. -/
theorem Controlled.indexedCoordinateEquations_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (w : α) (j : ℕ) :
    let equations := C.indexedCoordinateEquations E hn hdpos hF hd
    equations.degreeBound (w, j) = equations.degreeBound (w, 0) ∧
      equations.massExponent (w, j) = equations.massExponent (w, 0) ∧
      equations.cutoff (w, j) = equations.cutoff (w, 0) := by
  let i (q : α × ℕ) : Fin (n q.1) := ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩
  have hw := fst enc encNat
  have hi := addressedCoordinate_polyTime C.arity_computable
  let CQ := C.preprocess (fun q : α × ℕ => q.1) hw
  simpa only [indexedCoordinateEquations, degreeBound_onCoordinate, massExponent_onCoordinate,
    cutoff_onCoordinate, CQ, i] using CQ.criticalCoordinateEquations_bounds_eq
      (Decoder.pair E Decoder.nat) i (fun q => hdpos q.1) (fun q => hF q.1) (hd.comp hw) hi
      (w, j) (w, 0) rfl rfl rfl rfl

end Cslib.Complexity.RealAlgebraic
