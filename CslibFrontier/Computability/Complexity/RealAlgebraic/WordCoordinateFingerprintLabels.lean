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
    (fun q => (by decide : 0 < 2).trans (hb q).1) (fun q => by
      obtain ⟨_, _, _, ht⟩ := hb q
      exact ht)

/-- Evaluate the word-indexed label at its selected coordinate in the original variable space.
The binary address is reduced modulo the positive source arity to select that coordinate. -/
noncomputable def Controlled.wordCoordinateFingerprintTests {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ =>
      MvPolynomial.rename (fun _ : Fin 1 => (⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩ : Fin (n q.1)))
        ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
          (wordCoordinateFingerprintLabel (F q.1) (hF q.1) (C.massExponent q.1)
            (hn q.1) (word q.1) q.2))) (encPair enc encNat) (a + 20) :=
  (C.wordCoordinateFingerprintLabels E hn hdpos hF hd word hword).onCoordinate
    (C.arity_computable.comp (fst enc encNat)) (fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩)
    (addressedCoordinate_polyTime C.arity_computable)

/-- The coordinate root grid uses the zeros of the integer leading deformation coefficients.
This controlled family places each equation at the coordinate selected by its binary address.
Its evaluator uses counting level `a + 18` and needs no fingerprint word. -/
noncomputable def Controlled.indexedCoordinateEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat) :
    let i (q : α × ℕ) : Fin (n q.1) := ⟨q.2 % n q.1, Nat.mod_lt _ (hn q.1)⟩
    Controlled (fun q : α × ℕ => MvPolynomial.rename (fun _ : Fin 1 => i q)
      ((MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).symm
        (Polynomial.Bivariate.swap (parametricCoordinatePolynomial
          (Nat.succ_pos (d q.1)) (F q.1) (hF q.1) (i q))).leadingCoeff))
      (encPair enc encNat) (a + 18) := by
  intro i
  have hw := fst enc encNat
  have hi := addressedCoordinate_polyTime C.arity_computable
  let CQ := C.preprocess (fun q : α × ℕ => q.1) hw
  exact (CQ.criticalCoordinateEquations (Decoder.pair E Decoder.nat) i
    (fun q => hdpos q.1) (fun q => hF q.1) (hd.comp hw) hi).onCoordinate
      (C.arity_computable.comp hw) i hi

end Cslib.Complexity.RealAlgebraic
