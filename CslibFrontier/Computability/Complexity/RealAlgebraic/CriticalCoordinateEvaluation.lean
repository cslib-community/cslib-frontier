/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCoefficients
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CoordinateCharacteristicPolynomial
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.PolynomialEvaluation

/-!
# Modular evaluation of the coordinate characteristic polynomial

At a supplied deformation parameter, evaluate the characteristic polynomial of multiplication
by a coordinate by summing the addressed coefficients against powers of the coordinate value.
The cost includes every coefficient query, starting from evaluations of the source polynomial.

This adapts `LeanCanny.CountingHierarchy.coordinatePolynomialValue` at lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. Selection of the leading deformation coefficient
and real coordinate coverage remain open in
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

/-- Evaluate the coordinate characteristic polynomial at deformation parameter `u` and
coordinate value `t`. The degree bound is the dimension of the pure-power quotient. -/
noncomputable def criticalCoordinatePolynomialValue (p n d u i t : ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  polynomialResidue p ((d + 1) ^ n) t fun k =>
    criticalCoordinateCoefficientValue p n d u i k value

/-- The arity is unary. The modulus, degree parameter, deformation parameter, coordinate index,
and evaluation point are binary. The complete evaluation adds ten levels to source access. -/
theorem criticalCoordinatePolynomialValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u i t : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalCoordinatePolynomialValue (p w) (n w) (d w) (u w) (i w) (t w)
      (fun z => value (w, z))) ∈ CountingFunction (a + 10) enc encNat := by
  have hw := fst enc encNat
  have hsource := CountingFunction.preprocess hv
    ((hw.comp (fst (encPair enc encNat) (encList encNat))).prod (snd _ _))
  have hcoeff := criticalCoordinateCoefficientValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hw) (hn.comp hw) (hd.comp hw) (hu.comp hw) (hi.comp hw) (snd enc encNat) hsource
  exact polynomialResidue_mem E hp (binary_pow' (binary_add' hd (.const 1)) hn) ht hcoeff

/-- The modular evaluator agrees with evaluating the integer polynomial, first specializing the
deformation parameter and then evaluating the coordinate value. -/
theorem criticalCoordinatePolynomialValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (i : Fin n) (u t : ℕ)
    (hcut : (d + 1) * ((d + 1) ^ n + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ z, (value z : ZMod p) = eval₂ (Int.castRingHom (ZMod p))
      (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalCoordinatePolynomialValue p n d u i.val t value : ZMod p) =
      (parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i).eval₂
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) (u : ZMod p)) (t : ZMod p) := by
  let φ := Int.castRingHom (ZMod p)
  have hp : p.Prime := Fact.out
  refine polynomialResidue_cast hp.ne_zero _ _ _ _ (parametricCoordinatePolynomial_natDegree
    (by omega : 1 ≤ d + 1) F hF i).le _ ?_
  intro k _
  rw [criticalCoordinateCoefficientValue_eq d hd u k i (F.map φ)
    ((totalDegree_map_le φ F).trans hF) hcut hdegree value (by simpa only [eval_map] using hv),
    ZMod.natCast_zmod_val, ← Polynomial.coeff_map,
    parametricCoordinatePolynomial_map_eval₂]

end Cslib.Complexity.RealAlgebraic
