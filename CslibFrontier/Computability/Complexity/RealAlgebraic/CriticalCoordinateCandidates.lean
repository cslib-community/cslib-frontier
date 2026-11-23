/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalParameterEvaluation
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Modular evaluation of indexed coordinate candidates

Each coefficient in the deformation parameter is a polynomial in the coordinate value.
The bivariate evaluator and a finite-field coefficient sum evaluate the addressed polynomial
without expanding it. The theorem `coordinateParameterDegreeBound_polyTime` computes a bound
on the coefficient index in binary from the unary arity and the binary exponent parameter.
The theorem `parametricCoordinateCoeffNormExponent_polyTime` computes the binary norm exponent
that bounds every addressed coefficient.

This adapts `LeanCanny.CountingHierarchy.coordinateCandidateValue` at lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, the coefficient extraction in
[OpenAI2026CountingHierarchy], Proposition 6.3. Selecting the highest nonzero coefficient
and proving real coordinate coverage remain open in
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

/-- The parameter-degree bound has binary polynomial-time access from a unary arity
and the binary exponent parameter. -/
theorem coordinateParameterDegreeBound_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => coordinateParameterDegreeBound (n w) (d w)) enc encNat := by
  have hell := binary_add' hd (.const 1)
  exact binary_mul' (binary_pow' hell hn)
    (binary_add' (.const 1) (binary_mul' (unary_to_binary.comp hn) hell))

/-- The binary coordinate characteristic norm exponent is computable in polynomial time
from unary arity, binary pure-power exponent and the binary input norm exponent. -/
theorem parametricCoordinateCoeffNormExponent_polyTime {α : Type} {enc : α ↪ List Bool}
    {n ell b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => parametricCoordinateCoeffNormExponent (n w) (ell w) (b w))
      enc encNat :=
  multiplicationMatrixCharpolyCoeffNormExponent_polyTime hn hell (.const 1) (.const 0)
    (binary_add' (unary_to_binary.comp (binary_size.comp hell)) hb)

/-- Evaluate coefficient `j` in the deformation parameter at the coordinate value `t`. -/
noncomputable def criticalCoordinateCandidateValue (p n d i j t : ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  coefficientResidue p j (fun u => criticalCoordinatePolynomialValue p n d u i t value)

/-- A query has unary arity and binary modulus, exponent parameter, coordinate index,
deformation-coefficient index, and value. Extraction adds eleven levels above source access. -/
theorem criticalCoordinateCandidateValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d i j t : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalCoordinateCandidateValue (p w) (n w) (d w) (i w) (j w) (t w)
      (fun z => value (w, z))) ∈ CountingFunction (a + 11) enc encNat := by
  have hw := fst enc encNat
  have hsource := CountingFunction.preprocess hv
    ((hw.comp (fst (encPair enc encNat) (encList encNat))).prod (snd _ _))
  have heval := criticalCoordinatePolynomialValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hw) (hn.comp hw) (hd.comp hw) (snd enc encNat) (hi.comp hw) (ht.comp hw) hsource
  have h := coefficientResidue_mem (a := a + 10)
    (value := fun (w, u) => criticalCoordinatePolynomialValue (p w) (n w) (d w) u (i w) (t w)
      (fun z => value (w, z))) E hp hj heval
  simpa only [criticalCoordinateCandidateValue, Nat.add_assoc, Function.comp_apply] using h

/-- Over a sufficiently large prime, the query agrees with the addressed integer
deformation coefficient evaluated at the supplied coordinate value. -/
theorem criticalCoordinateCandidateValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (i : Fin n) (j t : ℕ)
    (hcut : (d + 1) * ((d + 1) ^ n + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (hparam : coordinateParameterDegreeBound n d < p - 1) (hj : j < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ z, (value z : ZMod p) = eval₂ (Int.castRingHom (ZMod p))
      (fun k : Fin n => ((z[k.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalCoordinateCandidateValue p n d i.val j t value : ZMod p) =
      ((Polynomial.Bivariate.swap
        (parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i)).coeff j).eval₂
        (Int.castRingHom (ZMod p)) (t : ZMod p) := by
  let P := parametricCoordinatePolynomial (by omega : 1 ≤ d + 1) F hF i
  let φ := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) (t : ZMod p)
  let Q := (Polynomial.Bivariate.swap P).map φ
  have hQ : Q.natDegree < p - 1 := Polynomial.natDegree_map_le.trans_lt
    ((parametricCoordinatePolynomial_natDegree_swap_le d hd F hF i).trans_lt hparam)
  have heval (u : ℕ) (_ : u < p) :
      (criticalCoordinatePolynomialValue p n d u i.val t value : ZMod p) =
        Q.eval (u : ZMod p) := by
    rw [criticalCoordinatePolynomialValue_cast d hd F hF i u t hcut hdegree value hv]
    dsimp only [Q, φ, P]
    rw [Polynomial.eval_map, Polynomial.Bivariate.eval₂_eval₂RingHom_swap]
  rw [criticalCoordinateCandidateValue, coefficientResidue_eq_val Q j _ hQ hj heval,
    ZMod.natCast_zmod_val]
  exact Polynomial.coeff_map φ j

end Cslib.Complexity.RealAlgebraic
