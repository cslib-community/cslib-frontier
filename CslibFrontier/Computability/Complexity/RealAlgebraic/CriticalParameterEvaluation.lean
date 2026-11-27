/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoefficientEvaluation
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalIntegerSpecialization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Modular evaluation at the chosen critical parameter

From unary arity and binary degree and norm data, the parameter exponent is computable in
polynomial time. Modular powering computes the parameter directly modulo a nonzero modulus.
For primes satisfying the existing finite-residue evaluator bounds, feeding this residue to
the coefficient evaluator gives the characteristic coefficient of the integer quotient
reduced modulo the prime.

Adapted from `NativeCriticalBounds` and `CriticalNumericEvaluation` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the shared norm allowance and the
parameter-exclusion bound for the actual quotient.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem

variable {α : Type} {enc : α ↪ List Bool}

private theorem binarySize_polyTime {f : α → ℕ} (hf : ComputableInPolyTime f enc encNat) :
    ComputableInPolyTime (fun w => (f w).size) enc encNat :=
  unary_to_binary.comp (binary_size.comp hf)

/-- The symbolic norm exponent is polynomial-time computable with unary arity. -/
@[fun_prop] theorem parametricValueCoeffNormExponent_polyTime {n ell b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hell : ComputableInPolyTime ell enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => parametricValueCoeffNormExponent (n w) (ell w) (b w))
      enc encNat := by
  have hn' := unary_to_binary.comp hn
  have he := binary_add' hell (.const 1)
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  have hB := binary_add' (binary_mul' hD he) (binary_mul' hn' (binary_sub' hell (.const 1)))
  have ha := binary_mul' hn' (binarySize_polyTime (binary_mul' (.const 4) hell))
  have hR := binary_add' (binarySize_polyTime (binary_add' (binary_mul' (.const 3) hn') (.const 1)))
    (binary_add' (binarySize_polyTime he) (binary_max' (binary_mul' he ha) hb))
  have hJ := binary_mul' (binary_add' (binary_add' (binarySize_polyTime hn')
    (binarySize_polyTime hell)) (binary_add' hR (.const 1))) hn'
  have hA := binary_add' (binary_add' (binary_add'
    (binary_mul' (binarySize_polyTime (binary_add' hB (.const 1))) hn') hJ)
    (binary_mul' hR hB)) hR
  simpa only [parametricValueCoeffNormExponent, criticalSystemCoeffNormExponent,
    Function.comp_apply] using binary_add'
      (binarySize_polyTime (binary_add' hD (.const 1))) (binary_mul' hA hD)

/-- The exponent that avoids the value-section and derivative-resultant roots is
polynomial-time computable from binary degree and norm bounds. -/
@[fun_prop] theorem parameterExclusionExponent_polyTime {D H : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hH : ComputableInPolyTime H enc encNat) :
    ComputableInPolyTime (fun w => Polynomial.parameterExclusionExponent (D w) (H w))
      enc encNat := by
  have ht := binary_mul' (.const 2) hD
  have hres := binary_add' (binary_mul' (binarySize_polyTime ht) ht)
    (binary_mul' (binary_add' (binarySize_polyTime hD) hH) ht)
  have hcut := binary_add' hH (binary_mul' (binary_add' hH (.const 1)) hD)
  simpa only [Polynomial.parameterExclusionExponent] using binary_add' (binary_max' hres hcut)
    (.const 1)

/-- Compute the chosen parameter as a residue without expanding the integer power of two. -/
@[expose] def criticalParameterResidue (p n ell b : ℕ) : ℕ :=
  powMod p 2 (criticalParameterExponent n ell b)

/-- The chosen parameter modulo `p) is polynomial-time computable from unary arity and the
binary modulus, pure-power degree and input norm exponent. -/
@[fun_prop] theorem criticalParameterResidue_polyTime {p n ell b : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalParameterResidue (p w) (n w) (ell w) (b w))
      enc encNat := by
  simpa only [criticalParameterResidue, criticalParameterExponent] using
    computableInPolyTime_powMod hp (.const 2)
      (parameterExclusionExponent_polyTime (binary_pow' (hbase := hell) (hexponent := hn))
        (parametricValueCoeffNormExponent_polyTime hn hell hb))

/-- For a nonzero modulus, the computed residue represents the chosen integer parameter. -/
theorem criticalParameterResidue_cast {p : ℕ} (hp : p ≠ 0) (n ell b : ℕ) :
    (criticalParameterResidue p n ell b : ZMod p) =
      (2 : ZMod p) ^ criticalParameterExponent n ell b := by
  simp only [criticalParameterResidue, powMod_of_ne_zero hp, ZMod.natCast_mod, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The addressed evaluator at the computed parameter gives the coefficient of the integer
critical-value polynomial reduced modulo the prime, under the finite-residue bounds. -/
theorem criticalCoefficientValue_at_criticalParameterResidue {p n m b : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    let u : ℤ := 2 ^ criticalParameterExponent n (d + 1) b
    let q := valuePolynomial (by omega : 1 ≤ d + 1)
      (fun i => (separatedCenters (d + 1) i : ℤ)) u F hF
    criticalCoefficientValue p n d (criticalParameterResidue p n (d + 1) b) m value =
      ((q.map (Int.castRingHom (ZMod p))).coeff m).val := by
  intro u q
  dsimp only [q]
  rw [valuePolynomial_map]
  have hu : (Int.castRingHom (ZMod p)) u = (criticalParameterResidue p n (d + 1) b : ZMod p) := by
    simpa only [u, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat] using
      (criticalParameterResidue_cast (Fact.out : p.Prime).ne_zero n (d + 1) b).symm
  rw [hu]
  simpa only [Int.coe_castRingHom, Int.cast_natCast, valuePolynomial] using
    criticalCoefficientValue_eq d hd (criticalParameterResidue p n (d + 1) b)
      (F.map (Int.castRingHom (ZMod p))) ((totalDegree_map_le _ F).trans hF) hcut hdegree value hv

end Cslib.Complexity.RealAlgebraic
