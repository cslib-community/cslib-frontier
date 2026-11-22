/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CoefficientEvaluation
public import CslibFrontier.Logics.RealArithmetic.FormulaGatePolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateKronecker
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap

/-!
# Indexed gate coefficients from modular coordinate values

Pack the bivariate coefficient indices in a single Kronecker exponent and use the
finite-field coefficient sum on the gate's executable modular evaluations.
This adapts `LeanCanny.ETR.BivariateTermReader.coefficient_eq` at
lean-canny `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
A polynomial-time source of the coordinate values yields a certificate at one
counting-function level. The source for the critical-point family remains separate.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Logic.RealArithmetic Turing.MultiTapeTM

/-- The coefficient sum for one gate at inner index `i` and outer index `j`.
The callback supplies coordinate residues at the packed evaluation point.
Indices outside the radix or finite-field interpolation range return zero. -/
@[expose] noncomputable def formulaWordGateCoefficientResidue (word : List Bool)
    (gate p radix i j : ℕ) (point : ℕ → List ℕ) : ℕ :=
  if i < radix then
    if i + radix * j < p - 1 then
      coefficientResidue p (i + radix * j) (fun z => formulaWordGateResidue word gate p (point z))
    else 0
  else 0

/-- Polynomial-time coordinate queries give coefficient extraction in one counting-function
level. The gate index, modulus, radix and coefficient indices are binary. -/
theorem formulaWordGateCoefficientResidue_mem {α : Type} {enc : α ↪ List Bool}
    (D : Decoder enc) {word : α → List Bool} {gate p radix i j : α → ℕ}
    {point : α × ℕ → List ℕ}
    (hword : ComputableInPolyTime word enc encBits)
    (hgate : ComputableInPolyTime gate enc encNat)
    (hp : ComputableInPolyTime p enc encNat) (hpos : ∀ w, 0 < p w)
    (hradix : ComputableInPolyTime radix enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat)
    (hpoint : ComputableInPolyTime point (encPair enc encNat) (encList encNat)) :
    (fun w => formulaWordGateCoefficientResidue (word w) (gate w) (p w) (radix w)
      (i w) (j w) (fun z => point (w, z))) ∈ CountingFunction 1 enc encNat := by
  let hf := ComputableInPolyTime.fst enc encNat
  have hv := formulaWordGateResidue_polyTime (hword.comp hf) (hgate.comp hf) (hp.comp hf)
    (fun a => hpos a.1) hpoint
  have hk := ComputableInPolyTime.binary_add' hi (ComputableInPolyTime.binary_mul' hradix hj)
  have hc := coefficientResidue_mem (a := 0) D hp hk (CountingFunction.of_polyTime hv)
  have hinner := ComputableInPolyTime.binary_lt' hi hradix
  have hfield := ComputableInPolyTime.binary_lt' hk
    (ComputableInPolyTime.binary_sub' hp (.const 1))
  have hzero := CountingFunction.of_polyTime (a := 1) (ComputableInPolyTime.const 0 :
    ComputableInPolyTime (fun _ : α => (0 : ℕ)) enc encNat)
  simpa only [formulaWordGateCoefficientResidue, Function.comp_apply, decide_eq_true_eq] using
    CountingFunction.ite (CountingFunction.of_polyTime hinner)
      (CountingFunction.ite (CountingFunction.of_polyTime hfield) hc hzero) hzero

/-- Correctness at a prime field whose size exceeds the degree of the packed gate
polynomial by at least two. The inner degree bound excludes index collisions.
The equation covers every query index, including those beyond either cutoff. -/
theorem formulaWordGateCoefficientResidue_eq_val (word : List Bool) (gate : ℕ)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ)) {p radix : ℕ} [Fact p.Prime]
    (i j : ℕ) (point : ℕ → List ℕ)
    (hinner : (Polynomial.Bivariate.swap
      (formulaWordGatePolynomial word gate coordinates)).natDegree < radix)
    (hdegree : ((formulaWordGatePolynomial word gate coordinates).eval
      (Polynomial.X ^ radix)).natDegree < p - 1)
    (hpoint : ∀ z < p, ∀ k : Fin word.length,
      (((point z)[k.val]?.getD 0 : ℕ) : ZMod p) =
        Polynomial.aevalAeval (z : ZMod p) ((z : ZMod p) ^ radix) (coordinates k)) :
    formulaWordGateCoefficientResidue word gate p radix i j point =
      (((((formulaWordGatePolynomial word gate coordinates).coeff j).coeff i : ℤ) :
        ZMod p)).val := by
  let P := formulaWordGatePolynomial word gate coordinates
  let packed := P.eval (Polynomial.X ^ radix)
  change _ = (((P.coeff j).coeff i : ℤ) : ZMod p).val
  have hp : p.Prime := Fact.out
  by_cases hi : i < radix
  · have hcoeff := Polynomial.Bivariate.coeff_eval_X_pow P hinner i j hi
    rw [formulaWordGateCoefficientResidue, ite_eq_left hi]
    by_cases hk : i + radix * j < p - 1
    · rw [ite_eq_left hk]
      have hvalue (z : ℕ) (hz : z < p) :
          (formulaWordGateResidue word gate p (point z) : ZMod p) =
            (packed.map (Int.castRingHom (ZMod p))).eval (z : ZMod p) := by
        rw [formulaWordGateResidue_eq_aevalAeval word gate coordinates hp.pos (point z)
          _ _ (hpoint z hz), ZMod.natCast_zmod_val, Polynomial.eval_map,
          ← algebraMap_int_eq, ← Polynomial.aeval_def]
        exact (Polynomial.Bivariate.aeval_eval_X_pow P radix (z : ZMod p)).symm
      rw [coefficientResidue_eq_val _ _ _
        (Polynomial.natDegree_map_le.trans_lt hdegree) hk hvalue, Polynomial.coeff_map, hcoeff,
        Int.coe_castRingHom]
    · rw [ite_eq_right hk, ← hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt
        (hdegree.trans_le (Nat.le_of_not_gt hk)), Int.cast_zero, ZMod.val_zero]
  · rw [formulaWordGateCoefficientResidue, ite_eq_right hi, ← Polynomial.Bivariate.coeff_coeff_swap,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_le (Nat.le_of_not_gt hi)),
      Polynomial.coeff_zero, Int.cast_zero, ZMod.val_zero]

end Cslib.Complexity.RealAlgebraic
