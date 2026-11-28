/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ShiftedCriticalObjectiveEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelPrecision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Modular evaluation of the critical label determinant

A single source evaluator supplies the shifted objective, Jacobian and lower relations
to the quotient determinant evaluator. The trace bound and prime cutoff are computed
from unary arity and binary degree and norm bounds.

Adapted from `SourceNormDeterminantEvaluation` and `NativeNormBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier label and trace bounds.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

private def traceDegreeBound (n d b : ℕ) : ℕ :=
  (d + 1) ^ n * criticalLabelObjectiveDegreeBound n (d + 1) b + n * d

/-- The prime must exceed the interpolation cutoffs for both coefficient evaluations and
the dimension-squared cutoff for characteristic reconstruction. -/
def criticalLabelDeterminantPrimeCutoff (n d b : ℕ) : ℕ :=
  let ell := d + 1
  let D := ell ^ n
  max (ell * (D * (d + 2) + n * d + 1) + 1)
    (max (ell * (traceDegreeBound n d b + 1) + 1) (D * D + 1))

private theorem criticalShiftedLabelDegreeBound_polyTime {α : Type} {enc : α ↪ List Bool}
    {n ell b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w =>
      Polynomial.signLabelDegreeBound (n w * (ell w).size + 1)
        (Polynomial.derivativeRootLabelPrecision (ell w ^ n w)
          (criticalRootLabelCoeffNormExponent (n w) (ell w) (b w))) (ell w ^ n w))
      enc encNat := by
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  have hN := unary_to_binary.comp (unary_mul' hn (binary_size.comp hell))
  have hprecision := derivativeRootLabelPrecision_polyTime hD
    (criticalRootLabelCoeffNormExponent_polyTime hn hell hb)
  have hm := binary_add' (binary_add' hN (.const 1)) (.const 1)
  have hfactor := binary_mul' (binary_mul' (.const 2) hm)
    (binary_add' (binary_mul' (.const 2) hprecision) (.const 1))
  exact binary_mul' (.const 2) (binary_mul' hm (binary_mul' hfactor hD))

/-- The shifted objective degree bound is computable in polynomial time from the source
degree and norm bounds and the unary arity. -/
theorem criticalLabelObjectiveDegreeBound_polyTime {α : Type} {enc : α ↪ List Bool}
    {n ell b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalLabelObjectiveDegreeBound (n w) (ell w) (b w))
      enc encNat :=
  binary_mul' (criticalShiftedLabelDegreeBound_polyTime hn hell hb) (binary_add' hell (.const 1))

/-- The binary magnitude exponent for the critical label determinant is computable
in polynomial time from unary arity and the binary source bounds. -/
theorem criticalLabelDeterminantExponent_polyTime {α : Type} {enc : α ↪ List Bool}
    {n ell b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalLabelDeterminantExponent (n w) (ell w) (b w))
      enc encNat := by
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  have hN := unary_to_binary.comp (unary_mul' hn (binary_size.comp hell))
  have hm := binary_add' hN (.const 1)
  have hm' := binary_add' hm (.const 1)
  have hB := criticalRootLabelCoeffNormExponent_polyTime hn hell hb
  have hderivative := iterateDerivativeNormExponent_polyTime hD hB
  have hprecision := derivativeRootLabelPrecision_polyTime hD hB
  have hwidth := binary_add' (binary_mul' (.const 2) hprecision) (.const 1)
  have hfactor := binary_mul' (binary_mul' (.const 2) hm') hwidth
  have hlabel := binary_add' (unary_to_binary.comp (binary_size.comp hm))
    (binary_mul' (.const 2) (binary_mul' hm' (binary_add'
      (binary_mul' hfactor (binary_add' hwidth hderivative)) (.const 2))))
  have hshift := binary_add' (binary_add' (binary_add' hlabel (.const 3)) hN) (.const 3)
  have hsystem := binary_add'
    (criticalSystemCoeffNormExponent_polyTime (unary_to_binary.comp hn) hell hb)
    (criticalParameterExponent_polyTime hn hell hb)
  have hobjective := binary_add' hshift
    (binary_mul' hsystem (criticalShiftedLabelDegreeBound_polyTime hn hell hb))
  exact multiplicationMatrixCharpolyCoeffNormExponent_polyTime hn hell
    (criticalLabelObjectiveDegreeBound_polyTime hn hell hb) hobjective hsystem

private theorem traceDegreeBound_polyTime {α : Type} {enc : α ↪ List Bool} {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => traceDegreeBound (n w) (d w) (b w)) enc encNat := by
  have hell := binary_add' hd (.const 1)
  simpa only [traceDegreeBound, Function.comp_apply] using binary_add'
    (binary_mul' (binary_pow' (hbase := hell) (hexponent := hn))
      (criticalLabelObjectiveDegreeBound_polyTime hn hell hb))
    (binary_mul' (unary_to_binary.comp hn) hd)

/-- The admissible-prime cutoff has a polynomial-time binary evaluator. -/
theorem criticalLabelDeterminantPrimeCutoff_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalLabelDeterminantPrimeCutoff (n w) (d w) (b w))
      enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  have hinner := binary_add' (binary_mul' hD (binary_add' hd (.const 2)))
    (binary_mul' (unary_to_binary.comp hn) hd)
  have hfirst := binary_add' (binary_mul' hell (binary_add' hinner (.const 1))) (.const 1)
  have hsecond := binary_add'
    (binary_mul' hell (binary_add' (traceDegreeBound_polyTime hn hd hb) (.const 1))) (.const 1)
  have hsquare := binary_add' (binary_mul' hD hD) (.const 1)
  simpa only [criticalLabelDeterminantPrimeCutoff, Function.comp_apply] using
    binary_max' hfirst (binary_max' hsecond hsquare)

/-- Evaluate the critical label determinant from the source polynomial callback and the
candidate derivative-sign witness and shift. -/
noncomputable def criticalLabelDeterminantResidue (p n d b e : ℕ)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  let u := criticalParameterResidue p n ell b
  quotientDeterminantValue p n ell (traceDegreeBound n d b)
    (fun z => criticalShiftedObjectiveResidue p n d b e z data value)
    (fun z => criticalJacobianValue p n ell u z value)
    (fun i z => criticalLowerValue p n ell u i z value)

/-- At any positive modulus the evaluator returns a canonical residue. -/
theorem criticalLabelDeterminantResidue_lt {p : ℕ} (hp : 0 < p) (n d b e : ℕ)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ) :
    criticalLabelDeterminantResidue p n d b e data value < p :=
  Nat.mod_lt _ hp

/-- The determinant costs eight counting levels above the shifted objective and twenty-one
above the source evaluator. -/
theorem criticalLabelDeterminantResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d b e : α → ℕ} {data : α → List RootLabelTestCode}
    {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (he : ComputableInPolyTime e enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalLabelDeterminantResidue (p w) (n w) (d w) (b w) (e w) (data w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 21) enc encNat := by
  let points := encList encNat
  have hell := binary_add' hd (.const 1)
  have hu := criticalParameterResidue_polyTime hp hn hell hb
  have haccess := criticalEvaluationAccess_mem E hp hn hell hu hv
  have hf := fst enc points
  have hobjective := criticalShiftedObjectiveResidue_mem (Decoder.pair E (Decoder.list Decoder.nat))
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hb.comp hf) (he.comp hf) (snd enc points)
    (hdata.comp hf)
    (CountingFunction.preprocess hv ((fst (encPair enc points) points).fst'.prod (snd _ _)))
  have hlevel : a + 1 ≤ a + 13 := by omega
  simpa only [criticalLabelDeterminantResidue, Nat.add_assoc, Function.comp_apply] using
    quotientDeterminantValue_mem E hp hn hell (traceDegreeBound_polyTime hn hd hb)
      hobjective (CountingFunction.mono hlevel haccess.2.1)
      (CountingFunction.mono hlevel haccess.2.2)

/-- Above the computed prime cutoff, the evaluator represents the integer determinant for
the decoded witness and bounded shift used in the real-feasibility criterion. -/
theorem criticalLabelDeterminantResidue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b e : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (hcut : criticalLabelDeterminantPrimeCutoff n d b < p)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ)
    (hv : ∀ z, (value z : ZMod p) = eval
      (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    let ell := d + 1
    let D := ell ^ n
    let L := decodeRootLabel (D := D) (by positivity) (n * ell.size) data
    (criticalLabelDeterminantResidue p n d b e data value : ZMod p) =
      (criticalLabelDeterminant (by omega : 1 ≤ ell) b F hF L (e % (D + 1)) : ZMod p) := by
  intro ell D L
  let φ := Int.castRingHom (ZMod p)
  let a : Fin n → ℤ := fun i => separatedCenters ell i
  let u : ℤ := 2 ^ criticalParameterExponent n ell b
  let ur := criticalParameterResidue p n ell b
  let r := criticalLower ell a u F
  let v := Polynomial.aeval (deformedPolynomial ell a u F)
    (criticalShiftedRootLabel (by omega : 1 ≤ ell) b F hF L (e % (D + 1)))
  have hr (i : Fin n) : (r i).totalDegree ≤ d :=
    Nat.le_of_lt_succ (criticalLower_degree ell (by omega) a u F hF i)
  have he : e % (D + 1) ≤ D := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
  have hvdeg : v.totalDegree ≤ criticalLabelObjectiveDegreeBound n ell b :=
    (criticalLabelObjective_bounds (by omega : 2 ≤ ell) F hF hb L he).1
  have hp : p.Prime := Fact.out
  have hu : φ u = (ur : ZMod p) := by
    simpa only [φ, u, ur, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat] using
      (criticalParameterResidue_cast hp.ne_zero n ell b).symm
  let rmod := criticalLower ell
    (fun i : Fin n => ((separatedCenters ell i : ℕ) : ZMod p)) (ur : ZMod p) (F.map φ)
  have hrmap (i : Fin n) : (r i).map φ = rmod i := by
    simp only [r, rmod, criticalLower_map, hu, a, φ, Int.coe_castRingHom, Int.cast_natCast]
  rw [criticalLabelDeterminantPrimeCutoff] at hcut
  have hinner := (le_max_left _ _).trans_lt hcut
  have hrest := (le_max_right _ _).trans_lt hcut
  have houter := (le_max_left _ _).trans_lt hrest
  have hsquare := (le_max_right _ _).trans_lt hrest
  have hdim : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have hsize : d + 2 < p := by
    have hspan : d + 2 ≤ (d + 1) ^ n * (d + 2) := Nat.le_mul_of_pos_left _ hdim
    have hgrid : (d + 1) ^ n * (d + 2) + n * d + 1 ≤
        (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hFp : (F.map φ).totalDegree < p - 1 := (totalDegree_map_le _ _).trans_lt (by omega)
  rw [criticalLabelDeterminantResidue, criticalLabelDeterminant]
  refine quotientDeterminantValue_cast φ d hd r hr v ?_ houter (by omega) _ _ _ ?_ ?_ ?_
  · intro k _ hk
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_pow v k).trans (Nat.mul_le_mul hk hvdeg))
      (totalDegree_jacobian_le d r hr))
  · intro s _
    exact criticalShiftedObjectiveResidue_cast d hd b e F hF hinner (by omega) _ data value hv
  · intro s _
    rw [jacobian_map, show (fun i => (r i).map φ) = rmod from funext hrmap]
    exact criticalJacobianValue_cast (F.map φ)
      (fun i => (separatedCenters ell i : ℕ)) ell ur _ value hFp (by omega) hv
  · intro i s _
    rw [hrmap]
    exact criticalLowerValue_cast (F.map φ) ell ur i _ value hFp (by omega) hv

end Cslib.Complexity.RealAlgebraic
