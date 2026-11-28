/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalParameterEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelWitness
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalDeterminantFeasibility
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
import CslibFrontier.Computability.Complexity.RealAlgebraic.SparseRootLabelEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Sparse root-label evaluation from critical source access

The source polynomial evaluator supplies the addressed coefficients of the integer
critical-value polynomial at its chosen parameter. The cutoff gives the qualifying
test, and the witness supplies the derivative orders and target values.

Adapted from `SourceRootLabelEvaluation` and `NativeCriticalBounds` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier critical parameter and norm
bounds.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

/-- The shared coefficient norm exponent for the critical label is computed from unary arity
and binary degree and source norm bounds. -/
@[fun_prop] theorem criticalRootLabelCoeffNormExponent_polyTime {α : Type} {enc : α ↪ List Bool}
    {n ell b : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalRootLabelCoeffNormExponent (n w) (ell w) (b w))
      enc encNat := by
  have hH := parametricValueCoeffNormExponent_polyTime hn hell hb
  have hdim := binary_pow' (hbase := hell) (hexponent := hn)
  have hspan := binary_add' (binary_add' hell (.const 2))
    (binary_mul' (unary_to_binary.comp hn) hell)
  have hspecialize := binary_mul' (criticalParameterExponent_polyTime hn hell hb)
    (binary_mul' hdim hspan)
  simpa only [criticalRootLabelCoeffNormExponent, Function.comp_apply] using
    binary_max' (binary_add' hH hspecialize) (binary_add' hH (.const 2))

/-- Evaluate the critical root label at the residue `z` from a source evaluation callback and
the bounded derivative-sign witness. Here `d + 1` is the bound on the source degree. -/
noncomputable def criticalRootLabelResidue (p n d b z : ℕ)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  let D := ell ^ n
  let N := n * ell.size
  let u := criticalParameterResidue p n ell b
  let cutoff := powMod p 2 (parametricValueCoeffNormExponent n ell b + 1)
  sparseRootLabelResidue p D N (criticalRootLabelCoeffNormExponent n ell b) z
    (modularSub p cutoff z) (fun j => criticalCoefficientValue p n d u j value)
    (rootLabelCodeOrders D N data) (rootLabelCodeTarget p data)

/-- The source evaluator yields sparse critical-label evaluations thirteen counting levels above
the source. The cutoff and the witness readers are polynomial-time computable. -/
theorem criticalRootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d b z : α → ℕ} {data : α → List RootLabelTestCode}
    {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalRootLabelResidue (p w) (n w) (d w) (b w) (z w) (data w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 13) enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  have hN := unary_mul' hn (binary_size.comp hell)
  have hu := criticalParameterResidue_polyTime hp hn hell hb
  have hcutoff := computableInPolyTime_powMod hp (.const 2)
    (binary_add' (parametricValueCoeffNormExponent_polyTime hn hell hb) (.const 1))
  have hbase := modularSub_polyTime hp hcutoff hz
  have hf := fst enc encNat
  have hi := snd enc encNat
  have hv' := CountingFunction.preprocess hv
    (input := encPair (encPair enc encNat) (encList encNat))
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hcoeff := criticalCoefficientValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hu.comp hf) hi hv'
  have htarget := rootLabelCodeTarget_polyTime (hp.comp hf) hi (hdata.comp hf)
  have hlabel := sparseRootLabelResidue_mem E hp hD hN
    (criticalRootLabelCoeffNormExponent_polyTime hn hell hb) hz
    (CountingFunction.of_polyTime hbase) (rootLabelCodeOrders_polyTime hD hN hdata)
    hcoeff (CountingFunction.of_polyTime htarget)
  have hmax : max (a + 9) 3 = a + 9 := max_eq_left (by omega)
  simpa only [criticalRootLabelResidue, hmax, Nat.add_assoc, Function.comp_apply] using hlabel

/-- At primes meeting the coefficient evaluator's cutoffs, the source-based evaluator gives the
integer sparse label used in the shifted determinant criterion. -/
theorem criticalRootLabelResidue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b z : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    let ell := d + 1
    let D := ell ^ n
    let N := n * ell.size
    let q := valuePolynomial (by omega : 1 ≤ ell)
      (fun i => (separatedCenters ell i : ℤ)) (2 ^ criticalParameterExponent n ell b) F hF
    let b₀ := Polynomial.C ((2 : ℤ) ^ (parametricValueCoeffNormExponent n ell b + 1)) -
      Polynomial.X
    let L := decodeRootLabel (D := D) (by positivity) N data
    (criticalRootLabelResidue p n d b z data value : ZMod p) =
      (Polynomial.sparseIntegerRootLabel q b₀ N
        (criticalRootLabelCoeffNormExponent n ell b) L).eval₂
        (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  intro ell D N q b₀ L
  have hp : p.Prime := Fact.out
  have hdim : D < p := by
    have hle : (d + 1) ^ n ≤ (d + 1) ^ n * (d + 1) ^ n :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact hle.trans_lt (hdegree.trans_le (Nat.sub_le _ _))
  have hq : q.natDegree ≤ D := (valuePolynomial_natDegree _ _ _ _ _).le
  have hcoeff (j : ℕ) (_ : j ≤ D) :
      (criticalCoefficientValue p n d (criticalParameterResidue p n ell b) j value : ZMod p) =
        (q.map (Int.castRingHom (ZMod p))).coeff j := by
    rw [criticalCoefficientValue_at_criticalParameterResidue (b := b) (m := j) d hd F hF
      hcut hdegree value hv,
      ZMod.natCast_zmod_val]
  have hbase :
      (modularSub p (powMod p 2 (parametricValueCoeffNormExponent n ell b + 1)) z : ZMod p) =
        b₀.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
    simp only [b₀, modularSub_cast hp.pos, powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod,
      Nat.cast_pow, Nat.cast_ofNat, Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
  rw [criticalRootLabelResidue, rootLabelCodeOrders_eq (by positivity)]
  exact sparseRootLabelResidue_cast q b₀ _ z _ _ _ L hq hdim hcoeff hbase
    (fun i => rootLabelCodeTarget_cast hp.pos (by positivity) data q b₀ i)

end Cslib.Complexity.RealAlgebraic
