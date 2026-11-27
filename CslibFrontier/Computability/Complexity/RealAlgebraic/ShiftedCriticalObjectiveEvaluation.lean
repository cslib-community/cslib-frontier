/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalRootLabelEvaluation
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalPolynomialEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring

/-!
# Modular evaluation of the shifted critical objective

The source polynomial supplies the deformed objective at the queried point and the root-label
evaluation at that value. The shift is reduced modulo the quotient dimension plus one. The
composition stays at the counting level of the root-label evaluator.

Adapted from `SourceNormObjectiveEvaluation` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier shifted root label.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial MvPolynomial.CriticalSystem

/-- Evaluate the shifted critical objective at a modular point from the original source
evaluation callback. Here `d + 1` bounds the source degree. -/
noncomputable def criticalShiftedObjectiveResidue (p n d b e : ℕ) (z : List ℕ)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  let D := ell ^ n
  let y := criticalObjectiveValue p n ell (criticalParameterResidue p n ell b) z value
  modularSub p (e % (D + 1)) (4 * D * criticalRootLabelResidue p n d b y data value)

/-- Composition retains the source context and adds no counting level beyond that of the
critical root label. -/
theorem criticalShiftedObjectiveResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d b e : α → ℕ} {z : α → List ℕ}
    {data : α → List RootLabelTestCode} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (he : ComputableInPolyTime e enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalShiftedObjectiveResidue (p w) (n w) (d w) (b w) (e w) (z w)
      (data w) (fun y => value (w, y))) ∈ CountingFunction (a + 13) enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hu := criticalParameterResidue_polyTime hp hn hell hb
  have hobjective := criticalObjectiveValue_mem hp hn hell hu hz hv
  have hf := fst enc encNat
  have hlabel := criticalRootLabelResidue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hb.comp hf) (snd enc encNat) (hdata.comp hf)
    (CountingFunction.preprocess hv
      ((fst (encPair enc encNat) (encList encNat)).fst'.prod (snd _ _)))
  have hcomp := CountingFunction.comp_with hlabel
    (CountingFunction.mono (by omega : a ≤ a + 13) hobjective)
  have hD := binary_pow' (hbase := hell) (hexponent := hn)
  simpa only [criticalShiftedObjectiveResidue, Function.comp_apply] using
    modularSub_mem (CountingFunction.of_polyTime hp)
      (CountingFunction.of_polyTime (binary_mod.comp (he.prod (binary_add' hD (.const 1)))))
      (CountingFunction.nat_mul (CountingFunction.of_polyTime (binary_mul' (.const 4) hD)) hcomp)

/-- At the coefficient evaluator's prime cutoffs, the computed residue equals the evaluation
of the integer multivariate objective used in the final quotient determinant. -/
theorem criticalShiftedObjectiveResidue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b e : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1) (z : List ℕ)
    (data : List RootLabelTestCode) (value : List ℕ → ℕ)
    (hv : ∀ w, (value w : ZMod p) = eval
      (fun i : Fin n => ((w[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    let ell := d + 1
    let D := ell ^ n
    let L := decodeRootLabel (D := D) (by positivity) (n * ell.size) data
    let point : Fin n → ZMod p := fun i => (z[i.val]?.getD 0 : ℕ)
    let objective := deformedPolynomial ell (fun i => (separatedCenters ell i : ℤ))
      (2 ^ criticalParameterExponent n ell b) F
    let label := criticalShiftedRootLabel (by omega : 1 ≤ ell) b F hF L (e % (D + 1))
    (criticalShiftedObjectiveResidue p n d b e z data value : ZMod p) =
      eval point ((Polynomial.aeval objective label).map (Int.castRingHom (ZMod p))) := by
  intro ell D L point objective label
  let φ := Int.castRingHom (ZMod p)
  let y := criticalObjectiveValue p n ell (criticalParameterResidue p n ell b) z value
  have hp : p.Prime := Fact.out
  have hobjective : (y : ZMod p) = eval point (objective.map φ) := by
    have hu : φ ((2 : ℤ) ^ criticalParameterExponent n ell b) =
        (criticalParameterResidue p n ell b : ZMod p) := by
      simpa only [φ, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat] using
        (criticalParameterResidue_cast hp.ne_zero n ell b).symm
    simpa only [objective, deformedPolynomial_map, hu, y, point, φ, Int.coe_castRingHom,
      Int.cast_natCast] using
      criticalObjectiveValue_cast (F.map φ) ell (criticalParameterResidue p n ell b) z value hv
  let ψ := MvPolynomial.eval₂Hom φ point
  have hcompose :
      eval point ((Polynomial.aeval objective label).map φ) =
        label.eval₂ φ (eval point (objective.map φ)) := by
    rw [MvPolynomial.eval_map]
    change ψ (Polynomial.aeval objective label) = _
    rw [Polynomial.map_aeval_eq_aeval_map (φ := φ) (ψ := ψ) (by ext t; simp [ψ]),
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, MvPolynomial.eval_map,
      MvPolynomial.coe_eval₂Hom]
  have hlabel := criticalRootLabelResidue_cast d hd b y F hF hcut hdegree data value hv
  dsimp only at hlabel
  rw [hcompose, ← hobjective, criticalShiftedObjectiveResidue, modularSub_cast hp.pos,
    Nat.cast_mul, Nat.cast_mul, hlabel]
  simp only [label, criticalShiftedRootLabel, Polynomial.shiftedRootLabel,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, φ, Int.coe_castRingHom,
    Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Nat.cast_ofNat]
  ring

end Cslib.Complexity.RealAlgebraic
