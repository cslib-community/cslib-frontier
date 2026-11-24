/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoordinateCoefficients
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Relative critical-value coefficients from a controlled source

`Controlled.relativeCoefficientValue` fixes the retained parameters in the source query and
computes an addressed critical-value coefficient. `Controlled.relativeCoefficientValue_mem`
charges nine counting levels above the source evaluator. `Controlled.relativeCoefficientValue_cast`
identifies the result with evaluation of the corresponding relative coefficient at the chosen
penalty and parameters, over a prime satisfying the trace interpolation and source cutoffs.

Adapted from `PointBlocks`, `FinitePolynomialBlocks`, `FrozenPolynomialEvaluation`, and
`FrozenCriticalCoefficients` in lean-canny (`970f28a5ecefc1327402ade16c068aa4b1b2c183`).
Evaluating the full flattened polynomial remains open under
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

private def fiberPoint (n : ℕ) (witness params : List ℕ) : List ℕ :=
  (List.range n).map (fun i => witness[i]?.getD 0) ++ params

private theorem fiberPoint_polyTime {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {witness params : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hw : ComputableInPolyTime witness enc (encList encNat))
    (hz : ComputableInPolyTime params enc (encList encNat)) :
    ComputableInPolyTime (fun q => fiberPoint (n q) (witness q) (params q))
      enc (encList encNat) := by
  have hi := unary_to_binary.comp (snd enc encUnary)
  have hread : ComputableInPolyTime (fun q : α × ℕ => (witness q.1)[q.2]?.getD 0)
      (encPair enc encUnary) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      listGetD_binary 0 (hw.comp (fst enc encUnary)) hi
  exact (listAppend _).comp ((mapWithInput (range.comp hn) hread).prod hz)

private theorem eval_fiberPoint {n m : ℕ} {S : Type*} [CommRing S]
    (P : MvPolynomial (Fin (n + m)) ℤ) (φ : ℤ →+* S) (witness params : List ℕ) :
    eval₂ φ (fun i : Fin (n + m) => (((fiberPoint n witness params)[i.val]?.getD 0 : ℕ) : S)) P =
      eval (fun i : Fin n => ((witness[i.val]?.getD 0 : ℕ) : S))
        ((sumRingEquiv ℤ (Fin n) (Fin m) (rename finSumFinEquiv.symm P)).map
          (eval₂Hom φ fun i => ((params[i.val]?.getD 0 : ℕ) : S))) := by
  rw [eval_map, eval₂_sumRingEquiv, eval₂_rename]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [fiberPoint, List.getElem?_append, j.isLt]
  · simp [fiberPoint, List.getElem?_append, Nat.not_lt.mpr (Nat.le_add_right n j.val)]

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

private theorem fiberEvaluate_mem (C : Controlled P enc a)
    (hn : ComputableInPolyTime n enc encUnary) {p : α → ℕ} {params : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hparams : ComputableInPolyTime params enc (encList encNat)) :
    (fun (w, y) => C.evaluate (w, p w, fiberPoint (n w) y (params w))) ∈
      CountingFunction a (encPair enc (encList encNat)) encNat := by
  have hw := fst enc (encList encNat)
  have hy := snd enc (encList encNat)
  have hpoint := fiberPoint_polyTime (hn.comp hw) hy (hparams.comp hw)
  exact CountingFunction.preprocess C.evaluate_mem (hw.prod ((hp.comp hw).prod hpoint))

/-- Query one relative critical-value coefficient with both the penalty and the parameter
coordinates supplied. Short point lists are read with zero padding. -/
noncomputable def relativeCoefficientValue (C : Controlled P enc a) (p d u k : α → ℕ)
    (params : α → List ℕ) (w : α) : ℕ :=
  zeroObjectiveCoefficientValue (p w) (n w) (d w) (u w) (k w)
    (fun y => C.evaluate (w, p w, fiberPoint (n w) y (params w)))

/-- Addressed coefficient access raises the source counting level by nine. Only the witness
arity is needed in unary to place the parameter block after it. -/
theorem relativeCoefficientValue_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary)
    {p d u k : α → ℕ} {params : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hu : ComputableInPolyTime u enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hparams : ComputableInPolyTime params enc (encList encNat)) :
    C.relativeCoefficientValue p d u k params ∈ CountingFunction (a + 9) enc encNat := by
  have h := zeroObjectiveCoefficientValue_mem E hp hn hd hu hk
    (fiberEvaluate_mem C hn hp hparams)
  change (fun w => C.relativeCoefficientValue p d u k params w) ∈ _
  simpa only [relativeCoefficientValue] using h

/-- The addressed query gives the evaluation of the actual relative coefficient at the
specified penalty and parameters, provided the prime supports the source and trace evaluators. -/
theorem relativeCoefficientValue_cast (C : Controlled P enc a) (p d u k : α → ℕ)
    (params : α → List ℕ) (w : α) (hp : (p w).Prime) (hcut : C.cutoff w < p w)
    (hd : 1 ≤ d w) (hdeg : (P w).totalDegree ≤ d w + 1)
    (hgrid : (d w + 1) * ((d w + 1) ^ n w * (d w + 2) + n w * d w + 1) + 1 < p w)
    (hsize : (d w + 1) ^ n w * (d w + 1) ^ n w < p w - 1) :
    (C.relativeCoefficientValue p d u k params w : ZMod (p w)) =
      eval₂ (Int.castRingHom (ZMod (p w)))
        (fun i : Option (Fin (m w)) => i.elim (u w : ZMod (p w))
          (fun j => (((params w)[j.val]?.getD 0 : ℕ) : ZMod (p w))))
        ((relativeValuePolynomial (by omega : 1 ≤ d w + 1)
          (rename finSumFinEquiv.symm (P w)) ((totalDegree_rename_le _ _).trans hdeg)).coeff
          (k w)) := by
  let : Fact (p w).Prime := ⟨hp⟩
  let φ := Int.castRingHom (ZMod (p w))
  let F := rename finSumFinEquiv.symm (P w)
  let z : Fin (m w) → ZMod (p w) := fun i => (((params w)[i.val]?.getD 0 : ℕ) : ZMod (p w))
  let fiber := (sumRingEquiv ℤ (Fin (n w)) (Fin (m w)) F).map (eval₂Hom φ z)
  have hF : F.totalDegree ≤ d w + 1 := (totalDegree_rename_le _ _).trans hdeg
  have hfiber : fiber.totalDegree ≤ d w + 1 :=
    (totalDegree_map_le _ _).trans ((totalDegree_sumRingEquiv_le F).trans hF)
  have hcoeff := zeroObjectiveCoefficientValue_eq (d w) hd (u w) (k w) fiber hfiber hgrid hsize
    (fun y => C.evaluate (w, p w, fiberPoint (n w) y (params w))) (by
      intro y
      rw [C.evaluate_eq w (p w) _ hp hcut, evaluation, ZMod.natCast_zmod_val]
      exact eval_fiberPoint (P w) φ y (params w))
  have hmap := relativeValuePolynomial_map (by omega : 1 ≤ d w + 1) F hF (u w : ZMod (p w)) z
  have hk := congrArg (fun Q : Polynomial (ZMod (p w)) => Q.coeff (k w)) hmap
  rw [Polynomial.coeff_map] at hk
  rw [relativeCoefficientValue, hcoeff, ZMod.natCast_zmod_val]
  exact hk.symm

end Cslib.Complexity.RealAlgebraic.Controlled
