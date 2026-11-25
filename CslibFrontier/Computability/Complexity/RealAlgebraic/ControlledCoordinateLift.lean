/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import Mathlib.Algebra.MvPolynomial.Rename
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-!
# Controlled tests on a selected coordinate

A controlled polynomial in one variable lifts to a selected coordinate of a larger point.
The evaluator reads that coordinate from the input list, with zero padding, and passes a
singleton list to the original evaluator. Degree, norm, cutoff and counting level are preserved
as bounds. Adapted from `ControlledCoordinateLift` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial

/-- Place a controlled one-variable polynomial at a binary-addressed coordinate without
increasing its evaluation level or polynomial bounds. -/
noncomputable def onCoordinate {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : α → MvPolynomial (Fin 1) ℤ} (C : Controlled P enc a)
    (hn : ComputableInPolyTime n enc encUnary) (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    Controlled (fun w => MvPolynomial.rename (fun _ : Fin 1 => i w) (P w)) enc a where
  arity_computable := hn
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := (MvPolynomial.totalDegree_rename_le _ _).trans (C.degree_le w)
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (MvPolynomial.coeffNorm1_rename_le _ _).trans (C.mass_le w)
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate := fun (w, p, z) => C.evaluate (w, p, [z.getD (i w).val 0])
  evaluate_mem := by
    let args := encPair encNat (encList encNat)
    have hw := fst enc args
    have hargs := snd enc args
    have hp := (fst encNat (encList encNat)).comp hargs
    have hz := (snd encNat (encList encNat)).comp hargs
    have hread := listGetD_binary (encA := encNat) 0 hz (hi.comp hw)
    have hpoint := (cons encNat).comp (hread.prod (.const []))
    exact CountingFunction.preprocess C.evaluate_mem (hw.prod (hp.prod hpoint))
  evaluate_eq w p z hp hcut := by
    change C.evaluate (w, p, [z.getD (i w).val 0]) = _
    rw [C.evaluate_eq w p _ hp hcut]
    simp only [evaluation, MvPolynomial.eval₂_rename]
    congr 2
    funext j
    rw [Fin.eq_zero j]
    simp only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some, Function.comp_apply,
      List.getD_eq_getElem?_getD]

end Cslib.Complexity.RealAlgebraic.Controlled
