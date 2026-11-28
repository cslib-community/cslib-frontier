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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-!
# Controlled variable renaming

A polynomial-time transformation of evaluation points realizes a variable renaming at
the original counting level. Appending unused variables takes the original list as it is.
Lifting a one-variable polynomial instead reads the addressed value into a singleton list.
Both preserve the degree, coefficient norm and prime cutoff bounds.

Adapted from `ControlledRenaming`, `ControlledAppendVariables` and `ControlledCoordinateLift`
in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial

/-- Rename the variables using a polynomial-time map on zero-padded evaluation points.
The realizing map must agree with the renaming on each original coordinate. -/
noncomputable def rename {α : Type} {n m : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (f : (w : α) → Fin (n w) → Fin (m w)) (point : α × List ℕ → List ℕ)
    (hpoint : ComputableInPolyTime point (encPair enc (encList encNat)) (encList encNat))
    (hlookup : ∀ w z (i : Fin (n w)), (point (w, z)).getD i.val 0 = z.getD (f w i).val 0) :
    Controlled (fun w => MvPolynomial.rename (f w) (P w)) enc a where
  arity_computable := hm
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := (MvPolynomial.totalDegree_rename_le _ _).trans (C.degree_le w)
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (MvPolynomial.coeffNorm1_rename_le _ _).trans (C.mass_le w)
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate := fun (w, p, z) => C.evaluate (w, p, point (w, z))
  evaluate_mem := by
    let args := encPair encNat (encList encNat)
    have hw := fst enc args
    have hargs := snd enc args
    have hp := (fst encNat (encList encNat)).comp hargs
    have hz := (snd encNat (encList encNat)).comp hargs
    exact CountingFunction.preprocess C.evaluate_mem (hw.prod (hp.prod (hpoint.comp (hw.prod hz))))
  evaluate_eq w p z hp hcut := by
    change C.evaluate (w, p, point (w, z)) = _
    rw [C.evaluate_eq w p _ hp hcut]
    simp only [evaluation, MvPolynomial.eval₂_rename]
    congr 2
    funext i
    simp only [Function.comp_apply, ← List.getD_eq_getElem?_getD, hlookup]

/-- Reindexing the evaluation point preserves the source prime cutoff. -/
@[simp] theorem cutoff_rename {α : Type} {n m : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (f : (w : α) → Fin (n w) → Fin (m w)) (point : α × List ℕ → List ℕ)
    (hpoint : ComputableInPolyTime point (encPair enc (encList encNat)) (encList encNat))
    (hlookup : ∀ w z (i : Fin (n w)), (point (w, z)).getD i.val 0 = z.getD (f w i).val 0) :
    (C.rename hm f point hpoint hlookup).cutoff = C.cutoff := by
  simp only [rename]

/-- Append a block of unused variables, preserving the controlled evaluator and its bounds.
The block size is computed in unary, as is the original arity. -/
noncomputable def appendVariables {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (k : α → ℕ) (hk : ComputableInPolyTime k enc encUnary) :
    Controlled (fun w => MvPolynomial.rename (Fin.castAdd (k w)) (P w)) enc a :=
  C.rename (unary_add' C.arity_computable hk) (fun w => Fin.castAdd (k w))
    Prod.snd (snd enc (encList encNat)) (fun _ _ _ => by rw [Fin.val_castAdd])

/-- Place a controlled one-variable polynomial at a binary-addressed coordinate without
increasing its evaluation level or polynomial bounds. -/
noncomputable def onCoordinate {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : α → MvPolynomial (Fin 1) ℤ} (C : Controlled P enc a)
    (hn : ComputableInPolyTime n enc encUnary) (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    Controlled (fun w => MvPolynomial.rename (fun _ : Fin 1 => i w) (P w)) enc a :=
  let hread := listGetD_binary (encA := encNat) 0 (snd enc (encList encNat))
    (hi.comp (fst enc (encList encNat)))
  C.rename hn (fun w _ => i w) (fun (w, z) => [z.getD (i w).val 0])
    ((cons encNat).comp (hread.prod (.const []))) (by
      intro w z j
      rw [Fin.eq_zero j]
      rfl)

section AppendVariables

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  (C : Controlled P enc a) (k : α → ℕ) (hk : ComputableInPolyTime k enc encUnary)

/-- Appending variables preserves the degree bound. -/
@[simp] theorem degreeBound_appendVariables :
    (C.appendVariables k hk).degreeBound = C.degreeBound := by
  simp only [appendVariables, rename]

/-- Appending variables preserves the coefficient norm exponent. -/
@[simp] theorem massExponent_appendVariables :
    (C.appendVariables k hk).massExponent = C.massExponent := by
  simp only [appendVariables, rename]

/-- Appending variables preserves the prime cutoff. -/
@[simp] theorem cutoff_appendVariables :
    (C.appendVariables k hk).cutoff = C.cutoff := by
  simp only [appendVariables, rename]

end AppendVariables

section OnCoordinate

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : α → MvPolynomial (Fin 1) ℤ} (C : Controlled P enc a)
  (hn : ComputableInPolyTime n enc encUnary) (i : (w : α) → Fin (n w))
  (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat)

/-- Lifting to one coordinate preserves the degree bound. -/
@[simp] theorem degreeBound_onCoordinate :
    (C.onCoordinate hn i hi).degreeBound = C.degreeBound := by
  simp only [onCoordinate, rename]

/-- Lifting to one coordinate preserves the coefficient norm exponent. -/
@[simp] theorem massExponent_onCoordinate :
    (C.onCoordinate hn i hi).massExponent = C.massExponent := by
  simp only [onCoordinate, rename]

/-- Lifting to one coordinate preserves the prime cutoff. -/
@[simp] theorem cutoff_onCoordinate :
    (C.onCoordinate hn i hi).cutoff = C.cutoff := by
  simp only [onCoordinate, cutoff_rename]

end OnCoordinate

end Cslib.Complexity.RealAlgebraic.Controlled
