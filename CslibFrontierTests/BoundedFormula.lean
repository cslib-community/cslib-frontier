/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula.Bounded

open Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.LocalValueGame.FormulaExpansion

private def conjunction : BoundedFormula 2 1 :=
  ⟨(Formula.input 0).and (.input 1), by decide⟩

example : (BoundedFormula.child conjunction false).val = .input 0 := rfl
example : (BoundedFormula.child conjunction true).val = .input 1 := rfl

private def negated : BoundedFormula 2 2 := ⟨conjunction.val.not, by decide⟩

-- Negation follows its only child even when the chosen Boolean branch is true.
example (b : Bool) : (BoundedFormula.child negated b).val = conjunction.val := rfl

-- Constants and input ports remain local leaves for the enclosing macro router.
example (b : Bool) : (BoundedFormula.child
    (⟨Formula.const true, by decide⟩ : BoundedFormula 0 1) b).val = Formula.const true := rfl

example (b : Bool) : BoundedFormula.operation
    (BoundedFormula.child (⟨Formula.input 1, by decide⟩ : BoundedFormula 2 0) b) = .inl 1 := rfl

example : IsEmpty (BoundedFormula 0 0) := by
  refine ⟨fun ⟨f, h⟩ => ?_⟩
  cases f with
  | input i => exact Fin.elim0 i
  | gate op args => simp [Formula.depth] at h
