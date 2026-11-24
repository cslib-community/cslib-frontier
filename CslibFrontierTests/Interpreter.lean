/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Foundations.FieldTheory.FiniteOfFiniteType
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Machine
import Mathlib.Algebra.Field.ZMod

/-! Tests of the first interpreter layer: finiteness of fields of finite type over `ℤ`, and
deterministic evaluation of small formulas. -/

namespace CslibFrontierTests.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter

/-- `ℤ` is a Jacobson ring. -/
example : IsJacobsonRing ℤ := inferInstance

/-- `ZMod 3` is of finite type over `ℤ` (the cast is onto), hence finite. -/
example : Finite (ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Cslib.finite_of_finiteType_int (ZMod 3)
    (RingHom.FiniteType.of_surjective (Int.castRingHom (ZMod 3)) ZMod.intCast_surjective)

variable {A : Type} [CommRing A] (θ : List Bool → A)

/-- Swapping the two halves of a pair: `(tl id, hd id)` at `(a, b)` is `(b, a)`, in `5` steps. -/
example (a b : Tree) :
    Dt θ (.cons (.tl .id) (.hd .id)) (.cons a b) (.cons b a) (2 + 2 + 1) :=
  Dt.cons (Dt.tl (Dt.id _)) (Dt.hd (Dt.id _))

/-- A quoted tree is its value after one step, whatever the input. -/
example (c x : Tree) : Dt θ (.quote c) x c 1 := Dt.quote c x

end CslibFrontierTests.Interpreter
