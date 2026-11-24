/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Foundations.FieldTheory.FiniteOfFiniteType
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.EvalThm
import Mathlib.Algebra.Field.ZMod

/-! Tests of the first interpreter layer: finiteness of fields of finite type over `ℤ`,
deterministic evaluation of small formulas, and the interpreter theorem on a named
multiplication with a one-unit and an exhausted budget. -/

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

/-! ### The interpreter on a named multiplication -/

/-- `mul (quote nil)` multiplies by the constant named by the empty word, once: its only run has
bill `[[]]`. -/
theorem ev_mulName : Ev θ (Fm.mul (.quote .nil)) .nil [⟨2, 1, [[]], .nil⟩] := by
  exact Ev.mul (Ev.quote .nil .nil)

/-- With one unit of budget for that name, the interpreter has exactly one run: its weight is the
weight `1` of the original run, its bill is empty (the interpreter only names no constants), and
its value is the original value paired with the depleted budget. -/
example : ∃ l', Ev θ IF (env (Fm.mul (.quote .nil)).code .nil (.leaf [true])) l' ∧
    ∃ r, l' = [r] ∧ r.th = 1 ∧ r.bill = [] ∧ r.out = .cons .nil (Bt.leaf [false]).enc := by
  obtain ⟨l', hl', hr⟩ := interp (H := 2) (ev_mulName θ) _ (Fm.ofTree_code _) (.leaf [true])
    (by decide)
  have hs : simS (.leaf [true]) [(⟨2, 1, [[]], .nil⟩ : Run A)] =
      [⟨⟨2, 1, [[]], .nil⟩, .leaf [false]⟩] := rfl
  rw [hs] at hr
  obtain ⟨r, u, hr1, hu, e⟩ := List.forall₂_cons_right_iff.1 hr
  rw [List.forall₂_nil_right_iff] at hu
  subst hu
  exact ⟨l', hl', r, e, hr1.th, hr1.bill, hr1.out⟩

/-- With an exhausted budget, the interpreter rejects: it has no accepting run. -/
example : Ev θ IF (env (Fm.mul (.quote .nil)).code .nil (.leaf [false])) [] := by
  obtain ⟨l', hl', hr⟩ := interp (H := 2) (ev_mulName θ) _ (Fm.ofTree_code _) (.leaf [false])
    (by decide)
  have hs : simS (.leaf [false]) [(⟨2, 1, [[]], .nil⟩ : Run A)] = [] := rfl
  rw [hs, List.forall₂_nil_right_iff] at hr
  exact hr ▸ hl'

end CslibFrontierTests.Interpreter
