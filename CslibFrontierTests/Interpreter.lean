/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Foundations.FieldTheory.FiniteOfFiniteType
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.EvalThm
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Comp
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Parts
import Mathlib.Algebra.Field.ZMod

/-! Tests of the first interpreter layer: finiteness of fields of finite type over `ℤ`,
deterministic evaluation of small formulas, and the interpreter theorem on a named
multiplication with a one-unit and an exhausted budget; budgets of constants, and the
compositional rules for weighted values; the program library of lists, tries and terms. -/

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

/-! ### Budgets of constants -/

/-- One unit of budget allows one use of the name, not two. -/
example : ok (.leaf [true]) [[]] = true ∧ ok (.leaf [true]) [[], []] = false := by decide

/-- With one digit, a constant `c` has the budgets `0` and `1`, with weights `c ^ 0` and `c ^ 1`. -/
example {R : Type} [CommRing R] (c : R) :
    (KT.leaf c).budg 1 = [(.leaf [false], c ^ 0), (.leaf [true], c ^ 1)] := by rfl

/-- The power `2 ^ 2` of a constant is named `1 1 0`. -/
example {R : Type} [CommRing R] (c : R) : KT.combVal c (KT.pw 2) = c ^ 4 := KT.combVal_pw c 2

/-! ### Weighted values of formulas -/

/-- A condition with a nonempty value selects the first branch. -/
example (x : Tree) :
    Gives θ (.ite (.quote (.cons .nil .nil)) .id (.quote .nil)) x x (1 + 1 + 1) :=
  Does.ite_true (Gives.quote _ _) (by simp) (Gives.id x)

/-- `hd` of a pair, then the first component: the value is computed step by step. -/
example (a b : Tree) : Gives θ (.hd (.cons (.quote a) (.quote b))) .nil a (1 + 1 + 1 + 1) :=
  Gives.hd (Gives.cons (Gives.quote a _) (Gives.quote b _))

/-! ### The program library -/

/-- A trie returns the value written at a path, and the empty tree at another path. -/
example (c : Tree) : tget [true] (tset [true] c .nil) = c ∧ tget [false] (tset [true] c .nil) =
    .nil := by
  simp [tget_tset, tget_nil]

/-- Equality of a tree with itself has the value `1`. -/
example (a x : Tree) : Gives θ (eqF (.quote a) (.quote a)) x (Tree.bit (decide (a = a)))
    (1 + 1 + 60 * a.size + 10) :=
  eqF_gives (Gives.quote a x) (Gives.quote a x)

/-- A term for `1 + c`, where `c` is the constant named by the empty word. -/
example : (WE.add .one (.nm [])).val θ = 1 + θ [] := by rfl

/-- There are four bit lists of length two. -/
example : (allBits 2).length = 4 := by decide

end CslibFrontierTests.Interpreter
