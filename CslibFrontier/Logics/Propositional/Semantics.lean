/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Logics.Propositional.Defs
public import Mathlib.Order.BooleanAlgebra.Defs

/-! # Algebraic semantics of propositions

A valuation `v : Atom → α` of the atoms in a Heyting algebra `α` extends to every proposition
(`Cslib.Logic.PL.Proposition.eval`): falsum is `⊥`, conjunction is `⊓`, disjunction is `⊔` and
implication is the Heyting implication `⇨`. Negation `¬A`, defined as `A → ⊥`, is then the
pseudo-complement `A ⇨ ⊥`. Heyting algebras are the algebraic models of intuitionistic
propositional logic and Boolean algebras those of classical logic.

Truth tables are the instance `α = Bool`, whose equations are the `Bool` simp lemmas below.
Mathlib's `Prop` is another instance: a Heyting algebra constructively and a Boolean algebra
classically. The soundness of Frege proofs (`Cslib.Logic.PL.Frege.IsProof.eval`) and the Tseitin
transformation (`Cslib.Logic.PL.Proposition.tseitinCNF`) are stated with the `Bool` instance.

## Main definitions

* `Cslib.Logic.PL.Proposition.eval`: the value of a proposition under a valuation of its atoms.
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

variable {Atom α : Type*}

/-- The value of a proposition in a Heyting algebra under a valuation `v` of its atoms. -/
def eval [HeytingAlgebra α] (v : Atom → α) : Proposition Atom → α
  | atom x => v x
  | falsum => ⊥
  | and A B => A.eval v ⊓ B.eval v
  | or A B => A.eval v ⊔ B.eval v
  | imp A B => A.eval v ⇨ B.eval v

/-! ### Truth tables -/

section Bool

variable (v : Atom → Bool) (A B : Proposition Atom)

@[simp] theorem eval_atom_bool (x : Atom) : (atom x).eval v = v x := rfl

@[simp] theorem eval_falsum_bool : (falsum : Proposition Atom).eval v = false := rfl

@[simp] theorem eval_bot_bool : (⊥ : Proposition Atom).eval v = false := rfl

@[simp] theorem eval_and_bool : (and A B).eval v = (A.eval v && B.eval v) := rfl

@[simp] theorem eval_or_bool : (or A B).eval v = (A.eval v || B.eval v) := rfl

@[simp] theorem eval_imp_bool : (imp A B).eval v = (!A.eval v || B.eval v) := by
  simp only [eval, himp_eq, Bool.compl_eq_bnot, Bool.sup_eq_bor, Bool.or_comm]

end Bool

end Cslib.Logic.PL.Proposition
