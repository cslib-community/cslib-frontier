/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF
import Mathlib.Data.Fintype.Pi

/-!
# The Plaisted–Greenbaum transformation of a proposition

The transformation of `p ∧ q` keeps two of the three Tseitin clauses of the conjunction: at
positive polarity its variable only has to imply `p` and `q`. On the negated contraposition it has
fewer clauses than the Tseitin transformation and is still unsatisfiable. The extension of a model
is not unique: in `(p ∧ q) ∨ p`, the variable of the positively occurring `p ∧ q` may be false
while `p` and `q` are true, which is a model of the Plaisted–Greenbaum transformation but not of
the Tseitin transformation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF

open Cslib.Logic.PL Cslib.Logic.PL.Proposition

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

example : (Proposition.and p q).plaistedGreenbaumCNF =
    [[(.inr (.and p q), true)],
      [(.inr (.and p q), false), (.inl 0, true)],
      [(.inr (.and p q), false), (.inl 1, true)]] := rfl

-- Twelve clauses against the Tseitin transformation's twenty-two.
example : (neg contraposition).plaistedGreenbaumCNF.length = 12 := by decide

-- The negation of a tautology still has an unsatisfiable transformation.
example : ¬ (neg contraposition).plaistedGreenbaumCNF.Satisfiable := by
  rw [satisfiable_plaistedGreenbaumCNF_iff]
  decide

/-- `(p ∧ q) ∨ p`, where `p ∧ q` occurs positively. -/
private abbrev disj : Proposition (Fin 2) := .or (.and p q) p

/-- The atoms and the disjunction are true, the conjunction's variable is false. -/
private def σ : Fin 2 ⊕ Proposition (Fin 2) → Bool
  | .inr (.and _ _) => false
  | _ => true

-- `σ` is a model of the Plaisted–Greenbaum transformation that differs from the extension of its
-- atoms on a variable of the formula, so it is not a model of the Tseitin transformation.
example : disj.plaistedGreenbaumCNF.eval σ = true := by decide

example : σ (.inr (.and p q)) ≠ tseitinExtend (σ ∘ Sum.inl) (.inr (.and p q)) := by decide

example : disj.tseitinCNF.eval σ = false := by decide

-- In general, models over a nonempty type of atoms are not determined by the atoms.
example : ¬ ∀ (A : Proposition (Fin 2)) (σ τ : Fin 2 ⊕ Proposition (Fin 2) → Bool),
    A.plaistedGreenbaumCNF.eval σ = true → A.plaistedGreenbaumCNF.eval τ = true →
      σ ∘ Sum.inl = τ ∘ Sum.inl → ∀ y ∈ A.plaistedGreenbaumCNF.vars, σ y = τ y :=
  not_forall_eq_of_eval_plaistedGreenbaumCNF

end CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF
