/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.TseitinCNF
import Mathlib.Data.Fintype.Pi

/-!
# The Tseitin transformation of a proposition

The transformation of `p ∧ q` is written out in full: the unit clause for the variable of the
conjunction and its three definitional clauses. Contraposition `(p → q) → ¬q → ¬p` is a
tautology, so the transformation of its negation is unsatisfiable; `p → q` is not, so the
transformation of its negation is satisfiable. Both are decided through
`satisfiable_tseitinCNF_iff` by enumerating the four valuations of two atoms.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.TseitinCNF

open Cslib.Logic.PL Cslib.Logic.PL.Proposition

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

example : (Proposition.and p q).tseitinCNF =
    [[(.inr (.and p q), true)],
      [(.inr (.and p q), false), (.inl 0, true)],
      [(.inr (.and p q), false), (.inl 1, true)],
      [(.inr (.and p q), true), (.inl 0, false), (.inl 1, false)]] := rfl

-- One unit clause, three clauses per binary connective and one per occurrence of `⊥`.
example : (neg contraposition).tseitinCNF.length = 22 := by decide

example : (neg contraposition).tseitinCNF.length ≤ 3 * (neg contraposition).size + 1 :=
  length_tseitinCNF_le _

-- The negation of a tautology has an unsatisfiable transformation.
example : ¬ (neg contraposition).tseitinCNF.Satisfiable := by
  rw [satisfiable_tseitinCNF_iff]
  decide

-- The negation of a non-tautology has a satisfiable transformation.
example : (neg (.imp p q)).tseitinCNF.Satisfiable := by
  rw [satisfiable_tseitinCNF_iff]
  decide

-- A model of the transformation restricts to a model of the proposition: `p ∧ q` holds at the
-- atoms of the extension of the valuation making both true.
example : (Proposition.and p q).tseitinCNF.eval (tseitinExtend fun _ => true) = true := by
  rw [eval_tseitinCNF_tseitinExtend]
  rfl

-- Two models of the transformation of `p ∧ q` that agree on the atoms agree on the variable of
-- the conjunction.
example {σ τ : Fin 2 ⊕ Proposition (Fin 2) → Bool} (hσ : (Proposition.and p q).tseitinCNF.eval σ)
    (hτ : (Proposition.and p q).tseitinCNF.eval τ) (hatoms : σ ∘ Sum.inl = τ ∘ Sum.inl) :
    σ (.inr (.and p q)) = τ (.inr (.and p q)) :=
  eq_of_eval_tseitinCNF hσ hτ hatoms
    (CNF.mem_vars.2 ⟨_, List.mem_cons_self, true, List.mem_singleton_self _⟩)

end CslibFrontierTests.Logics.Propositional.TseitinCNF
