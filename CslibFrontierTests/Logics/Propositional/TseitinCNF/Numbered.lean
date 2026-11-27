/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.TseitinCNF.Numbered
import Mathlib.Data.Fintype.Pi

/-!
# The Tseitin transformation with numbered variables

Over the atoms `p = 0` and `q = 1`, the conjunction `p ∧ q` is the variable `2`, and its
transformation is the unit clause for `2` and the three definitional clauses, newest first. In
`(p ∧ p) ∨ (p ∧ p)` the two equal conjunctions get the different numbers `2` and `3`, which the
renaming sends to the same variable of the Tseitin transformation. The transformation of the negated
contraposition is unsatisfiable.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.TseitinCNF.Numbered

open Cslib.Logic.PL Cslib.Logic.PL.Proposition

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

example : (Proposition.and p q).tseitinNumberedCNF =
    [[(2, true)], [(2, false), (0, true)], [(2, false), (1, true)],
      [(2, true), (0, false), (1, false)]] := rfl

-- Equal subformulas get different numbers, renamed to the same Tseitin variable.
example : (Proposition.or (.and p p) (.and p p)).tseitinNumberedCNF.length = 10 := rfl

example : (Proposition.or (.and p p) (.and p p)).tseitinNumberedVar 2 =
    (Proposition.or (.and p p) (.and p p)).tseitinNumberedVar 3 := rfl

example : ¬ (neg contraposition).tseitinNumberedCNF.Satisfiable := by
  rw [satisfiable_tseitinNumberedCNF_iff]
  decide

example : (neg (.imp p q)).tseitinNumberedCNF.Satisfiable := by
  rw [satisfiable_tseitinNumberedCNF_iff]
  decide

example : (neg contraposition).tseitinNumberedCNF.length ≤ 3 * (neg contraposition).size + 1 :=
  length_tseitinNumberedCNF_le _

end CslibFrontierTests.Logics.Propositional.TseitinCNF.Numbered
