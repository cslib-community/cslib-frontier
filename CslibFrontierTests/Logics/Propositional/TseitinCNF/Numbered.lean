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
# The Tseitin and Plaisted–Greenbaum transformations with numbered variables

Over the atoms `p = 0` and `q = 1`, the conjunction `p ∧ q` is the variable `2`, and its
transformation is the unit clause for `2` and the three definitional clauses, newest first. In
`(p ∧ p) ∨ (p ∧ p)` the two equal conjunctions get the different numbers `2` and `3`, which the
renaming sends to the same variable of the Tseitin transformation. The transformation of the negated
contraposition is unsatisfiable.

The Plaisted–Greenbaum transformation of `p ∧ q` keeps only the two clauses saying that `2`
implies `p` and `q`. In `(p ∧ q) → p` the conjunction is an antecedent, so it is negative and keeps
only the clause saying that `p ∧ q` implies its variable, while the implication keeps the clause
saying that its variable implies it. The Plaisted–Greenbaum transformation of the negated
contraposition has 12 clauses against 22 for the Tseitin transformation, and is also unsatisfiable.
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

/-! ### The Plaisted–Greenbaum transformation -/

example : (Proposition.and p q).plaistedGreenbaumNumberedCNF =
    [[(2, true)], [(2, false), (0, true)], [(2, false), (1, true)]] := rfl

-- The antecedent `p ∧ q` is negative: it keeps the clause `p ∧ q → 2` only.
example : (Proposition.imp (.and p q) p).plaistedGreenbaumNumberedCNF =
    [[(3, true)], [(3, false), (2, false), (0, true)], [(2, true), (0, false), (1, false)]] := rfl

-- `⊥` at negative polarity has no clause; at positive polarity it has the unit clause `¬x`.
example : (neg (neg p)).plaistedGreenbaumNumberedCNF =
    [[(5, true)], [(5, false), (3, false), (4, true)], [(4, false)],
      [(3, true), (0, true)], [(3, true), (2, false)]] := by decide +kernel

example : (neg contraposition).plaistedGreenbaumNumberedCNF.length = 12 ∧
    (neg contraposition).tseitinNumberedCNF.length = 22 := by decide +kernel

-- Every clause is a clause of the numbered Tseitin transformation.
example : (neg contraposition).plaistedGreenbaumNumberedCNF.all
    ((neg contraposition).tseitinNumberedCNF.contains ·) = true := by decide +kernel

example : ¬ (neg contraposition).plaistedGreenbaumNumberedCNF.Satisfiable := by
  rw [satisfiable_plaistedGreenbaumNumberedCNF_iff]
  decide

example : (neg (.imp p q)).plaistedGreenbaumNumberedCNF.Satisfiable := by
  rw [satisfiable_plaistedGreenbaumNumberedCNF_iff]
  decide

example : (neg contraposition).plaistedGreenbaumNumberedCNF.length ≤
    2 * (neg contraposition).size + 1 :=
  length_plaistedGreenbaumNumberedCNF_le _

end CslibFrontierTests.Logics.Propositional.TseitinCNF.Numbered
