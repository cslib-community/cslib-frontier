/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF.Numbered
import Mathlib.Data.Fintype.Pi

/-!
# The Plaisted–Greenbaum transformation with numbered variables

Over the atoms `p = 0` and `q = 1`, the conjunction `p ∧ q` is the variable `2`, and its
transformation is the unit clause for `2` and the two clauses saying that `2` implies `p` and `q`.
In `(p ∧ q) → p` the conjunction is an antecedent, so it is negative and keeps only the clause
saying that `p ∧ q` implies its variable, while the implication keeps the clause saying that its
variable implies it. `⊥` has a clause only at positive polarity. In `(p ∧ p) ∨ (p ∧ p)` the two
equal conjunctions get the different numbers `2` and `3`, which the renaming sends to the same
variable of the Plaisted–Greenbaum transformation. The transformation of the negated
contraposition has 12 clauses against 22 for the Tseitin transformation, and is unsatisfiable.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF.Numbered

open Cslib.Logic.PL Cslib.Logic.PL.Proposition

private abbrev p : Proposition (Fin 2) := .atom 0
private abbrev q : Proposition (Fin 2) := .atom 1

/-- Negation, written with the constructors. -/
private abbrev neg (A : Proposition (Fin 2)) : Proposition (Fin 2) := .imp A .falsum

/-- Contraposition, `(p → q) → ¬q → ¬p`. -/
private abbrev contraposition : Proposition (Fin 2) := .imp (.imp p q) (.imp (neg q) (neg p))

example : (Proposition.and p q).plaistedGreenbaumNumberedCNF =
    [[(2, true)], [(2, false), (0, true)], [(2, false), (1, true)]] := rfl

-- The antecedent `p ∧ q` is negative: it keeps the clause `p ∧ q → 2` only.
example : (Proposition.imp (.and p q) p).plaistedGreenbaumNumberedCNF =
    [[(3, true)], [(3, false), (2, false), (0, true)], [(2, true), (0, false), (1, false)]] := rfl

-- `⊥` at negative polarity has no clause; at positive polarity it has the unit clause `¬x`.
example : (neg (neg p)).plaistedGreenbaumNumberedCNF =
    [[(5, true)], [(5, false), (3, false), (4, true)], [(4, false)],
      [(3, true), (0, true)], [(3, true), (2, false)]] := by decide +kernel

-- Equal subformulas get different numbers, renamed to the same variable.
example : (Proposition.or (.and p p) (.and p p)).plaistedGreenbaumNumberedCNF.length = 6 := rfl

example : (Proposition.or (.and p p) (.and p p)).plaistedGreenbaumNumberedVar 2 =
    (Proposition.or (.and p p) (.and p p)).plaistedGreenbaumNumberedVar 3 := rfl

example : (neg contraposition).plaistedGreenbaumNumberedCNF.length = 12 ∧
    (neg contraposition).tseitinCNF.length = 22 := by decide +kernel

example : ¬ (neg contraposition).plaistedGreenbaumNumberedCNF.Satisfiable := by
  rw [satisfiable_plaistedGreenbaumNumberedCNF_iff]
  decide

example : (neg (.imp p q)).plaistedGreenbaumNumberedCNF.Satisfiable := by
  rw [satisfiable_plaistedGreenbaumNumberedCNF_iff]
  decide

example : (neg contraposition).plaistedGreenbaumNumberedCNF.length ≤
    2 * (neg contraposition).size + 1 :=
  length_plaistedGreenbaumNumberedCNF_le _

end CslibFrontierTests.Logics.Propositional.PlaistedGreenbaumCNF.Numbered
