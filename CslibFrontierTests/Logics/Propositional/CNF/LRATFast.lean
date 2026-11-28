/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.LRATFast
public meta import CslibFrontier.Logics.Propositional.CNF.LRATFast
public meta import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# The array-based LRAT checker

The compiled checker accepts CaDiCaL's certificate for the pigeonhole formula PHP(5, 4) from the
tests of `CNF.checkLRAT`, and rejects each failing certificate of those tests: hints that do not
propagate to a conflict, a certificate without an empty-clause step, a RAT step without the hints
its candidates need, a hint naming a deleted clause or no clause, and a RUP step whose hint leaves
two literals open.

The checker reuses one assignment for all steps, so a step must not see the literals assigned by
an earlier one. Two satisfiable formulas have certificates that an implementation which did not
reset its assignment would accept: one where a step relies on a literal propagated by the previous
step, and one where it relies on the negation of the clause the previous step added.

The reference checker's trail can hold both polarities of a variable, when the added clause
contains a literal and its negation; both literals are then false. The array-based checker
agrees, which an assignment holding one value per variable would not. Reusing a clause number
shadows the earlier clause, and deleting an absent number does nothing, in both checkers.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.CNF.LRATFast

open Cslib.Logic.PL Std.Tactic.BVDecide
open CslibFrontierTests.Logics.Propositional.CNF.LRAT (php phpCert)

/-- info: true -/
#guard_msgs in
#eval php.checkLRATFast phpCert

/-- Every clause over two variables, as in the tests of `CNF.checkLRAT`. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

#guard φ.checkLRATFast cert

-- A repeated literal counts once.
#guard CNF.checkLRATFast [[(0, true), (0, true)], [(0, false)]] #[.addEmpty 3 #[1, 2]]

-- The steps after an accepted empty-clause step are not read.
#guard φ.checkLRATFast (cert ++ #[.addRat 7 #[1] (0, true) #[] #[]])

/-! Each failing case of the tests of `CNF.checkLRAT` is rejected. -/

-- Hints that do not propagate to a conflict.
#guard !φ.checkLRATFast #[.addEmpty 5 #[3, 4]]

-- A certificate that does not reach an empty-clause step.
#guard !φ.checkLRATFast #[.addRup 5 #[1] #[1, 2]]

-- A RAT step on `a` whose candidates `¬a ∨ b` and `¬a ∨ ¬b` have no RAT hints.
#guard !φ.checkLRATFast #[.addRat 5 #[1] (0, true) #[] #[], .addEmpty 6 #[5, 3, 4]]

-- A hint naming a deleted clause.
#guard !φ.checkLRATFast #[.del #[1], .addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

-- A hint naming no clause.
#guard !φ.checkLRATFast #[.addEmpty 5 #[9]]

-- A RUP step whose hint leaves two literals open.
#guard !φ.checkLRATFast #[.addRup 5 #[1] #[3], .addEmpty 6 #[5, 3, 4]]

/-! Each step starts from an empty assignment. -/

/-- The satisfiable formula `a ∨ b`, `a ∨ ¬b`, `¬b`. -/
private abbrev ψ : CNF ℕ := [[(0, true), (1, true)], [(0, true), (1, false)], [(1, false)]]

/-- Clause `4`, `a`, is a RUP clause: from `¬a`, clause `1` forces `b`, which falsifies clause `2`.
Without a reset, `b` would still be true in the next step and falsify clause `3`. -/
private abbrev staleUnit : Array LRAT.IntAction :=
  #[.addRup 4 #[1] #[1, 2], .addEmpty 5 #[3]]

example : ψ.checkLRAT staleUnit = false := by decide

#guard !ψ.checkLRATFast staleUnit

/-- The satisfiable formula `a ∨ b`, `a ∨ ¬b`. -/
private abbrev χ : CNF ℕ := [[(0, true), (1, true)], [(0, true), (1, false)]]

/-- Clause `3`, `a`, is a RUP clause as above. Without a reset, `¬a` would still be true in the
next step, so that clause `1` forces `b` and clause `2` is false. -/
private abbrev staleNegation : Array LRAT.IntAction :=
  #[.addRup 3 #[1] #[1, 2], .addEmpty 4 #[1, 2]]

example : χ.checkLRAT staleNegation = false := by decide

#guard !χ.checkLRATFast staleNegation

/-! Edge cases of the reference checker. -/

/-- The clause `a ∨ ¬a` is added with hint `1`: both `¬a` and `a` are assumed, so the clause `a`
has no literal left, and the step is accepted. -/
private abbrev tautology : Array LRAT.IntAction :=
  #[.addRup 3 #[1, -1] #[1], .addEmpty 4 #[1, 2]]

example : CNF.checkLRAT [[(0, true)], [(0, false)]] tautology = true := by decide

#guard CNF.checkLRATFast [[(0, true)], [(0, false)]] tautology

/-- Clause `1`, `a ∨ b`, is replaced by the unit clause `a` under the same number, a RUP clause
as in `cert`. The empty clause then uses the new clause `1`, where the old one would leave two
literals open. -/
private abbrev reuse : Array LRAT.IntAction :=
  #[.addRup 1 #[1] #[1, 2], .addEmpty 5 #[1, 3, 4]]

example : φ.checkLRAT reuse = true := by decide

#guard φ.checkLRATFast reuse

-- Deleting an absent clause number does nothing.
example : φ.checkLRAT (#[.del #[7, 1000]] ++ cert) = true := by decide

#guard φ.checkLRATFast (#[.del #[7, 1000]] ++ cert)

end CslibFrontierTests.Logics.Propositional.CNF.LRATFast
