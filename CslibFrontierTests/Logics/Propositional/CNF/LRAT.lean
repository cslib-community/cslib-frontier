/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Logics.Propositional.CNF.LRAT
import CslibFrontier.Logics.Propositional.CNF.StdSat
import Std.Tactic.BVDecide.LRAT.Checker

/-!
# The LRAT checker

The four clauses over the variables `a = 0` and `b = 1` (DIMACS `1` and `2`), numbered `1` to `4`,

  `a ∨ b`, `a ∨ ¬b`, `¬a ∨ b`, `¬a ∨ ¬b`,

are refuted in two steps. Clause `5`, `a`, is a RUP clause: from `¬a`, clause `1` forces `b` and
then clause `2` is false. The empty clause follows: clause `5` forces `a`, then clause `3` forces
`b`, and clause `4` is false. The kernel checks the certificate with `decide`, and Lean core's
checker accepts it too. The hints `3, 4` alone do not refute the formula, since clause `3` has two
unassigned literals, and the checker rejects them; so does a certificate that ends before the
empty clause.
-/

namespace CslibFrontierTests.Logics.Propositional.CNF.LRAT

open Cslib.Logic.PL Std.Tactic.BVDecide

/-- Every clause over two variables. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

example : φ.checkLRAT cert = true := by decide

example : ¬ φ.Satisfiable := CNF.not_satisfiable_of_checkLRAT (cert := cert) (by decide)

-- Lean core's checker accepts the same certificate.
/-- info: true -/
#guard_msgs in
#eval LRAT.check cert φ.toStdSat

-- Hints that do not propagate to a conflict are rejected.
example : φ.checkLRAT #[.addEmpty 5 #[3, 4]] = false := by decide

-- A certificate must end with the empty clause.
example : φ.checkLRAT #[.addRup 5 #[1] #[1, 2]] = false := by decide

-- RAT steps are rejected.
example : φ.checkLRAT #[.addRat 5 #[1] (0, true) #[] #[], .addEmpty 6 #[5, 3, 4]] = false := by
  decide

end CslibFrontierTests.Logics.Propositional.CNF.LRAT
