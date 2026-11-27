/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.LRATFile
public meta import CslibFrontier.Logics.Propositional.CNF.LRATFile

/-!
# The LRAT file checker

The four clauses over two variables, written in DIMACS by `CNF.toDIMACS`, are refuted by a text
LRAT proof with a RAT step on a fresh variable, the refutation of the tests of `CNF.checkLRATRat`.
The file checker accepts it, which shows the formula unsatisfiable through
`CNF.not_satisfiable_of_checkDIMACSLRAT`. It rejects a proof that does not reach the empty clause,
a proof it cannot parse, and a formula whose header disagrees with its clauses.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.CNF.LRATFile

open Cslib.Logic.PL

/-- Every clause over two variables, in DIMACS. -/
private def cnf : String :=
  CNF.toDIMACS [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation through the fresh variable `3`, as a text LRAT file. -/
private def proof : String := "5 3 0 0\n6 -3 1 0 -5 1 2 0\n7 1 0 6 5 0\n8 0 7 3 4 0\n"

#guard CNF.checkDIMACSLRAT cnf proof.toUTF8 matches .ok ()

-- The same proof without its empty-clause step.
#guard CNF.checkDIMACSLRAT cnf "5 3 0 0\n6 -3 1 0 -5 1 2 0\n7 1 0 6 5 0\n".toUTF8 matches .error _

-- A proof that does not parse.
#guard CNF.checkDIMACSLRAT cnf "5 3 x 0\n".toUTF8 matches .error _

-- A header announcing more clauses than the file has.
#guard CNF.checkDIMACSLRAT "p cnf 2 5\n1 0\n" proof.toUTF8 matches .error _

end CslibFrontierTests.Logics.Propositional.CNF.LRATFile
