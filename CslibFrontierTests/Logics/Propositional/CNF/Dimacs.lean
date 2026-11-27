/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Logics.Propositional.CNF.Dimacs
import CslibFrontier.Logics.Propositional.Pigeonhole

/-!
# Reading and writing DIMACS CNF

A file with comments, a clause split across lines and the SATLIB ending `%` is read with the
DIMACS variable `v` as the variable `v - 1`. Reading what `CNF.toDIMACS` writes gives the formula
back, on PHP(4, 3) and on formulas with an empty clause and a repeated literal. Malformed files
are rejected: no header, a literal beyond the header's variables, a wrong number of clauses, an
unterminated clause, and a token that is not an integer.
-/

set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.CNF.Dimacs

open Cslib.Logic.PL

-- Comments, a clause across two lines, and the SATLIB ending.
#guard CNF.ofDIMACS "c a comment\np cnf 3 2\n 1 -3 0\n2\n3 -1 0\n%\n0\n" =
  .ok [[(0, true), (2, false)], [(1, true), (2, true), (0, false)]]

/-- PHP(4, 3) with the variable of pigeon `i` in hole `j` as `3 * i + j`. -/
private def php43 : CNF ℕ := (CNF.pigeonhole 4 3).relabel fun x => 3 * x.1.val + x.2.val

-- Reading what is written gives the formula back.
#guard CNF.ofDIMACS php43.toDIMACS = .ok php43

#guard CNF.ofDIMACS (CNF.toDIMACS [[(0, true), (0, true)], [], [(4, false)]]) =
  .ok [[(0, true), (0, true)], [], [(4, false)]]

-- The written header: one more variable than the greatest, and the number of clauses.
#guard (CNF.toDIMACS [[(0, true), (2, false)]]).startsWith "p cnf 3 1\n"

-- Malformed files.
#guard (CNF.ofDIMACS "1 2 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 3 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 2\n1 2 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 2\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 x 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2\n1 2 0\n").toOption.isNone

end CslibFrontierTests.Logics.Propositional.CNF.Dimacs
