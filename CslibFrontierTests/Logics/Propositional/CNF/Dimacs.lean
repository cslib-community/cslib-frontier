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
back (`CNF.ofDIMACS_toDIMACS`), run here on PHP(4, 3) and on formulas with an empty clause and a
repeated literal. Windows line endings are read. Numbers are read as `String.toNat?` and
`String.toInt?` read them, `_` digit separators included, in the header and in the clauses.
Malformed files are rejected: no header, a literal beyond the header's variables, a wrong number
of clauses, an unterminated clause, a token that is not an integer, and misplaced separators.
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

-- Windows line endings.
#guard CNF.ofDIMACS "p cnf 2 1\r\n1 -2 0\r\n" = .ok [[(0, true), (1, false)]]

-- The written text: the header gives one more variable than the greatest, and the number of
-- clauses.
#guard CNF.toDIMACS [[(0, true), (2, false)], []] = "p cnf 3 2\n1 -3 0\n0\n"
#guard CNF.toDIMACS [] = "p cnf 0 0\n"

#guard (CNF.toDIMACS [[(0, true), (2, false)]]).startsWith "p cnf 3 1\n"

-- Digit separators, as `String.toNat?` and `String.toInt?` read them: in the header and in a
-- clause.
#guard CNF.ofDIMACS "p cnf 1_0 1\n10 0\n" = .ok [[(9, true)]]
#guard CNF.ofDIMACS "p cnf 10 1\n-1_0 0\n" = .ok [[(9, false)]]
example : Dimacs.header? [['p'], ['c', 'n', 'f'], ['1', '_', '0'], ['1']] = some (10, 1) := by
  decide
example : Dimacs.intOfChars? ['-', '1', '_', '0'] = some (-10) := by decide

-- The number readers agree with `String.toNat?` and `String.toInt?`.
#guard ["0", "7", "007", "10", "1_0", "1_000_000", "", "_", "_1", "1_", "1__0", "-1", "+1",
  "1a", "-", "-0_1", "-_1", "--1", "1-"].all fun t =>
    Dimacs.natOfChars? t.toList == t.toNat? && Dimacs.intOfChars? t.toList == t.toInt?

-- Malformed files.
#guard (CNF.ofDIMACS "1 2 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 3 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 2\n1 2 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 2\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2 1\n1 x 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 2\n1 2 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 10_ 1\n1 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 10 1\n-_1 0\n").toOption.isNone
#guard (CNF.ofDIMACS "p cnf 10 1\n1__0 0\n").toOption.isNone

end CslibFrontierTests.Logics.Propositional.CNF.Dimacs
