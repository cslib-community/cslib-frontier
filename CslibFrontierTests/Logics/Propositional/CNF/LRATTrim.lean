/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.LRATTrim
public meta import CslibFrontier.Logics.Propositional.CNF.LRATTrim
public meta import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# Trimming and renumbering LRAT certificates

`CNF.trimCert` keeps the steps the first empty clause depends on and drops the deletions, and
`CNF.renumberCert` numbers the added clauses after those of the formula. The checker accepts the
results on CaDiCaL's certificate for PHP(5, 4) from the tests of `CNF.checkLRAT`, and on
certificates that reuse the number of a deleted clause, reuse the number of a clause of the
formula, or delete a number they never added.

The last is the case that renumbering deletions would get wrong: renumbered, the deletion of the
absent number `5` would delete the clause the certificate adds, which is numbered `5` too.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.CNF.LRATTrim

open Cslib.Logic.PL Std.Tactic.BVDecide
open CslibFrontierTests.Logics.Propositional.CNF.LRAT (php phpCert)

#guard php.checkLRAT (CNF.renumberCert php.length (CNF.trimCert phpCert))

/-- Every clause over two variables, as in the tests of `CNF.checkLRAT`. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- A refutation with an unused step `7`, a deletion, and the steps after the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 7 #[2] #[1, 3], .addRup 9 #[1] #[1, 2], .del #[7], .addEmpty 10 #[9, 3, 4],
    .addRup 11 #[2] #[1, 3]]

#guard φ.checkLRAT cert

-- The unused step, the deletion and the steps after the empty clause are dropped.
#guard CNF.trimCert cert == #[.addRup 9 #[1] #[1, 2], .addEmpty 10 #[9, 3, 4]]

-- The added clauses are numbered after the four clauses of the formula.
#guard CNF.renumberCert φ.length (CNF.trimCert cert) ==
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

/-- The number `9` is used for `¬a`, which is deleted, and then for `a`, which the empty clause
uses. -/
private abbrev reuseDeleted : Array LRAT.IntAction :=
  #[.addRup 9 #[-1] #[3, 4], .del #[9], .addRup 9 #[1] #[1, 2], .addEmpty 10 #[9, 3, 4]]

#guard φ.checkLRAT reuseDeleted
#guard φ.checkLRAT (CNF.trimCert reuseDeleted)
#guard φ.checkLRAT (CNF.renumberCert φ.length (CNF.trimCert reuseDeleted))

/-- Clause `1` of the formula is replaced by `a` under the same number, as in the tests of
`CNF.checkLRAT`; the hint `1` of the step adding it names the clause of the formula. -/
private abbrev reuseFormula : Array LRAT.IntAction :=
  #[.addRup 1 #[1] #[1, 2], .addEmpty 5 #[1, 3, 4]]

#guard φ.checkLRAT reuseFormula
#guard CNF.renumberCert φ.length (CNF.trimCert reuseFormula) ==
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]
#guard φ.checkLRAT (CNF.renumberCert φ.length (CNF.trimCert reuseFormula))

/-- A deletion of the absent number `5` before the refutation. -/
private abbrev deleteAbsent : Array LRAT.IntAction :=
  #[.addRup 9 #[1] #[1, 2], .del #[5], .addEmpty 10 #[9, 3, 4]]

#guard φ.checkLRAT deleteAbsent
#guard φ.checkLRAT (CNF.renumberCert φ.length deleteAbsent)

-- Renumbering the deletion along with the clauses would delete the clause numbered `5`.
#guard !φ.checkLRAT #[.addRup 5 #[1] #[1, 2], .del #[5], .addEmpty 6 #[5, 3, 4]]

end CslibFrontierTests.Logics.Propositional.CNF.LRATTrim
