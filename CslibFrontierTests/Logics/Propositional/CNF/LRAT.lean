/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.LRAT
public meta import CslibFrontier.Logics.Propositional.CNF.StdSat
public meta import Std.Tactic.BVDecide.LRAT.Checker

/-!
# The LRAT checker

The four clauses over the variables `a = 0` and `b = 1` (DIMACS `1` and `2`), numbered `1` to `4`,

  `a ∨ b`, `a ∨ ¬b`, `¬a ∨ b`, `¬a ∨ ¬b`,

are refuted in two steps. Clause `5`, `a`, is a RUP clause: from `¬a`, clause `1` forces `b` and
then clause `2` is false. The empty clause follows: clause `5` forces `a`, then clause `3` forces
`b`, and clause `4` is false. The kernel checks the certificate with `decide`, and Lean core's
checker accepts it too. The hints `3, 4` alone do not refute the formula, since clause `3` has two
unassigned literals, and the checker rejects them; so does a certificate that ends before the
empty clause. A literal repeated in a clause counts once.

A certificate from an independent solver: CaDiCaL 3.0.1 refutes the pigeonhole formula PHP(4, 3),
four pigeons in three holes, with fifteen RUP steps, and both checkers accept its certificate.
-/

set_option linter.privateModule false

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

-- A certificate must reach an empty-clause step.
example : φ.checkLRAT #[.addRup 5 #[1] #[1, 2]] = false := by decide

-- RAT steps are rejected.
example : φ.checkLRAT #[.addRat 5 #[1] (0, true) #[] #[], .addEmpty 6 #[5, 3, 4]] = false := by
  decide

-- A repeated literal counts once: `a ∨ a` forces `a`, which falsifies `¬a`.
example : CNF.checkLRAT [[(0, true), (0, true)], [(0, false)]] #[.addEmpty 3 #[1, 2]] = true := by
  decide

/-- PHP(4, 3): pigeon `i` in hole `j` is the variable `3 * i + j`. -/
private abbrev php : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)],
    [(6, true), (7, true), (8, true)], [(9, true), (10, true), (11, true)],
    [(0, false), (3, false)], [(0, false), (6, false)], [(0, false), (9, false)],
    [(3, false), (6, false)], [(3, false), (9, false)], [(6, false), (9, false)],
    [(1, false), (4, false)], [(1, false), (7, false)], [(1, false), (10, false)],
    [(4, false), (7, false)], [(4, false), (10, false)], [(7, false), (10, false)],
    [(2, false), (5, false)], [(2, false), (8, false)], [(2, false), (11, false)],
    [(5, false), (8, false)], [(5, false), (11, false)], [(8, false), (11, false)]]

/-- The certificate CaDiCaL 3.0.1 emits for `php`, transcribed from its LRAT output: write `php` in
DIMACS (variable `v` as `v + 1`) to `php43.cnf` and run
`cadical --lrat=true --binary=false php43.cnf php43.lrat`. -/
private abbrev phpCert : Array LRAT.IntAction :=
  #[.addRup 23 #[-11, -12] #[22, 19, 13, 16, 1, 3, 6],
    .addRup 24 #[-7, -12] #[21, 19, 6, 8, 1, 2, 11],
    .addRup 25 #[-12] #[19, 21, 22, 24, 3, 12, 14, 1, 2, 5],
    .addRup 26 #[-8] #[25, 12, 14, 16, 4, 7, 9, 1, 2, 17],
    .addRup 27 #[-7] #[25, 6, 8, 10, 4, 13, 15, 1, 2, 17],
    .addRup 28 #[9] #[27, 26, 3],
    .addRup 29 #[-3] #[28, 18],
    .addRup 30 #[-6] #[28, 20],
    .addRup 31 #[-1] #[30, 25, 5, 7, 2, 4, 15],
    .addRup 32 #[2] #[31, 29, 1],
    .addRup 33 #[-5] #[32, 11],
    .addRup 34 #[-11] #[32, 13],
    .addRup 35 #[4] #[33, 30, 2],
    .addRup 36 #[10] #[34, 25, 4],
    .addEmpty 37 #[35, 36, 9]]

example : php.checkLRAT phpCert = true := by decide

example : ¬ php.Satisfiable := CNF.not_satisfiable_of_checkLRAT (cert := phpCert) (by decide)

/-- info: true -/
#guard_msgs in
#eval LRAT.check phpCert php.toStdSat

end CslibFrontierTests.Logics.Propositional.CNF.LRAT
