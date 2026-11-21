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

A certificate from an independent solver: CaDiCaL 3.0.1 refutes the pigeonhole formula PHP(5, 4),
five pigeons in four holes, with RUP steps and deletions, and both checkers accept its
certificate. Hints naming deleted or missing clauses and RUP steps whose hints do not propagate
are rejected; steps after an accepted empty-clause step are not read.
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

/-- PHP(5, 4): pigeon `i` in hole `j` is the variable `4 * i + j`. -/
public abbrev php : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true), (7, true)],
    [(8, true), (9, true), (10, true), (11, true)],
    [(12, true), (13, true), (14, true), (15, true)],
    [(16, true), (17, true), (18, true), (19, true)], [(0, false), (4, false)],
    [(0, false), (8, false)], [(0, false), (12, false)], [(0, false), (16, false)],
    [(4, false), (8, false)], [(4, false), (12, false)], [(4, false), (16, false)],
    [(8, false), (12, false)], [(8, false), (16, false)], [(12, false), (16, false)],
    [(1, false), (5, false)], [(1, false), (9, false)], [(1, false), (13, false)],
    [(1, false), (17, false)], [(5, false), (9, false)], [(5, false), (13, false)],
    [(5, false), (17, false)], [(9, false), (13, false)], [(9, false), (17, false)],
    [(13, false), (17, false)], [(2, false), (6, false)], [(2, false), (10, false)],
    [(2, false), (14, false)], [(2, false), (18, false)], [(6, false), (10, false)],
    [(6, false), (14, false)], [(6, false), (18, false)], [(10, false), (14, false)],
    [(10, false), (18, false)], [(14, false), (18, false)], [(3, false), (7, false)],
    [(3, false), (11, false)], [(3, false), (15, false)], [(3, false), (19, false)],
    [(7, false), (11, false)], [(7, false), (15, false)], [(7, false), (19, false)],
    [(11, false), (15, false)], [(11, false), (19, false)], [(15, false), (19, false)]]

/-- The certificate CaDiCaL 3.0.1 emits for `php`, transcribed from its LRAT output: write `php` in
DIMACS (variable `v` as `v + 1`) to `php54.cnf` and run
`cadical --lrat=true --binary=false php54.cnf php54.lrat`. It has 47 RUP steps, 7 deletions and
an empty-clause step. -/
public abbrev phpCert : Array LRAT.IntAction :=
  #[.addRup 46 #[-18, -19, -20] #[35, 29, 45, 39, 19, 25, 1, 4, 8],
    .addRup 47 #[-13, -19, -20] #[34, 29, 44, 39, 8, 13, 1, 3, 17],
    .addRup 48 #[-19, -20] #[45, 44, 39, 29, 34, 35, 47, 4, 18, 23, 1, 3, 7], .del #[47, 46],
    .addRup 49 #[-1, -14, -20] #[23, 21, 44, 42, 6, 7, 2, 3, 30],
    .addRup 50 #[-14, -20] #[44, 42, 39, 18, 21, 23, 49, 1, 26, 27, 2, 3, 10], .del #[49],
    .addRup 51 #[-3, -13, -20] #[13, 11, 44, 42, 26, 27, 2, 3, 20],
    .addRup 52 #[-13, -20] #[44, 42, 39, 8, 11, 13, 51, 1, 16, 17, 2, 3, 30], .del #[51],
    .addRup 53 #[-9, -20] #[45, 50, 52, 4, 31, 28, 42, 39, 7, 10, 1, 2, 16],
    .addRup 54 #[-20] #[39, 42, 44, 45, 50, 52, 4, 28, 31, 33, 53, 3, 17, 20, 1, 2, 6],
    .addRup 55 #[-5, -10, 3] #[54, 24, 23, 17, 6, 11, 12, 1, 5, 38, 35, 4],
    .addRup 56 #[-7, -10, 3] #[54, 24, 23, 17, 31, 32, 5, 9, 15, 1, 4, 38],
    .addRup 57 #[-10, 3] #[54, 17, 20, 23, 24, 55, 56, 2, 36, 41, 1, 8, 9, 4, 5, 35],
    .del #[56, 55], .addRup 58 #[-8, -9, 3] #[54, 14, 13, 7, 36, 41, 1, 18, 19, 4, 5, 35],
    .addRup 59 #[-2, 8, 17, 5] #[54, 16, 19, 2, 5, 32],
    .addRup 60 #[-19, 16, 8, 13, 5] #[32, 35, 2, 4, 21],
    .addRup 61 #[-9, 3] #[54, 7, 10, 13, 14, 58, 59, 1, 38, 60, 5, 22, 25, 2, 4, 31], .del #[58],
    .addRup 62 #[-5, 16, -11] #[54, 34, 33, 11, 12, 4, 5, 25],
    .addRup 63 #[16, 8, -11] #[54, 34, 33, 30, 62, 2, 21, 22, 4, 5, 15],
    .addRup 64 #[-6, 4, 19, 3] #[54, 16, 22, 1, 5, 9],
    .addRup 65 #[8, -11, 3] #[54, 34, 30, 63, 38, 64, 2, 6, 12, 1, 5, 19],
    .addRup 66 #[-18, -11, 3] #[65, 41, 36, 33, 19, 25, 1, 4, 8],
    .addRup 67 #[-11, 3] #[54, 33, 34, 65, 36, 41, 66, 5, 9, 15, 1, 4, 18], .del #[66, 65],
    .addRup 68 #[-13, -2, 8] #[11, 15, 59],
    .addRup 69 #[-2, 18, -12] #[54, 43, 40, 16, 18, 68, 4, 31, 35, 2, 5, 12],
    .addRup 70 #[18, 3] #[54, 61, 57, 67, 3, 43, 40, 37, 69, 1, 6, 8, 9, 60, 5],
    .addRup 71 #[3] #[57, 61, 67, 3, 37, 40, 43, 70, 19, 22, 25, 1, 6, 8, 2, 4, 31],
    .addRup 72 #[-7] #[71, 26], .addRup 73 #[-11] #[71, 27], .addRup 74 #[-15] #[71, 28],
    .addRup 75 #[-19] #[71, 29], .addRup 76 #[-14, 8] #[72, 54, 75, 21, 25, 2, 5, 12],
    .addRup 77 #[8, 16] #[74, 72, 54, 75, 76, 4, 11, 15, 2, 5, 22], .del #[63, 60],
    .addRup 78 #[-13, 12] #[73, 54, 75, 13, 15, 3, 5, 24],
    .addRup 79 #[16] #[74, 73, 54, 75, 77, 40, 78, 4, 23, 25, 3, 5, 14],
    .addRup 80 #[-4] #[79, 38], .addRup 81 #[-8] #[79, 41], .addRup 82 #[-12] #[79, 43],
    .addRup 83 #[-14] #[81, 76], .addRup 84 #[-13] #[82, 78],
    .addRup 85 #[-17] #[81, 72, 73, 82, 12, 14, 2, 3, 20], .addRup 86 #[18] #[85, 75, 54, 5],
    .addRup 87 #[-2] #[86, 19], .addRup 88 #[-6] #[86, 22], .addRup 89 #[-10] #[86, 24],
    .addRup 90 #[5] #[88, 72, 81, 2], .addRup 91 #[9] #[89, 82, 73, 3],
    .addRup 92 #[-1] #[90, 6], .addEmpty 93 #[90, 91, 10]]

example : php.checkLRAT phpCert = true := by decide

example : ¬ php.Satisfiable := CNF.not_satisfiable_of_checkLRAT (cert := phpCert) (by decide)

/-- info: true -/
#guard_msgs in
#eval LRAT.check phpCert php.toStdSat

/-! Each way of failing, on the four clauses over two variables. -/

-- A hint naming a deleted clause is rejected.
example : φ.checkLRAT #[.del #[1], .addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]] = false := by
  decide

-- A hint naming no clause is rejected.
example : φ.checkLRAT #[.addEmpty 5 #[9]] = false := by decide

-- A RUP step whose hint leaves two literals open is rejected.
example : φ.checkLRAT #[.addRup 5 #[1] #[3], .addEmpty 6 #[5, 3, 4]] = false := by decide

-- As in Lean core's checker, the steps after an accepted empty-clause step are not read.
example : φ.checkLRAT (cert ++ #[.addRat 7 #[1] (0, true) #[] #[]]) = true := by decide

end CslibFrontierTests.Logics.Propositional.CNF.LRAT
