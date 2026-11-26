/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.LRATKernel
public meta import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# The LRAT checker for kernel reduction

The kernel evaluates `CNF.checkLRATKernel` with `decide +kernel`. It accepts CaDiCaL's certificate
for the pigeonhole formula PHP(5, 4) from the tests of `CNF.checkLRAT`, and rejects each failing
certificate of those tests: hints that do not propagate to a conflict, a certificate without an
empty-clause step, a RAT step, a hint naming a deleted clause or no clause, and a RUP step whose
hint leaves two literals open.

Each step starts from an empty trail, and the edge cases of the tests of `CNF.checkLRATFast` are
checked here too: a clause containing both polarities of a variable, a reused clause number, and
deleting an absent number. Clause numbers far from the formula's exercise long paths in the trie,
and a variable far from `0` a wide bitmask.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.CNF.LRATKernel

open Cslib.Logic.PL Std.Tactic.BVDecide
open CslibFrontierTests.Logics.Propositional.CNF.LRAT (php phpCert)

example : php.checkLRATKernel phpCert = true := by decide +kernel

example : ¬ php.Satisfiable :=
  CNF.not_satisfiable_of_checkLRAT (cert := phpCert)
    ((CNF.checkLRATKernel_eq_checkLRAT _ _).symm.trans (by decide +kernel))

/-- Every clause over two variables, as in the tests of `CNF.checkLRAT`. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

example : φ.checkLRATKernel cert = true := by decide +kernel

-- A repeated literal counts once.
example : CNF.checkLRATKernel [[(0, true), (0, true)], [(0, false)]] #[.addEmpty 3 #[1, 2]] =
    true := by
  decide +kernel

-- The steps after an accepted empty-clause step are not read.
example : φ.checkLRATKernel (cert ++ #[.addRat 7 #[1] (0, true) #[] #[]]) = true := by
  decide +kernel

/-! Each failing case of the tests of `CNF.checkLRAT` is rejected. -/

-- Hints that do not propagate to a conflict.
example : φ.checkLRATKernel #[.addEmpty 5 #[3, 4]] = false := by decide +kernel

-- A certificate that does not reach an empty-clause step.
example : φ.checkLRATKernel #[.addRup 5 #[1] #[1, 2]] = false := by decide +kernel

-- A RAT step.
example : φ.checkLRATKernel #[.addRat 5 #[1] (0, true) #[] #[], .addEmpty 6 #[5, 3, 4]] =
    false := by
  decide +kernel

-- A hint naming a deleted clause.
example : φ.checkLRATKernel #[.del #[1], .addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]] =
    false := by
  decide +kernel

-- A hint naming no clause.
example : φ.checkLRATKernel #[.addEmpty 5 #[9]] = false := by decide +kernel

-- A RUP step whose hint leaves two literals open.
example : φ.checkLRATKernel #[.addRup 5 #[1] #[3], .addEmpty 6 #[5, 3, 4]] = false := by
  decide +kernel

/-! Each step starts from an empty trail. -/

-- From `¬a`, clause `1` of `a ∨ b`, `a ∨ ¬b`, `¬b` forces `b`, which falsifies clause `2`. The
-- formula is satisfiable: `b` must not stay true in the next step and falsify clause `3`.
example : CNF.checkLRATKernel [[(0, true), (1, true)], [(0, true), (1, false)], [(1, false)]]
    #[.addRup 4 #[1] #[1, 2], .addEmpty 5 #[3]] = false := by
  decide +kernel

-- As above on `a ∨ b`, `a ∨ ¬b`: `¬a` must not stay true in the next step.
example : CNF.checkLRATKernel [[(0, true), (1, true)], [(0, true), (1, false)]]
    #[.addRup 3 #[1] #[1, 2], .addEmpty 4 #[1, 2]] = false := by
  decide +kernel

/-! Edge cases of the reference checker. -/

-- The clause `a ∨ ¬a` assumes both `¬a` and `a`, so the clause `a` has no literal left.
example : CNF.checkLRATKernel [[(0, true)], [(0, false)]]
    #[.addRup 3 #[1, -1] #[1], .addEmpty 4 #[1, 2]] = true := by
  decide +kernel

-- Reusing the number `1` shadows the clause `a ∨ b` by the unit clause `a`.
example : φ.checkLRATKernel #[.addRup 1 #[1] #[1, 2], .addEmpty 5 #[1, 3, 4]] = true := by
  decide +kernel

-- Deleting an absent clause number does nothing.
example : φ.checkLRATKernel (#[.del #[7, 1000]] ++ cert) = true := by decide +kernel

/-! Large clause numbers and variables. -/

-- Clause numbers far from the formula's, and a deletion of one of them.
example : φ.checkLRATKernel #[.addRup 1000000 #[1] #[1, 2], .addRup 65536 #[1] #[1, 2],
    .del #[1000000], .addEmpty 1000001 #[65536, 3, 4]] = true := by
  decide +kernel

example : φ.checkLRATKernel #[.addRup 1000000 #[1] #[1, 2], .del #[1000000],
    .addEmpty 1000001 #[1000000, 3, 4]] = false := by
  decide +kernel

-- The variable `999`, at bits `1998` and `1999` of the trail.
example : CNF.checkLRATKernel [[(999, true), (0, true)], [(999, false), (0, true)], [(0, false)]]
    #[.addEmpty 4 #[3, 1, 2]] = true := by
  decide +kernel

end CslibFrontierTests.Logics.Propositional.CNF.LRATKernel
