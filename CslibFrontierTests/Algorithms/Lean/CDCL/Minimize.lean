/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Minimize

/-!
# Basic and recursive minimization on one learned clause

The variables are `p = 0`, `q = 1`, `a = 2`, `b = 3`, `c = 4`, `e = 5`, `d = 6`. At the root, `p`
holds and `p → q` implies `q`; the decision `a` implies `b` by `a → b`, `c` by `b → c` and `e` by
`a ∧ q → e`; then comes the decision `d`. The learned clause is `¬d ∨ ¬c ∨ ¬e ∨ ¬a`, asserting `¬d`,
numbered `6` after the five clauses of the formula.

Basic minimization (MiniSat's `ccmin_mode = 1`) follows only reasons of literals implied at the
root: it removes `¬e`, whose reason has `¬a` from the clause and `¬q` from the root, and keeps `¬c`,
whose reason has `¬b`, implied above the root. Recursive minimization (`ccmin_mode = 2`) also
follows `b`, and removes `¬c` as well. The kernel computes both, the hints of the RUP step,
including the root chain `1, 2`, and its check.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Minimize

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.Lean.CDCL

/-- The five clauses of the formula, and the learned clause as the sixth. -/
private abbrev fx : CNF ℕ :=
  [[(0, true)], [(0, false), (1, true)], [(2, false), (3, true)], [(3, false), (4, true)],
    [(2, false), (1, false), (5, true)], [(6, false), (4, false), (5, false), (2, false)]]

/-- The trail, newest first. -/
private abbrev T : XTrail :=
  [.decision (6, true), .implied (5, true) 5, .implied (4, true) 4, .implied (3, true) 3,
    .decision (2, true), .implied (1, true) 2, .implied (0, true) 1]

/-- The learned clause `¬d ∨ ¬c ∨ ¬e ∨ ¬a`. -/
private abbrev C : Clause ℕ := [(6, false), (4, false), (5, false), (2, false)]

/-- The minimized clause and the hints of its RUP step, as `Learned.minimize` builds them. -/
private def minimized (recursive : Bool) : Clause ℕ × List ℕ :=
  let r := minimizeRedundant (LRATLog.init fx) T C (6, false) recursive 7
  ((6, false) :: C.filter fun y => y != (6, false) && !r.1.contains y, derivedHints T r.2 ++ [6])

/-- Basic minimization removes `¬e` and keeps `¬c`; the hints replay the root chain and `e`. -/
example : minimized false = ([(6, false), (4, false), (2, false)], [1, 2, 5, 6]) := by
  decide +kernel

/-- Recursive minimization removes `¬c` and `¬e`, through `b`. -/
example : minimized true = ([(6, false), (2, false)], [1, 2, 3, 4, 5, 6]) := by decide +kernel

/-- Both RUP steps are accepted. -/
example : ∀ recursive : Bool, propagateHints fx.lratDB
    ((minimized recursive).1.map Std.Sat.Literal.negate) (minimized recursive).2 = true := by
  decide +kernel

end CslibFrontierTests.Algorithms.Lean.CDCL.Minimize
