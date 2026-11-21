/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Watched
import CslibFrontier.Logics.Propositional.Pigeonhole
public meta import CslibFrontier.Algorithms.Lean.CDCL.Watched
public meta import CslibFrontier.Logics.Propositional.CNF.StdSat
public meta import CslibFrontier.Logics.Propositional.Pigeonhole
public meta import Std.Tactic.BVDecide.LRAT.Checker

/-!
# CDCL with watched literals

The kernel runs the watched solver with `decide` on the pigeonhole formula PHP(3, 2), proving it
unsatisfiable, and on satisfiable formulas, checking the model. The formulas exercise the short
clauses: unit clauses, the empty clause and a clause with a repeated literal. At runtime, Lean
core's checker accepts the certificates for PHP(5, 4) and PHP(6, 5).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Watched

open Cslib.Logic.PL Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- PHP(3, 2), the library's pigeonhole formula with pigeon `i` in hole `j` as `2 * i + j`. -/
private abbrev php : CNF ℕ := (CNF.pigeonhole 3 2).relabel fun x => 2 * x.1.val + x.2.val

example : ¬ php.Satisfiable := by
  rw [← CDCL.isSat_solveWatched_iff]
  decide +kernel

/-- info: true -/
#guard_msgs in
#eval match CDCL.solveWatched php with
  | .unsat cert => LRAT.check cert php.toStdSat
  | .sat _ => false

/-- `a ∨ b`, `¬a ∨ b`, `a ∨ ¬b`, `¬b ∨ c`. -/
private abbrev small : CNF ℕ :=
  [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)],
    [(1, false), (2, true)]]

example : (match CDCL.solveWatched small with
    | .sat σ => small.eval σ
    | .unsat _ => false) = true := by
  decide

/-- Unit clauses, and a clause `¬a ∨ ¬a` with a repeated literal, which is stored as short. -/
private abbrev units : CNF ℕ :=
  [[(2, true)], [(0, false), (0, false)], [(0, true), (1, true), (2, false)],
    [(1, false), (3, true)]]

example : (match CDCL.solveWatched units with
    | .sat σ => units.eval σ
    | .unsat _ => false) = true := by
  decide

/-- Contradictory unit clauses. -/
example : (CDCL.solveWatched [[(0, true)], [(0, false)]]).isSat = false := by decide

/-- The empty clause. -/
example : (CDCL.solveWatched [[(0, true), (1, true)], []]).isSat = false := by decide

/-- The empty formula. -/
example : (CDCL.solveWatched []).isSat = true := by decide

-- PHP(5, 4) and PHP(6, 5): Lean core's checker accepts the watched solver's certificates.
/-- info: (true, true) -/
#guard_msgs in
#eval
  let check (n : ℕ) :=
    let φ := (CNF.pigeonhole (n + 1) n).relabel fun x => n * x.1.val + x.2.val
    match CDCL.solveWatched φ with
    | .unsat cert => LRAT.check cert φ.toStdSat
    | .sat _ => false
  (check 4, check 5)

end CslibFrontierTests.Algorithms.Lean.CDCL.Watched
