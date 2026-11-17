/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public meta import CslibFrontier.Algorithms.Lean.CDCL.Naive
public meta import CslibFrontier.Logics.Propositional.CNF.StdSat
public meta import Std.Tactic.BVDecide.LRAT.Checker
public meta import CslibFrontier.Logics.Propositional.Pigeonhole

/-!
# The naive CDCL solver

The kernel runs the solver on the pigeonhole formula PHP(3, 2) with `decide`: it answers `unsat`,
which proves the formula unsatisfiable, and Lean core's checker accepts its certificate. On a
satisfiable formula it returns a model, checked by the kernel. At runtime, Lean core's checker
accepts its certificate for PHP(5, 4).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Naive

open Cslib.Logic.PL Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- Pigeon `i` sits in hole `j`. -/
private abbrev p (i j : ℕ) : ℕ := 2 * i + j

/-- PHP(3, 2): every pigeon has a hole, and no hole has two pigeons. -/
private abbrev php : CNF ℕ :=
  [[(p 0 0, true), (p 0 1, true)], [(p 1 0, true), (p 1 1, true)], [(p 2 0, true), (p 2 1, true)],
    [(p 0 0, false), (p 1 0, false)], [(p 0 0, false), (p 2 0, false)],
    [(p 1 0, false), (p 2 0, false)], [(p 0 1, false), (p 1 1, false)],
    [(p 0 1, false), (p 2 1, false)], [(p 1 1, false), (p 2 1, false)]]

example : (CDCL.solve php).isSat = false := by decide

example : ¬ php.Satisfiable := by
  rw [← CDCL.isSat_solve_iff]
  decide

/-- info: true -/
#guard_msgs in
#eval match CDCL.solve php with
  | .unsat cert => LRAT.check cert php.toStdSat
  | .sat _ => false

/-- `a ∨ b`, `¬a ∨ b`, `a ∨ ¬b`, `¬b ∨ c`. -/
private abbrev small : CNF ℕ :=
  [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)],
    [(1, false), (2, true)]]

example : (match CDCL.solve small with
    | .sat σ => small.eval σ
    | .unsat _ => false) = true := by
  decide

-- PHP(5, 4), the library's pigeonhole formula with pigeon `i` in hole `j` as `4 * i + j`: Lean
-- core's checker accepts the CDCL certificate.
/-- info: true -/
#guard_msgs in
#eval
  let φ := (CNF.pigeonhole 5 4).relabel fun x => 4 * x.1.val + x.2.val
  match CDCL.solve φ with
  | .unsat cert => LRAT.check cert φ.toStdSat
  | .sat _ => false

end CslibFrontierTests.Algorithms.Lean.CDCL.Naive
