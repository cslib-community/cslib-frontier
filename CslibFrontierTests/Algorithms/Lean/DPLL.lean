/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Algorithms.Lean.DPLL
import CslibFrontier.Logics.Propositional.CNF.StdSat
import Std.Tactic.BVDecide.LRAT.Checker

/-!
# The DPLL solver

The pigeonhole formula PHP(3, 2) says that three pigeons sit in two holes, no two in the same one.
Pigeon `i` in hole `j` is the variable `2 * i + j`. The kernel runs the solver with `decide`: it
answers `unsat`, which proves the formula unsatisfiable through `isSat_solve_iff`, and Lean core's
checker accepts its certificate too. On a satisfiable chain of implications the solver returns a
model, checked by the kernel.
-/

namespace CslibFrontierTests.Algorithms.Lean.DPLL

open Cslib.Logic.PL Cslib.Algorithms.Lean.DPLL Std.Tactic.BVDecide

/-- Pigeon `i` sits in hole `j`. -/
private abbrev p (i j : ℕ) : ℕ := 2 * i + j

/-- PHP(3, 2): every pigeon has a hole, and no hole has two pigeons. -/
private abbrev php : CNF ℕ :=
  [[(p 0 0, true), (p 0 1, true)], [(p 1 0, true), (p 1 1, true)], [(p 2 0, true), (p 2 1, true)],
    [(p 0 0, false), (p 1 0, false)], [(p 0 0, false), (p 2 0, false)],
    [(p 1 0, false), (p 2 0, false)], [(p 0 1, false), (p 1 1, false)],
    [(p 0 1, false), (p 2 1, false)], [(p 1 1, false), (p 2 1, false)]]

example : (solve php).isSat = false := by decide

example : ¬ php.Satisfiable := by
  rw [← isSat_solve_iff]
  decide

-- Lean core's checker accepts the certificate.
/-- info: true -/
#guard_msgs in
#eval match solve php with
  | .unsat cert => LRAT.check cert php.toStdSat
  | .sat _ => false

/-- `a`, `a → b`, `b → c`. -/
private abbrev chain : CNF ℕ := [[(0, true)], [(0, false), (1, true)], [(1, false), (2, true)]]

example : (solve chain).isSat = true := by decide

example : (match solve chain with
    | .sat σ => chain.eval σ
    | .unsat _ => false) = true := by
  decide

end CslibFrontierTests.Algorithms.Lean.DPLL
