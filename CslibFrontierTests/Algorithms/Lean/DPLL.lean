/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public meta import CslibFrontier.Algorithms.Lean.DPLL
public meta import CslibFrontier.Logics.Propositional.CNF.StdSat
public meta import Std.Tactic.BVDecide.LRAT.Checker

/-!
# The DPLL solver

The pigeonhole formula PHP(3, 2) says that three pigeons sit in two holes, no two in the same one.
Pigeon `i` in hole `j` is the variable `2 * i + j`. The kernel runs the solver with `decide`: it
answers `unsat`, which proves the formula unsatisfiable through `isSat_solve_iff`, and Lean core's
checker accepts its certificate too. On a satisfiable chain of implications the solver returns a
model, checked by the kernel. On a formula whose variables occur in several clauses, the search
starts from its variables without repetitions, and returns a model.
-/

set_option linter.privateModule false

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

/-- Variables `0` and `5` occur in several clauses, so `CNF.vars` lists them more than once. -/
private abbrev repeated : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (3, true), (4, true)],
    [(5, true), (6, true), (7, true)], [(5, false), (6, false), (7, false)]]

-- The search starts from the variables without repetitions, which are open; the list with
-- repetitions is not, so a variable cannot be chosen again after it is assigned.
example : OpenVars repeated [] repeated.vars.dedup :=
  ⟨fun _ hx => .inl (List.mem_dedup.2 hx), by simp, List.nodup_dedup _⟩

example : ¬ OpenVars repeated [] repeated.vars := fun h => by
  have := h.nodup
  revert this
  decide

-- After `0` is assigned, the open variables are the others, and the search branches on `1`,
-- which is unassigned.
example : ((1, true) : Literal ℕ) ∉ [((0, true) : Literal ℕ)] ∧
    ((1, false) : Literal ℕ) ∉ [((0, true) : Literal ℕ)] :=
  OpenVars.fresh (φ := repeated) (x := 1) (xs := [2, 3, 4, 5, 6, 7])
    ⟨by decide, by decide, by decide⟩ rfl

example : (match solve repeated with
    | .sat σ => repeated.eval σ
    | .unsat _ => false) = true := by
  decide

end CslibFrontierTests.Algorithms.Lean.DPLL
