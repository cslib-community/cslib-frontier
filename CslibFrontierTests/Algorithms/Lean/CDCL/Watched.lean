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
clauses: unit clauses, the empty clause and a clause with a repeated literal. Every combination of
the options decides correctly, and the statistics count conflicts, propagations and decisions.
Restarts happen when allowed, minimization shortens the learned clauses of PHP(4, 3), and the kernel
refutes PHP(5, 4) through a reduction of the learned clauses. At runtime, Lean core's checker
accepts the certificates for PHP(5, 4) and PHP(6, 5), whose learned clauses are minimized, some of
them forgotten, and whose intermediate resolvents are deleted.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Watched

open Cslib.Logic.PL Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- PHP(3, 2), the library's pigeonhole formula with pigeon `i` in hole `j` as `2 * i + j`. -/
private abbrev php : CNF ℕ := (CNF.pigeonhole 3 2).relabel fun x => 2 * x.1.val + x.2.val

example : ¬ php.Satisfiable := by
  rw [← CDCL.isSat_solve_iff]
  decide +kernel

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

/-- Unit clauses, and a clause `¬a ∨ ¬a` with a repeated literal, which is stored as short. -/
private abbrev units : CNF ℕ :=
  [[(2, true)], [(0, false), (0, false)], [(0, true), (1, true), (2, false)],
    [(1, false), (3, true)]]

example : (match CDCL.solve units with
    | .sat σ => units.eval σ
    | .unsat _ => false) = true := by
  decide

/-- Contradictory unit clauses. -/
example : (CDCL.solve [[(0, true)], [(0, false)]]).isSat = false := by decide

/-- The empty clause. -/
example : (CDCL.solve [[(0, true), (1, true)], []]).isSat = false := by decide

/-- Every combination of options refutes PHP(3, 2) and finds a model of `units`. -/
example : (CDCL.solveWith { vsids := false } php).1.isSat = false ∧
    (CDCL.solveWith { phaseSaving := false } php).1.isSat = false ∧
    (CDCL.solveWith { vsids := false, phaseSaving := false } php).1.isSat = false := by
  decide +kernel

example : (match (CDCL.solveWith { vsids := false, phaseSaving := false } units).1 with
    | .sat σ => units.eval σ
    | .unsat _ => false) = true := by
  decide

/-- The statistics of a run: refuting `x₀`, `¬x₀` takes one conflict and one propagation. -/
example : (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.conflicts = 1 ∧
    (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.propagations = 1 ∧
    (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.decisions = 0 := by
  decide

/-- Propagations count the literals taken from the queue, decisions included, as MiniSat counts
them: on `x₀ ∨ x₁`, the decision `¬x₀` and the implied `x₁` are both processed. -/
example : (CDCL.solveWith {} [[(0, true), (1, true)]]).2.decisions = 1 ∧
    (CDCL.solveWith {} [[(0, true), (1, true)]]).2.propagations = 2 := by
  decide

/-- PHP(4, 3), with pigeon `i` in hole `j` as `3 * i + j`. -/
private abbrev php43 : CNF ℕ := (CNF.pigeonhole 4 3).relabel fun x => 3 * x.1.val + x.2.val

/-- With a first restart budget of one conflict, scaled by the Luby sequence `1, 1, 2, 1, 1, 2, 4,
…`, the solver still refutes PHP(4, 3), and restarts. -/
example : (CDCL.solveWith { restartFirst := 1 } php43).1.isSat = false ∧
    0 < (CDCL.solveWith { restartFirst := 1 } php43).2.restarts := by
  decide +kernel

/-- Without restarts, it never restarts. -/
example : (CDCL.solveWith { restarts := false } php).2.restarts = 0 := by decide +kernel

/-- A state on `x₀ ∨ x₁` with the decision `¬x₀`, from the saved phase `false`, which forces `x₁`
by the clause; the saved phase of `x₁` is still `false`. -/
private def beforeRestart : CDCL.WExec [[(0, true), (1, true)]] :=
  let S := (CDCL.WExec.init [[(0, true), (1, true)]] {}).decide 0
  { S with exec := S.exec.propagate (1, []) (1, true), queue := [] }

/-- The decision is `¬x₀`, and the clause `x₀ ∨ x₁` then forces `x₁`. -/
example : CDCL.Trail.lits beforeRestart.M = [(1, true), (0, false)] := by decide +kernel

/-- With phase saving, restart saves the phase of `x₁` as `true`. -/
example : beforeRestart.phase.get 1 = false ∧ beforeRestart.restart.phase.get 1 = true := by
  decide +kernel

/-- Without phase saving, restart keeps the phase of `x₁` at `false`. -/
example :
    ({ beforeRestart with opts := { phaseSaving := false } }).restart.phase.get 1 = false := by
  decide +kernel

/-- The minimization steps of a certificate: the RUP steps hinting at least three clauses, which
resolution steps, hinting two, cannot be. Each comes with whether its clause repeats no literal. -/
private def minimizationSteps (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) : List Bool :=
  cert.toList.filterMap fun
    | .addRup _ c hints => if 3 ≤ hints.size then some (decide c.toList.Nodup) else none
    | _ => none

/-- On PHP(4, 3) minimization removes literals, and its clause repeats no literal: the asserting
literal is not kept in the tail as well as at the head. -/
example : (match (CDCL.solveWith {} php43).1 with
    | .unsat cert => !(minimizationSteps cert).isEmpty && (minimizationSteps cert).all id
    | .sat _ => false) = true := by
  decide +kernel

/-- Minimization removes literals from the clauses learned on PHP(4, 3); without it, none are. -/
example : (CDCL.solveWith {} php43).2.literals < (CDCL.solveWith {} php43).2.maxLiterals ∧
    (CDCL.solveWith { minimize := false } php43).2.literals =
      (CDCL.solveWith { minimize := false } php43).2.maxLiterals := by
  decide +kernel

/-- PHP(5, 4), with pigeon `i` in hole `j` as `4 * i + j`. -/
private abbrev php54 : CNF ℕ := (CNF.pigeonhole 5 4).relabel fun x => 4 * x.1.val + x.2.val

/-- The kernel refutes PHP(5, 4) through a reduction of the learned clauses. -/
example : (CDCL.solveWith {} php54).1.isSat = false ∧ 0 < (CDCL.solveWith {} php54).2.removed := by
  decide +kernel

-- Without reduction, no learned clause is forgotten.
/-- info: 0 -/
#guard_msgs in
#eval (CDCL.solveWith { reduce := false } php54).2.removed

/-- The empty formula. -/
example : (CDCL.solve []).isSat = true := by decide

-- PHP(5, 4) and PHP(6, 5): Lean core's checker accepts the watched solver's certificates, which
-- delete the intermediate resolvents and the forgotten learned clauses.
/-- info: (true, true) -/
#guard_msgs in
#eval
  let check (n : ℕ) :=
    let φ := (CNF.pigeonhole (n + 1) n).relabel fun x => n * x.1.val + x.2.val
    match CDCL.solveWith {} φ with
    | (.unsat cert, s) => LRAT.check cert φ.toStdSat && 0 < s.removed
    | (.sat _, _) => false
  (check 4, check 5)

/-- With `27` clauses the limit on the learned clauses starts at `9` and grows by a tenth at each
adjustment, kept in thousandths: `9000`, `9900`, `10890`, as MiniSat's `9`, `9.9`, `10.89`. -/
example : (CDCL.Reduction.init 27).max = 9000 ∧
    ({ CDCL.Reduction.init 27 with countdown := 1 }.learn [] 0 0 false).max = 9900 ∧
    ({ { CDCL.Reduction.init 27 with countdown := 1 }.learn [] 0 0 false with countdown := 1 }.learn
      [] 0 0 false).max = 10890 := by
  decide

/-- Deleting no clause leaves the log, and so the certificate, unchanged. -/
example (φ : CNF ℕ) : (CNF.LRATLog.init φ).delete [] = CNF.LRATLog.init φ := rfl

end CslibFrontierTests.Algorithms.Lean.CDCL.Watched
