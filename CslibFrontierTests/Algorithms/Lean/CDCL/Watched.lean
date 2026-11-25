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
Restarts happen when allowed, minimization, recursive or basic, shortens the learned clauses of
PHP(4, 3), simplification deletes clauses of PHP(4, 3) satisfied at the root, and the kernel
refutes PHP(4, 3) through a reduction of the learned clauses. At runtime, Lean core's checker
accepts the certificates for PHP(5, 4) and PHP(6, 5), whose learned clauses are minimized, some of
them forgotten.
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
  decide +kernel

/-- Unit clauses, and a clause `¬a ∨ ¬a` with a repeated literal, which is stored as short. -/
private abbrev units : CNF ℕ :=
  [[(2, true)], [(0, false), (0, false)], [(0, true), (1, true), (2, false)],
    [(1, false), (3, true)]]

example : (match CDCL.solve units with
    | .sat σ => units.eval σ
    | .unsat _ => false) = true := by
  decide +kernel

/-- Contradictory unit clauses. -/
example : (CDCL.solve [[(0, true)], [(0, false)]]).isSat = false := by decide +kernel

/-- The empty clause. -/
example : (CDCL.solve [[(0, true), (1, true)], []]).isSat = false := by decide +kernel

/-- Every combination of options refutes PHP(3, 2) and finds a model of `units`. -/
example : (CDCL.solveWith { vsids := false } php).1.isSat = false ∧
    (CDCL.solveWith { phaseSaving := false } php).1.isSat = false ∧
    (CDCL.solveWith { vsids := false, phaseSaving := false } php).1.isSat = false := by
  decide +kernel

example : (match (CDCL.solveWith { vsids := false, phaseSaving := false } units).1 with
    | .sat σ => units.eval σ
    | .unsat _ => false) = true := by
  decide +kernel

/-- The statistics of a run: refuting `x₀`, `¬x₀` takes one conflict and one propagation. -/
example : (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.conflicts = 1 ∧
    (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.propagations = 1 ∧
    (CDCL.solveWith {} [[(0, true)], [(0, false)]]).2.decisions = 0 := by
  decide +kernel

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
  let S₀ := CDCL.WExec.init [[(0, true), (1, true)]] {}
  let S := S₀.decide 0 S₀.order
  { S with exec := S.exec.propagate (1, []) (1, true), qhead := 2 }

/-- The decision is `¬x₀`, and the clause `x₀ ∨ x₁` then forces `x₁`. -/
example : CDCL.Trail.lits beforeRestart.M = [(1, true), (0, false)] := by decide +kernel

/-- With phase saving, restart saves the phase of `x₁` as `true`. -/
example : beforeRestart.phase.get 1 = false ∧ beforeRestart.restart.phase.get 1 = true := by
  decide +kernel

/-- Without phase saving, restart keeps the phase of `x₁` at `false`. -/
example :
    ({ beforeRestart with opts := { phaseSaving := false } }).restart.phase.get 1 = false := by
  decide +kernel

/-- Minimization removes literals from the clauses learned on PHP(4, 3); without it, none are. -/
example : (CDCL.solveWith {} php43).2.literals < (CDCL.solveWith {} php43).2.maxLiterals ∧
    (CDCL.solveWith { ccminMode := .none } php43).2.literals =
      (CDCL.solveWith { ccminMode := .none } php43).2.maxLiterals := by
  decide +kernel

/-- Simplification deletes input clauses of PHP(4, 3) satisfied at the root; keeping the input
clauses (MiniSat's `remove_satisfied = false`), it deletes none here, and the answer is the same. -/
example : (CDCL.solveWith {} php43).1.isSat = false ∧ 0 < (CDCL.solveWith {} php43).2.simplified ∧
    (CDCL.solveWith { removeSatisfied := false } php43).1.isSat = false ∧
    (CDCL.solveWith { removeSatisfied := false } php43).2.simplified = 0 := by
  decide +kernel

/-- Basic minimization (MiniSat's `ccmin_mode = 1`) also refutes PHP(4, 3), and removes literals. -/
example : (CDCL.solveWith { ccminMode := .basic } php43).1.isSat = false ∧
    (CDCL.solveWith { ccminMode := .basic } php43).2.literals <
      (CDCL.solveWith { ccminMode := .basic } php43).2.maxLiterals := by
  decide +kernel

/-- With the limit on learned clauses starting at `0`, and restarting after every conflict, the
kernel refutes PHP(4, 3) through a reduction of the learned clauses. -/
example : (CDCL.solveWith { restartFirst := 1, learntsDivisor := 1000 } php43).1.isSat = false ∧
    0 < (CDCL.solveWith { restartFirst := 1, learntsDivisor := 1000 } php43).2.removed := by
  decide +kernel

-- Without reduction, no learned clause is forgotten.
/-- info: 0 -/
#guard_msgs in
#eval
  (CDCL.solveWith { restartFirst := 1, learntsDivisor := 1000, reduce := false } php43).2.removed

/-- The empty formula. -/
example : (CDCL.solve []).isSat = true := by decide +kernel

-- PHP(5, 4) and PHP(6, 5): Lean core's checker accepts the watched solver's certificates, which
-- learn each clause in one RUP step and, for PHP(6, 5), delete forgotten learned clauses.
/-- info: (true, true, true) -/
#guard_msgs in
#eval
  let φ (n : ℕ) := (CNF.pigeonhole (n + 1) n).relabel fun x => n * x.1.val + x.2.val
  let check (n : ℕ) :=
    match CDCL.solveWith {} (φ n) with
    | (.unsat cert, _) => LRAT.check cert (φ n).toStdSat
    | (.sat _, _) => false
  (check 4, check 5, decide (0 < (CDCL.solveWith {} (φ 5)).2.removed))

/-- With `27` clauses the limit on the learned clauses starts at `9` and grows by a tenth at each
adjustment, kept in thousandths: `9000`, `9900`, `10890`, as MiniSat's `9`, `9.9`, `10.89`. -/
example : (CDCL.Reduction.init 27 3).max = 9000 ∧
    ({ CDCL.Reduction.init 27 3 with countdown := 1 }.learn [] 0 0 false).max = 9900 ∧
    ({ { CDCL.Reduction.init 27 3 with countdown := 1 }.learn [] 0 0 false with
      countdown := 1 }.learn [] 0 0 false).max = 10890 := by
  decide

/-- Deleting no clause leaves the log, and so the certificate, unchanged. -/
example (φ : CNF ℕ) : (CNF.LRATLog.init φ).delete [] = CNF.LRATLog.init φ := rfl

/-- Deleting a number that names no clause clears nothing past the index: it does not grow. -/
example : ((CNF.LRATLog.init [[(0, true)]]).delete [1000000]).index.size =
    (CNF.LRATLog.init [[(0, true)]]).index.size := by
  decide

/-- The trail below the newest decision of a level-3 conflict, newest first: level 2 (`x₅` implied
over the decision `x₄`), level 1 (`x₃` implied over the decision `x₂`), and
the root (`x₁` implied). -/
private abbrev below : CDCL.XTrail :=
  [.implied (5, true) 9, .decision (4, true), .implied (3, true) 9, .decision (2, true),
    .implied (1, true) 9]

/-- A learned clause with the variable `x₃` of level 1, implied there, and none of level 2: the
backjump drops level 2 and keeps the whole of level 1, with the root below it. -/
example : ((CDCL.XTrail.dropLevels (· == 3) below).1.map CDCL.XEntry.entry =
      [⟨(5, true), false⟩, ⟨(4, true), true⟩]) ∧
    (CDCL.XTrail.dropLevels (· == 3) below).2.map CDCL.XEntry.entry =
      [⟨(3, true), false⟩, ⟨(2, true), true⟩, ⟨(1, true), false⟩] := by
  decide

/-- A unit learned clause marks no variable below the current level: the backjump keeps just the
root, with its implied literal. -/
example : (CDCL.XTrail.dropLevels (fun _ => false) below).2.map CDCL.XEntry.entry =
    [⟨(1, true), false⟩] := by
  decide

/-- Option values MiniSat rejects count as its least allowed ones: a first budget of `0` as `1`,
and a growth of `1` as `2`, so the geometric budgets still grow. -/
example : ({ restartFirst := 0 } : CDCL.Options).restartBudget 0 = 1 ∧
    ({ luby := false, restartFirst := 1, restartInc := 1 } : CDCL.Options).restartBudget 3 = 8 := by
  decide

/-- `p`, `¬p ∨ q`, `q ∨ r`. -/
private abbrev rootSat : CNF ℕ := [[(0, true)], [(0, false), (1, true)], [(1, true), (2, true)]]

/-- On `rootSat` the first two clauses imply `p` and `q` at the root, and root simplification
deletes `q ∨ r`, the only clause with `r`: the solver then needs no decision. Keeping the input
clauses leaves `r` in the database, and it is decided. -/
example : (CDCL.solveWith {} rootSat).2.simplified = 1 ∧
    (CDCL.solveWith {} rootSat).2.decisions = 0 ∧
    (CDCL.solveWith { removeSatisfied := false } rootSat).2.decisions = 1 := by
  decide +kernel

/-- The learned clause and the clauses met are bumped by the increment `2 ^ 40`, the others not. -/
example : ((CDCL.Reduction.init 3 3).learn [3, 1] 5 6 false).act.score =
    #[0, 2 ^ 40, 0, 2 ^ 40, 0, 2 ^ 40] := by
  decide

/-- The formula `a ∨ b`, `¬a ∨ b`: its clauses are numbered `1` and `2`. -/
private abbrev two : CNF ℕ := [[(0, true), (1, true)], [(0, false), (1, true)]]

/-- Storing a clause under the number `2`, a clause of the formula (when the analysis returns the
conflict clause), does not count as a learned clause, in the store or at insertion; under the
number `3` it does, in both. On the solver's insertion path the counter follows `isLearntId`
(`WExec.afterConflict_learnts`), as the store count does (`WatchStore.learntCount_addClause`). -/
example :
    ((CDCL.WExec.init two {}).store.addClause 2 [(0, false), (1, true)]).learntCount 2 =
      (CDCL.WExec.init two {}).store.learntCount 2 ∧ CDCL.isLearntId 2 2 = false ∧
    ((CDCL.WExec.init two {}).store.addClause 3 [(0, false), (1, false)]).learntCount 2 =
      (CDCL.WExec.init two {}).store.learntCount 2 + 1 ∧ CDCL.isLearntId 2 3 = true := by
  decide +kernel

/-- With reduction on, a conflict learning a clause of two or more literals numbered `2` in a
formula of two clauses, at the newest decision at position `p` of the trail, leaves the counter
of learned clauses as it is, and one numbered `3` adds one. -/
example (S : CDCL.WExec two) (p : ℕ) (L : S.exec.LearnedAt (S.exec.tr.splitAt p)) (k₀ : ℕ)
    (hred : S.opts.reduce = true) (hk : 2 ≤ (CDCL.dedupLits L.clause).length) :
    (L.id = 2 → (S.afterConflict p L k₀).red.learnts = S.red.learnts) ∧
    (L.id = 3 → (S.afterConflict p L k₀).red.learnts = S.red.learnts + 1) := by
  rw [S.afterConflict_learnts p L k₀ hred hk]
  exact ⟨fun h => by simp [h, CDCL.isLearntId], fun h => by simp [h, CDCL.isLearntId]⟩

end CslibFrontierTests.Algorithms.Lean.CDCL.Watched
