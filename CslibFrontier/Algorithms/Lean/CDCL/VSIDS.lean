/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System
public import Mathlib.Data.List.MinMax

/-! # VSIDS: variable activities for the CDCL solver

MiniSat's branching heuristic, *variable state independent decaying sum*. Every variable has an
*activity*. After each conflict, the variables of the clauses met by the conflict analysis are
*bumped*: the current *increment* is added to their activity. These are all the variables of the
conflict clause and of the reasons resolved on, including variables assigned at decision level
`0`. MiniSat bumps a variable only when it is assigned above level `0` (`level(var(q)) > 0` in
`analyze`), so this rule is a variant of MiniSat's. The increment then becomes `inc + inc / 19`,
with integer division: at most the factor `1 / 0.95` (MiniSat's `var_decay = 0.95`), so older bumps
weigh exponentially less. The solver decides an unassigned variable of greatest activity.

Activities and the increment are natural numbers, so the kernel can run the solver. The decay
step sets the increment to `inc + inc / 19`, with integer division, in place of MiniSat's
floating-point `inc / 0.95`. As in MiniSat, when an activity exceeds a limit (here `2 ^ 200`) all
activities and the increment are scaled down (here by `2 ^ 100`, with truncation). The increment
starts at `2 ^ 100`. The truncations can make the increment grow less than by `1 / 0.95` and turn
different activities into ties, so decisions can differ from those of floating-point activities.

The choice of variable does not affect correctness: the solver only needs an unassigned variable
of the database (`Activity.pick_some`), or the fact that there is none (`Activity.pick_none`).
`Activity.pick_max` states that the choice is of greatest activity. MiniSat keeps the variables in
a binary heap ordered by activity; here the unassigned variables are scanned.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Activity`: activities and the increment.
* `Cslib.Algorithms.Lean.CDCL.Activity.bump`: bumping the variables met by an analysis, then
  decaying.
* `Cslib.Algorithms.Lean.CDCL.Activity.pick`: an unassigned variable of greatest activity.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Activity.pick_some`, `Cslib.Algorithms.Lean.CDCL.Activity.pick_none`,
  `Cslib.Algorithms.Lean.CDCL.Activity.pick_max`: what `pick` returns.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **Variable activities**: a score for each variable, by index, and the current increment. -/
structure Activity where
  /-- The activity of each variable; variables past the end have activity `0`. -/
  score : Array ℕ
  /-- The amount added to the activity of a bumped variable. -/
  inc : ℕ

/-- The initial activities of the variables below `n`: all `0`, with increment `2 ^ 100`. -/
def Activity.init (n : ℕ) : Activity := ⟨Array.replicate n 0, 2 ^ 100⟩

/-- The activity of the variable `v`. -/
def Activity.get (A : Activity) (v : ℕ) : ℕ := A.score.getD v 0

/-- The activity above which every activity is scaled down. -/
def Activity.limit : ℕ := 2 ^ 200

/-- **Bumping** `v`: its activity grows by the increment; if it exceeds the limit, every activity
and the increment are divided by `2 ^ 100`. The activities are an array indexed by variable: for
`v` beyond its end, `Array.modify` leaves it unchanged, so bumping `v` does nothing and its
activity stays `0`. The solver's variables are all within the array (`WExec.init` sizes it by the
largest variable of the formula). -/
def Activity.bumpVar (A : Activity) (v : ℕ) : Activity :=
  let score := A.score.modify v (· + A.inc)
  if Activity.limit < score.getD v 0 then ⟨score.map (· >>> 100), A.inc >>> 100⟩
  else ⟨score, A.inc⟩

/-- **After a conflict**: bump each variable met by the analysis once, then set the increment to
`inc + inc / 19`, with integer division: at most the factor `1 + 1 / 19 = 1 / 0.95`, and less by the
truncation. -/
def Activity.bump (A : Activity) (vs : List ℕ) : Activity :=
  let A := vs.dedup.foldl Activity.bumpVar A
  ⟨A.score, A.inc + A.inc / 19⟩

/-- **The decision variable**: an unassigned variable of `vs` of greatest activity, the first one
among ties. -/
def Activity.pick (A : Activity) (M : Trail) (vs : List ℕ) : Option ℕ :=
  (vs.filter fun x => !(Trail.vars M).contains x).argmax A.get

theorem Activity.pick_some {A : Activity} {M : Trail} {vs : List ℕ} {x : ℕ}
    (h : A.pick M vs = some x) : x ∈ vs ∧ x ∉ Trail.vars M := by
  have hm : x ∈ (vs.filter fun x => !(Trail.vars M).contains x).argmax A.get := by
    change x ∈ A.pick M vs; rw [h]; rfl
  have := List.mem_filter.1 (List.argmax_mem hm)
  exact ⟨this.1, by simpa using this.2⟩

theorem Activity.pick_none {A : Activity} {M : Trail} {vs : List ℕ}
    (h : A.pick M vs = none) : ∀ x ∈ vs, x ∈ Trail.vars M := by
  intro x hx
  have := List.argmax_eq_none.1 h
  by_contra hxM
  have : x ∈ vs.filter fun x => !(Trail.vars M).contains x := List.mem_filter.2 ⟨hx, by simpa⟩
  simp_all

/-- **The chosen variable has the greatest activity** among the unassigned variables of `vs`. -/
theorem Activity.pick_max {A : Activity} {M : Trail} {vs : List ℕ} {x : ℕ}
    (h : A.pick M vs = some x) {y : ℕ} (hy : y ∈ vs) (hyM : y ∉ Trail.vars M) :
    A.get y ≤ A.get x :=
  List.le_of_mem_argmax (List.mem_filter.2 ⟨hy, by simpa using hyM⟩)
    (show x ∈ A.pick M vs by rw [h]; rfl)

end Cslib.Algorithms.Lean.CDCL
