/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Search problems and solutions

A search problem in the parametrization of [RussellNorvig2020] (§3.1.1): an initial state, the
list of actions applicable in each state, a deterministic transition model, a goal test and an
action cost in `ℕ`. The state type need not be finite; finiteness belongs to the hypotheses of
completeness theorems, not to the notion of a problem.

The relational view is derived from this functional data rather than taken as primitive: the
problem's labelled transition system `Problem.toLTS` (CSLib's `LTS`) has a transition from `s`
to `s'` labelled `a` when `a` is applicable in `s` and leads to `s'`. A *path* is a sequence of
actions; it leads from `s` to `t` when it is a multistep transition `P.toLTS.MTr s as t`, which
says that every action is applicable where it is taken. The successor relation and reachability
are CSLib's `LTS.UnlabelledTr` and `LTS.CanReach` of `P.toLTS`. The cost of a path is the sum of
its action costs (the textbook's additivity assumption), and a *solution* is a path from the
initial state to a goal state.

## Main definitions

* `Cslib.Algorithms.Lean.Search.Problem`: a search problem.
* `Problem.toLTS`: the labelled transition system of applicable actions.
* `Problem.pathCost`: the cost of a path.
* `Problem.IsSolution`: a path from the initial state to a goal state.
* `Problem.IsOptimalSolution`: a solution of least path cost.

## Main results

* `Problem.deterministic_toLTS`: the transition system of a problem is deterministic.
* `Problem.toLTS_mTr_cons_iff`: a path `a :: as` leads from `s` to `t` iff `a` is applicable in
  `s` and `as` leads from the result to `t`.
* `Problem.pathCost_append_of_mTr`: path costs add along a concatenation.

## References

* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

universe u v

/-- A search problem ([RussellNorvig2020], §3.1.1) with states `S` and actions `A`: an initial
state, the actions `ACTIONS(s)` applicable in each state (a list), the transition model
`RESULT(s, a)`, a decidable goal test `IS-GOAL(s)` and the action cost `c(s, a, s')` in `ℕ`.

The transition model is deterministic, so the reached state `s'` is `result s a` and the action
cost is stored as a function of `s` and `a` alone. -/
structure Problem (S : Type u) (A : Type v) where
  /-- The state the agent starts in. -/
  initial : S
  /-- The actions applicable in a state. -/
  actions : S → List A
  /-- The transition model: the state reached by taking an action in a state. -/
  result : S → A → S
  /-- The goal test. -/
  isGoal : S → Bool
  /-- The cost of taking an action in a state. -/
  stepCost : S → A → ℕ

namespace Problem

variable {S : Type u} {A : Type v} (P : Problem S A)

/-- The labelled transition system of the problem: a transition from `s` to `s'` labelled `a`
when the action `a` is applicable in `s` and leads to `s'`. Its multistep transitions
`P.toLTS.MTr s as t` are the paths from `s` to `t`. -/
@[expose] def toLTS : LTS S A where
  Tr s a s' := a ∈ P.actions s ∧ P.result s a = s'

/-- The cost of the path `as` from `s`: the sum of the action costs along it. -/
@[expose] def pathCost : S → List A → ℕ
  | _, [] => 0
  | s, a :: as => P.stepCost s a + pathCost (P.result s a) as

/-- A solution ([RussellNorvig2020], §3.1.1): a path from the initial state to a goal state. -/
@[expose] def IsSolution (as : List A) : Prop :=
  ∃ t, P.toLTS.MTr P.initial as t ∧ P.isGoal t = true

/-- An optimal solution ([RussellNorvig2020], §3.1.1): a solution whose path cost is at most the
path cost of every solution. -/
@[expose] def IsOptimalSolution (as : List A) : Prop :=
  P.IsSolution as ∧ ∀ bs, P.IsSolution bs → P.pathCost P.initial as ≤ P.pathCost P.initial bs

/-- The transition system of a problem is deterministic: an action leads to at most one
state. -/
instance deterministic_toLTS : P.toLTS.Deterministic :=
  ⟨fun _ _ _ _ h h' => h.2.symm.trans h'.2⟩

@[simp] theorem toLTS_tr (s s' : S) (a : A) :
    P.toLTS.Tr s a s' ↔ a ∈ P.actions s ∧ P.result s a = s' := Iff.rfl

/-- A path `a :: as` leads from `s` to `t` iff `a` is applicable in `s` and `as` leads from
`result s a` to `t`. -/
@[simp] theorem toLTS_mTr_cons_iff (s t : S) (a : A) (as : List A) :
    P.toLTS.MTr s (a :: as) t ↔ a ∈ P.actions s ∧ P.toLTS.MTr (P.result s a) as t := by
  rw [LTS.MTr.cons_iff]
  constructor
  · rintro ⟨_, ⟨ha, rfl⟩, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨_, ⟨ha, rfl⟩, h⟩

@[simp] theorem pathCost_nil (s : S) : P.pathCost s [] = 0 := rfl

@[simp] theorem pathCost_cons (s : S) (a : A) (as : List A) :
    P.pathCost s (a :: as) = P.stepCost s a + P.pathCost (P.result s a) as := rfl

/-- Path costs add along a concatenation: if `as` leads from `s` to `t`, the cost of `as ++ bs`
from `s` is the cost of `as` from `s` plus the cost of `bs` from `t`. -/
theorem pathCost_append_of_mTr {s t : S} {as : List A} (h : P.toLTS.MTr s as t) (bs : List A) :
    P.pathCost s (as ++ bs) = P.pathCost s as + P.pathCost t bs := by
  induction h with
  | refl => simp
  | stepL htr _ ih =>
    obtain ⟨-, rfl⟩ := htr
    simp [ih, Nat.add_assoc]

end Problem

end Cslib.Algorithms.Lean.Search
