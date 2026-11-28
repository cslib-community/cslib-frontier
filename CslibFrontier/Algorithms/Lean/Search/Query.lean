/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.Problem
public import Cslib.Algorithms.Lean.Query.FreeM

/-!
# The search query type

Search algorithms access a problem only through its interface: the actions of a state, the
result of an action, the goal test, the action cost and, for informed search, a heuristic. In
CSLib's query-complexity framework (`Cslib.Algorithms.Lean.Query.FreeM`) this interface is the
query type `SearchQuery S A`, and a search algorithm written as a `FreeM (SearchQuery S A)`
program can be run against any oracle answering these queries. A problem `P` together with a
heuristic `h` induces the oracle `P.oracle h`.

Algorithms are written once, monad-polymorphically, against a handler
`q : {ι : Type} → SearchQuery S A ι → m ι` interpreting the queries in a monad `m`, as CSLib's
`List.mergeSortM` is written against a monadic comparison. Interpreting the queries by
`fun op => pure (P.oracle h op)` in `Id` gives the pure algorithm, and interpreting them by
`FreeM.lift` gives the query program, whose evaluation against an oracle is `FreeM.eval`. An
informed algorithm asks for the heuristic through its node priority, so a search whose priority
does not ask for it makes no heuristic queries and does not depend on `h`.

The textbook's complexity analyses count the nodes a search generates and expands (for instance
in [RussellNorvig2020], §3.4). Expanding a node asks for the actions of its state and generating a
child asks for the result of an action, so these counts are the costs of a query program under
the weights `SearchQuery.expansionWeight` and `SearchQuery.generationWeight`, read off the program
tree rather than annotated by hand.

## Main definitions

* `Cslib.Algorithms.Lean.Search.SearchQuery`: the queries on a search problem's interface.
* `Problem.oracle`: the oracle a problem and a heuristic induce.
* `SearchQuery.expansionWeight`, `SearchQuery.generationWeight`: query weights counting
  expansions and generations.

## References

* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

/-- The queries on the interface of a search problem with states `S` and actions `A`, indexed by
their answer types. -/
inductive SearchQuery (S A : Type) : Type → Type where
  /-- The actions applicable in a state. -/
  | actions (s : S) : SearchQuery S A (List A)
  /-- The state reached by taking an action in a state. -/
  | result (s : S) (a : A) : SearchQuery S A S
  /-- Whether a state is a goal state. -/
  | isGoal (s : S) : SearchQuery S A Bool
  /-- The cost of taking an action in a state. -/
  | stepCost (s : S) (a : A) : SearchQuery S A ℕ
  /-- The heuristic estimate of the cost from a state to a goal. -/
  | heuristic (s : S) : SearchQuery S A ℕ

variable {S A : Type}

/-- The oracle induced by a problem `P` and a heuristic `h`: it answers each query from `P`'s
data, and heuristic queries by `h`. -/
@[expose] def Problem.oracle (P : Problem S A) (h : S → ℕ) : {ι : Type} → SearchQuery S A ι → ι
  | _, .actions s => P.actions s
  | _, .result s a => P.result s a
  | _, .isGoal s => P.isGoal s
  | _, .stepCost s a => P.stepCost s a
  | _, .heuristic s => h s

section Oracle

variable (P : Problem S A) (h : S → ℕ)

@[simp] theorem Problem.oracle_actions (s : S) : P.oracle h (.actions s) = P.actions s := rfl

@[simp] theorem Problem.oracle_result (s : S) (a : A) : P.oracle h (.result s a) = P.result s a :=
  rfl

@[simp] theorem Problem.oracle_isGoal (s : S) : P.oracle h (.isGoal s) = P.isGoal s := rfl

@[simp] theorem Problem.oracle_stepCost (s : S) (a : A) :
    P.oracle h (.stepCost s a) = P.stepCost s a := rfl

@[simp] theorem Problem.oracle_heuristic (s : S) : P.oracle h (.heuristic s) = h s := rfl

end Oracle

/-- Query weight counting node expansions: expanding a node is one `actions` query. -/
@[expose] def SearchQuery.expansionWeight : {ι : Type} → SearchQuery S A ι → ℕ
  | _, .actions _ => 1
  | _, .result _ _ => 0
  | _, .isGoal _ => 0
  | _, .stepCost _ _ => 0
  | _, .heuristic _ => 0

/-- Query weight counting node generations: generating a child is one `result` query. -/
@[expose] def SearchQuery.generationWeight : {ι : Type} → SearchQuery S A ι → ℕ
  | _, .actions _ => 0
  | _, .result _ _ => 1
  | _, .isGoal _ => 0
  | _, .stepCost _ _ => 0
  | _, .heuristic _ => 0

end Cslib.Algorithms.Lean.Search
