/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.Game.Query
import Mathlib.Data.ENat.Lattice

/-!
# Tests for minimax and alpha-beta search

* The two-ply tree of [RussellNorvig2020], Figure 5.2, with leaf values `3, 12, 8 / 2, 4, 6 /
  14, 5, 2` has minimax value `3`; both variants of alpha-beta compute it with the full window.
* Windows that the value lies below, inside and above: fail-hard clamps, fail-soft returns a bound
  on the correct side, as `alphaBetaHard_eq` and the fail-soft theorems say.
* The same tree as a `Game` whose states are subtrees: every play ends within two moves, so the
  tree unfolded to depth `2` does not depend on the evaluation function (the hypothesis of
  `Game.unfold_eq_of_endsWithin` is satisfiable); at depth `1` the evaluation function is used.
* In the query model, minimax makes `42` queries and evaluates all `9` leaves, while alpha-beta
  makes `36` queries and evaluates `7` leaves: after the first subtree has value `3`, the second
  is cut off after its first leaf `2`, skipping the leaves `4` and `6` (strict pruning).
* Boundary cases: the degenerate window `[4, 4]` for fail-hard, and nodes without moves.
* A game with an infinite state space and no terminal states, searched to depth `4` with a
  heuristic evaluation: the three algorithms agree, and alpha-beta makes `94` queries to
  minimax's `107`.
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.Game

open Cslib Cslib.Algorithms.Lean.Search

/-- The two-ply game tree of [RussellNorvig2020], Figure 5.2: MAX moves at the root, MIN at the
three inner nodes. -/
def fig52 : GameTree ℕ∞ :=
  .node .max [.node .min [.leaf 3, .leaf 12, .leaf 8], .node .min [.leaf 2, .leaf 4, .leaf 6],
    .node .min [.leaf 14, .leaf 5, .leaf 2]]

example : fig52.minimax = 3 := by decide
example : fig52.alphaBetaHard ⊥ ⊤ = 3 := by decide
example : fig52.alphaBetaSoft ⊥ ⊤ = 3 := by decide

/-! ### Windows: fail low, inside, fail high -/

-- Value `3` below the window `[5, 10]`: fail-hard returns `5`, fail-soft a bound in `[3, 5]`.
example : fig52.alphaBetaHard 5 10 = 5 := by decide
example : fig52.alphaBetaSoft 5 10 = 5 := by decide
-- Value `3` inside the window `[1, 4]`: both return it.
example : fig52.alphaBetaHard 1 4 = 3 := by decide
example : fig52.alphaBetaSoft 1 4 = 3 := by decide
-- Value `3` above the window `[0, 2]`: fail-hard returns `2`, fail-soft a bound in `[2, 3]`.
example : fig52.alphaBetaHard 0 2 = 2 := by decide
example : fig52.alphaBetaSoft 0 2 = 3 := by decide

-- The degenerate window `[4, 4]` (fail-hard allows `α = β`).
example : fig52.alphaBetaHard 4 4 = 4 := by decide

-- A node of MAX without moves has value `⊥`, and one of MIN `⊤` (the textbook's `∓∞`); such a
-- node inside a tree is searched consistently by both variants.
example : (GameTree.node .max [] : GameTree ℕ∞).minimax = ⊥ := by decide
example : (GameTree.node .min [] : GameTree ℕ∞).minimax = ⊤ := by decide

/-- A tree with two nodes without moves below nodes of MIN: one of MAX, worth `⊥`, and one of MIN,
worth `⊤`. -/
def deadEnd : GameTree ℕ∞ :=
  .node .max [.node .min [.leaf 5, .node .max []], .node .min [.leaf 1, .node .min []]]

example : deadEnd.minimax = 1 := by decide
example : deadEnd.alphaBetaHard ⊥ ⊤ = 1 := by decide
example : deadEnd.alphaBetaSoft ⊥ ⊤ = 1 := by decide

/-! ### The tree as a game -/

/-- A game tree as a game: the states are subtrees, the moves at a node are its children, a leaf
is terminal with its value as utility. -/
def treeGame (t : GameTree ℕ∞) : Game (GameTree ℕ∞) (GameTree ℕ∞) ℕ∞ where
  initial := t
  toMove | .leaf _ => .max | .node p _ => p
  actions | .leaf _ => [] | .node _ ts => ts
  result _ t' := t'
  isTerminal | .leaf _ => true | .node _ _ => false
  utility | .leaf x => x | .node _ _ => 0

/-- A heuristic evaluation for the tree game: `7` at every non-terminal state. -/
def eval7 : GameTree ℕ∞ → ℕ∞ := fun _ => 7

example : (treeGame fig52).EndsWithin 2 fig52 := by
  simp [Game.EndsWithin, treeGame, fig52]

-- Every play ends within two moves, so the cut-off is never reached at depth `2` or more.
example (eval eval' : GameTree ℕ∞ → ℕ∞) :
    (treeGame fig52).unfold eval 2 fig52 = (treeGame fig52).unfold eval' 5 fig52 :=
  Game.unfold_eq_of_endsWithin _ (by simp [Game.EndsWithin, treeGame, fig52]) (by omega) _ _

example : ((treeGame fig52).unfold eval7 2 fig52).minimax = 3 := by decide
-- At depth `1` the three inner nodes are cut off and evaluated to `7`.
example : ((treeGame fig52).unfold eval7 1 fig52).minimax = 7 := by decide

/-! ### Queries: alpha-beta prunes -/

/-- The tree game of Figure 5.2. -/
abbrev game52 : Game (GameTree ℕ∞) (GameTree ℕ∞) ℕ∞ := treeGame fig52

-- Evaluating the query programs gives the minimax value.
example : (minimaxQ 2 fig52).eval (game52.oracle eval7) = 3 := by decide
example : (alphaBetaHardQ 2 ⊥ ⊤ fig52).eval (game52.oracle eval7) = 3 := by decide
example : (alphaBetaSoftQ 2 ⊥ ⊤ fig52).eval (game52.oracle eval7) = 3 := by decide

-- Minimax: 3 queries at each inner node, 1 `result` and 2 queries (`isTerminal`, `utility`) per
-- leaf and per inner child: 3 + 3 * (1 + 3 + 3 * 3) = 42.
example : (minimaxQ 2 fig52).countQueries (game52.oracle eval7) = 42 := by decide
-- Alpha-beta skips the leaves `4` and `6`, three queries each.
example : (alphaBetaHardQ 2 ⊥ ⊤ fig52).countQueries (game52.oracle eval7) = 36 := by decide
example : (alphaBetaSoftQ 2 ⊥ ⊤ fig52).countQueries (game52.oracle eval7) = 36 := by decide

/-- Weight one on the queries that evaluate a leaf (`utility` and `eval`), zero on the others. -/
def leafWeight {S A U : Type} : {ι : Type} → GameQuery S A U ι → ℕ
  | _, .utility _ => 1
  | _, .eval _ => 1
  | _, _ => 0

example : (minimaxQ 2 fig52).cost (game52.oracle eval7) leafWeight = 9 := by decide
example : (alphaBetaHardQ 2 ⊥ ⊤ fig52).cost (game52.oracle eval7) leafWeight = 7 := by decide

-- The general bound, instantiated.
example : (alphaBetaHardQ 2 ⊥ ⊤ fig52).cost (game52.oracle eval7) leafWeight ≤
    (minimaxQ 2 fig52).cost (game52.oracle eval7) leafWeight :=
  cost_alphaBetaHardQ_le_cost_minimaxQ _ _ _ _ _ _

-- For every game, with the full window, the query programs compute depth-limited minimax.
example {S A U : Type} [LinearOrder U] [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ)
    (s : S) :
    (alphaBetaHardQ d ⊥ ⊤ s).eval (g.oracle eval) = (minimaxQ d s).eval (g.oracle eval) := by
  simp
example {S A U : Type} [LinearOrder U] [BoundedOrder U] (g : Game S A U) (eval : S → U) (d : ℕ)
    (s : S) :
    (alphaBetaSoftQ d ⊥ ⊤ s).eval (g.oracle eval) = (minimaxQ d s).eval (g.oracle eval) := by
  simp

/-! ### An unbounded game with a depth cut-off -/

/-- A game on `ℕ` that never ends: from `s`, the player to move (MAX on even states) adds `1` or
`2`. The state space is infinite and no play is bounded, so only depth-limited search applies. -/
def countGame : Game ℕ ℕ ℕ∞ where
  initial := 0
  toMove s := if s % 2 = 0 then .max else .min
  actions _ := [1, 2]
  result s a := s + a
  isTerminal _ := false
  utility _ := 0

/-- A heuristic evaluation for `countGame`: the state modulo `5`. -/
def countEval (s : ℕ) : ℕ∞ := (s % 5 : ℕ)

example : (minimaxQ 4 countGame.initial).eval (countGame.oracle countEval) = 3 := by decide
example : (alphaBetaHardQ 4 ⊥ ⊤ countGame.initial).eval (countGame.oracle countEval) = 3 := by
  decide
example : (alphaBetaSoftQ 4 ⊥ ⊤ countGame.initial).eval (countGame.oracle countEval) = 3 := by
  decide
-- Minimax: 15 inner nodes with 3 queries, 30 `result` queries, 16 cut-off leaves with 2 queries.
example : (minimaxQ 4 countGame.initial).countQueries (countGame.oracle countEval) = 107 := by
  decide
example : (alphaBetaHardQ 4 ⊥ ⊤ countGame.initial).countQueries (countGame.oracle countEval) =
    94 := by
  decide

end CslibFrontierTests.Algorithms.Lean.Search.Game
