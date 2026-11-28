/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Two-player games and finite game trees

A `Game` is a deterministic, fully observable, two-player, turn-taking game in the
parametrization of [RussellNorvig2020], Section 5.1.1: an initial state, the player to move in each
state, the legal moves (`List`-valued), the transition model, a terminal test and a utility,
read from MAX's point of view. The two players are MAX and MIN (`Player`). Nothing is assumed
finite: the state space may be infinite and plays may be unbounded.

Search algorithms work on a `GameTree`, a finite tree whose leaves carry values and whose inner
nodes carry the player to move and the list of subtrees, following [Nipkow2024]. A game is
unfolded into a tree to a depth `d` (`Game.unfold`): terminal states become leaves carrying
their utility, non-terminal states at the depth cut-off become leaves carrying a heuristic
evaluation, and every other state becomes a node with one subtree per legal move, in order. This
is the tree that the textbook's depth-limited heuristic minimax (H-MINIMAX, [RussellNorvig2020],
Section 5.3) explores. When every play from a state ends within `d` moves (`Game.EndsWithin`),
the cut-off is never reached, and the unfolded tree is the full game tree: it depends neither on
the evaluation function nor on any extra depth (`Game.unfold_eq_of_endsWithin`).

`Cslib.GameTheory.Extensive.PerfectInfoTree` models perfect-information extensive games for
equilibrium analysis, with real payoff vectors, finite-type action sets and chance nodes;
`GameTree` is the search-algorithm counterpart, with values in an arbitrary linear order and
children in a list, which is the order in which search algorithms visit them.

## Main definitions

* `Cslib.Algorithms.Lean.Search.Player`: the players MAX and MIN.
* `Cslib.Algorithms.Lean.Search.Game`: a two-player game in the AIMA parametrization.
* `Cslib.Algorithms.Lean.Search.GameTree`: finite game trees.
* `Cslib.Algorithms.Lean.Search.Game.unfold`: the game tree below a state, cut off at a depth.
* `Cslib.Algorithms.Lean.Search.Game.EndsWithin`: every play from a state ends within a number
  of moves.

## Main results

* `Cslib.Algorithms.Lean.Search.Game.unfold_eq_of_endsWithin`: if every play from `s` ends within
  `n` moves, then the tree unfolded from `s` to any depth `m ≥ n` does not depend on `m` or on
  the evaluation function.

## References

* [S. Russell, P. Norvig, *Artificial Intelligence: A Modern Approach*][RussellNorvig2020],
  Chapter 5.
* [T. Nipkow, *Alpha-Beta Pruning Verified*][Nipkow2024].
-/

public section

namespace Cslib.Algorithms.Lean.Search

universe u v w

/-- The two players of a two-player zero-sum game: MAX, who moves to maximize the utility, and
MIN, who moves to minimize it. -/
inductive Player where
  /-- The maximizing player. -/
  | max
  /-- The minimizing player. -/
  | min
  deriving DecidableEq, Repr, Inhabited

/-- A deterministic, fully observable, two-player, turn-taking game with states `S`, moves `A`
and utilities `U` ([RussellNorvig2020], Section 5.1.1). The utility is read from MAX's point of
view and only at terminal states; algorithms compare utilities in a linear order on `U`. -/
structure Game (S : Type u) (A : Type v) (U : Type w) where
  /-- The initial state. -/
  initial : S
  /-- The player whose turn it is to move in a state (`TO-MOVE`). -/
  toMove : S → Player
  /-- The legal moves in a state, in the order in which search algorithms try them
  (`ACTIONS`). -/
  actions : S → List A
  /-- The transition model: the state that results from making a move (`RESULT`). -/
  result : S → A → S
  /-- The terminal test: whether the game is over (`IS-TERMINAL`). -/
  isTerminal : S → Bool
  /-- The utility of a terminal state for MAX (`UTILITY(s, MAX)`). -/
  utility : S → U

/-- A finite game tree: a leaf carries a value, and an inner node carries the player to move and
the list of its subtrees, in the order in which search algorithms visit them. -/
inductive GameTree (α : Type u) where
  /-- A leaf carrying a value (a utility or a heuristic evaluation). -/
  | leaf (value : α)
  /-- An inner node where `player` moves to one of the `children`. -/
  | node (player : Player) (children : List (GameTree α))

namespace Game

variable {S : Type u} {A : Type v} {U : Type w} (g : Game S A U)

/-- The game tree below the state `s`, cut off at depth `n`: a terminal state is a leaf carrying
its utility, a non-terminal state at depth `0` is a leaf carrying its heuristic evaluation
`eval s`, and any other state is a node of the player to move with one subtree per legal move. -/
@[expose] def unfold (eval : S → U) : ℕ → S → GameTree U
  | 0, s => if g.isTerminal s then .leaf (g.utility s) else .leaf (eval s)
  | n + 1, s =>
    if g.isTerminal s then .leaf (g.utility s)
    else .node (g.toMove s) ((g.actions s).map fun a => unfold eval n (g.result s a))

/-- Every play from the state `s` reaches a terminal state within `n` moves. -/
@[expose] def EndsWithin : ℕ → S → Prop
  | 0, s => g.isTerminal s = true
  | n + 1, s => g.isTerminal s = true ∨ ∀ a ∈ g.actions s, EndsWithin n (g.result s a)

/-- If every play from `s` ends within `n` moves, the game tree unfolded from `s` to any depth
`m ≥ n` is the full game tree below `s`: it depends neither on `m` nor on the evaluation
function, which is never applied. -/
theorem unfold_eq_of_endsWithin {n m : ℕ} {s : S} (h : g.EndsWithin n s) (hnm : n ≤ m)
    (eval eval' : S → U) : g.unfold eval n s = g.unfold eval' m s := by
  induction n generalizing s m with
  | zero =>
    cases m <;> simp [EndsWithin, unfold] at h ⊢ <;> simp [h]
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    by_cases ht : g.isTerminal s = true
    · simp [unfold, ht]
    · have h' : ∀ a ∈ g.actions s, g.EndsWithin n (g.result s a) := by
        simpa [EndsWithin, ht] using h
      simp only [unfold, ht, Bool.false_eq_true, ↓reduceIte]
      exact congrArg _ (List.map_congr_left fun a ha => ih (h' a ha) (by omega))

end Game

end Cslib.Algorithms.Lean.Search
