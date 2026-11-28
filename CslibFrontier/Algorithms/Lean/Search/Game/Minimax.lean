/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.Game.Basic
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Minimax values of game trees

The minimax value of a finite game tree ([RussellNorvig2020], Section 5.2.1) is the value of a
leaf, the largest value of the subtrees at a node where MAX moves, and the smallest at a node
where MIN moves. Values lie in a bounded linear order: the textbook's `-∞` and `+∞`, the values
of a node without moves for MAX and for MIN, are `⊥` and `⊤`.

A node's value is computed as in the textbook's `MAX-VALUE` and `MIN-VALUE`: starting from `⊥`
(or `⊤`), fold in the values of the subtrees from left to right (`GameTree.maxValue`,
`GameTree.minValue`).

For a game `g`, an evaluation function `eval` and a depth `d`, `(g.unfold eval d s).minimax` is
the textbook's depth-limited heuristic minimax value H-MINIMAX of the state `s`
([RussellNorvig2020], Section 5.3). If every play from `s` ends within `d` moves
(`Game.EndsWithin`), it is the minimax value MINIMAX of `s` itself: by
`Game.unfold_eq_of_endsWithin` it depends neither on `eval` nor on any further depth.

## Main definitions

* `Cslib.Algorithms.Lean.Search.GameTree.minimax`: the minimax value of a game tree.
* `Cslib.Algorithms.Lean.Search.GameTree.maxValue`,
  `Cslib.Algorithms.Lean.Search.GameTree.minValue`: a running maximum (minimum) folded with the
  minimax values of a list of trees.

This file provides definitions and their defining equations only; the first property proved
about `minimax`, that alpha-beta pruning computes it, is in
`CslibFrontier.Algorithms.Lean.Search.Game.AlphaBeta`.

## References

* [S. Russell, P. Norvig, *Artificial Intelligence: A Modern Approach*][RussellNorvig2020],
  Sections 5.2.1 and 5.3.
* [T. Nipkow, *Alpha-Beta Pruning Verified*][Nipkow2024].
-/

public section

namespace Cslib.Algorithms.Lean.Search.GameTree

universe u

variable {α : Type u} [LinearOrder α] [BoundedOrder α]

mutual

/-- The minimax value of a game tree: the value of a leaf, the largest minimax value of the
subtrees at a node of MAX (`⊥` if there are none) and the smallest at a node of MIN (`⊤` if there
are none). -/
@[expose] def minimax : GameTree α → α
  | leaf x => x
  | node .max ts => maxValue ⊥ ts
  | node .min ts => minValue ⊤ ts

/-- `maxValue v ts` folds the minimax values of `ts` into the running maximum `v`, from left to
right. -/
@[expose] def maxValue (v : α) : List (GameTree α) → α
  | [] => v
  | t :: ts => maxValue (max v (minimax t)) ts

/-- `minValue v ts` folds the minimax values of `ts` into the running minimum `v`, from left to
right. -/
@[expose] def minValue (v : α) : List (GameTree α) → α
  | [] => v
  | t :: ts => minValue (min v (minimax t)) ts

end

@[simp] theorem minimax_leaf (x : α) : (leaf x).minimax = x := by
  simp [minimax]

@[simp] theorem minimax_node_max (ts : List (GameTree α)) :
    (node .max ts).minimax = maxValue ⊥ ts := by
  simp [minimax]

@[simp] theorem minimax_node_min (ts : List (GameTree α)) :
    (node .min ts).minimax = minValue ⊤ ts := by
  simp [minimax]

@[simp] theorem maxValue_nil (v : α) : maxValue v [] = v := by
  simp [maxValue]

@[simp] theorem maxValue_cons (v : α) (t : GameTree α) (ts : List (GameTree α)) :
    maxValue v (t :: ts) = maxValue (max v t.minimax) ts := by
  simp [maxValue]

@[simp] theorem minValue_nil (v : α) : minValue v [] = v := by
  simp [minValue]

@[simp] theorem minValue_cons (v : α) (t : GameTree α) (ts : List (GameTree α)) :
    minValue v (t :: ts) = minValue (min v t.minimax) ts := by
  simp [minValue]

/-- The running maximum is the larger of the start value and the maximum over the list. -/
theorem maxValue_eq_max (v : α) (ts : List (GameTree α)) :
    maxValue v ts = max v (maxValue ⊥ ts) := by
  induction ts generalizing v with
  | nil => simp
  | cons t ts ih => rw [maxValue_cons, maxValue_cons, ih, ih (max ⊥ _)]; simp [max_assoc]

/-- The running minimum is the smaller of the start value and the minimum over the list. -/
theorem minValue_eq_min (v : α) (ts : List (GameTree α)) :
    minValue v ts = min v (minValue ⊤ ts) := by
  induction ts generalizing v with
  | nil => simp
  | cons t ts ih => rw [minValue_cons, minValue_cons, ih, ih (min ⊤ _)]; simp [min_assoc]

end Cslib.Algorithms.Lean.Search.GameTree
