/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.Game.Minimax

/-!
# Alpha-beta pruning on game trees

Alpha-beta search ([RussellNorvig2020], Section 5.2.3; [KnuthMoore1975]) computes the minimax value
of a game tree while skipping subtrees that cannot affect it. It searches a tree with a *window*
`[α, β]`: `α` is the value MAX is already assured of on the path to the root and `β` the value MIN
is already assured of. At a node of MAX the subtrees are searched from left to right, the window's
lower end rising to the best value found so far, and the remaining subtrees are skipped as soon as
that value reaches `β` (a *cut-off*); nodes of MIN are symmetric.

Two variants differ in what they return when the true value lies outside the window.

* **Fail-hard** (`GameTree.alphaBetaHard`): the value folded in at a node of MAX starts at `α`, and
  leaf values are clamped into the window, so the result always lies in `[α, β]`, even when the
  tree is a single leaf. It is exactly the minimax value clamped into the window
  (`GameTree.alphaBetaHard_eq`).
* **Fail-soft** (`GameTree.alphaBetaSoft`, the textbook's `MAX-VALUE` and `MIN-VALUE` of
  `ALPHA-BETA-SEARCH`): the value folded in at a node of MAX starts at `-∞`. When `α < β`, the
  result equals the minimax value if that lies strictly inside the window, is an upper bound for it
  at most `α` if the minimax value is at most `α` (the search *fails low*), and is a lower bound
  for it at least `β` if the minimax value is at least `β` (it *fails high*)
  (`GameTree.alphaBetaSoft_eq_minimax`, `GameTree.alphaBetaSoft_mem_Icc_of_minimax_le`,
  `GameTree.alphaBetaSoft_mem_Icc_of_le_minimax`). This is Knuth and Moore's specification of
  alpha-beta, strengthened by the bounds.

With the full window `[⊥, ⊤]` both compute the minimax value (`GameTree.alphaBetaHard_bot_top`,
`GameTree.alphaBetaSoft_bot_top`). The tree setting follows [Nipkow2024], who verifies fail-hard
and fail-soft alpha-beta in Isabelle/HOL on trees whose levels alternate between the players; here
every node names the player to move. Both variants are proved correct by structural induction on
the tree.

Applied to `g.unfold eval d s`, these are the textbook's depth-limited heuristic alpha-beta search
of a game `g` from the state `s` (`Game.unfold`). That they skip work, in the sense of making no
more queries to the game than minimax does, is proved in the query model in
`CslibFrontier.Algorithms.Lean.Search.Game.Query`.

## Main definitions

* `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaHard`: fail-hard alpha-beta search.
* `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaSoft`: fail-soft alpha-beta search.

## Main results

* `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaHard_eq`: for `α ≤ β`, fail-hard alpha-beta
  returns `max α (min (minimax t) β)`.
* `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaSoft_eq_minimax`,
  `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaSoft_mem_Icc_of_minimax_le`,
  `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaSoft_mem_Icc_of_le_minimax`: correctness of
  fail-soft alpha-beta for `α < β`, by the position of the minimax value relative to the window.
* `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaHard_bot_top`,
  `Cslib.Algorithms.Lean.Search.GameTree.alphaBetaSoft_bot_top`: with the full window, both
  variants return the minimax value.

## References

* [S. Russell, P. Norvig, *Artificial Intelligence: A Modern Approach*][RussellNorvig2020],
  Section 5.2.3.
* [D. E. Knuth, R. W. Moore, *An Analysis of Alpha-Beta Pruning*][KnuthMoore1975].
* [T. Nipkow, *Alpha-Beta Pruning Verified*][Nipkow2024].
-/

public section

namespace Cslib.Algorithms.Lean.Search.GameTree

universe u

variable {α : Type u} [LinearOrder α]

/-! ## Fail-hard alpha-beta -/

mutual

/-- Fail-hard alpha-beta search of a tree with the window `[a, b]`. A leaf value is clamped into
the window; see `alphaBetaHardMax` and `alphaBetaHardMin` for inner nodes. -/
@[expose] def alphaBetaHard (a b : α) : GameTree α → α
  | leaf x => max a (min x b)
  | node .max ts => alphaBetaHardMax a b ts
  | node .min ts => alphaBetaHardMin a b ts

/-- Fail-hard alpha-beta search of the subtrees `ts` of a node of MAX with the window `[a, b]`:
each subtree is searched with the current window and its value raises the lower end `a`; the
remaining subtrees are skipped once `a` reaches `b`. -/
@[expose] def alphaBetaHardMax (a b : α) : List (GameTree α) → α
  | [] => a
  | t :: ts =>
    let a' := max a (alphaBetaHard a b t)
    if b ≤ a' then a' else alphaBetaHardMax a' b ts

/-- Fail-hard alpha-beta search of the subtrees `ts` of a node of MIN with the window `[a, b]`:
each subtree is searched with the current window and its value lowers the upper end `b`; the
remaining subtrees are skipped once `b` reaches `a`. -/
@[expose] def alphaBetaHardMin (a b : α) : List (GameTree α) → α
  | [] => b
  | t :: ts =>
    let b' := min b (alphaBetaHard a b t)
    if b' ≤ a then b' else alphaBetaHardMin a b' ts

end

@[simp] theorem alphaBetaHard_leaf (a b x : α) : alphaBetaHard a b (leaf x) = max a (min x b) := by
  simp [alphaBetaHard]

@[simp] theorem alphaBetaHard_node_max (a b : α) (ts : List (GameTree α)) :
    alphaBetaHard a b (node .max ts) = alphaBetaHardMax a b ts := by
  simp [alphaBetaHard]

@[simp] theorem alphaBetaHard_node_min (a b : α) (ts : List (GameTree α)) :
    alphaBetaHard a b (node .min ts) = alphaBetaHardMin a b ts := by
  simp [alphaBetaHard]

@[simp] theorem alphaBetaHardMax_nil (a b : α) : alphaBetaHardMax a b [] = a := by
  simp [alphaBetaHardMax]

theorem alphaBetaHardMax_cons (a b : α) (t : GameTree α) (ts : List (GameTree α)) :
    alphaBetaHardMax a b (t :: ts) =
      if b ≤ max a (alphaBetaHard a b t) then max a (alphaBetaHard a b t)
      else alphaBetaHardMax (max a (alphaBetaHard a b t)) b ts := by
  simp [alphaBetaHardMax]

@[simp] theorem alphaBetaHardMin_nil (a b : α) : alphaBetaHardMin a b [] = b := by
  simp [alphaBetaHardMin]

theorem alphaBetaHardMin_cons (a b : α) (t : GameTree α) (ts : List (GameTree α)) :
    alphaBetaHardMin a b (t :: ts) =
      if min b (alphaBetaHard a b t) ≤ a then min b (alphaBetaHard a b t)
      else alphaBetaHardMin a (min b (alphaBetaHard a b t)) ts := by
  simp [alphaBetaHardMin]

variable [BoundedOrder α]

mutual

/-- **Correctness of fail-hard alpha-beta**: for a window `a ≤ b`, fail-hard alpha-beta search
returns the minimax value clamped into the window. For `a < b` this gives Knuth and Moore's
specification of alpha-beta ([KnuthMoore1975]): the result is at most `a` if the minimax value is,
equals the minimax value if that lies strictly inside the window, and is at least `b` if the
minimax value is. -/
theorem alphaBetaHard_eq (a b : α) (hab : a ≤ b) :
    (t : GameTree α) → alphaBetaHard a b t = max a (min t.minimax b)
  | leaf x => by simp
  | node .max ts => by simpa using alphaBetaHardMax_eq a b hab ts
  | node .min ts => by simpa using alphaBetaHardMin_eq a b hab ts

private theorem alphaBetaHardMax_eq (a b : α) (hab : a ≤ b) :
    (ts : List (GameTree α)) → alphaBetaHardMax a b ts = max a (min (maxValue ⊥ ts) b)
  | [] => by simp
  | t :: ts => by
    rw [alphaBetaHardMax_cons, alphaBetaHard_eq a b hab t, maxValue_cons, max_bot_left,
      maxValue_eq_max]
    split_ifs with h
    · grind
    · rw [alphaBetaHardMax_eq _ b (by grind) ts]
      grind

private theorem alphaBetaHardMin_eq (a b : α) (hab : a ≤ b) :
    (ts : List (GameTree α)) → alphaBetaHardMin a b ts = max a (min (minValue ⊤ ts) b)
  | [] => by simp [hab]
  | t :: ts => by
    rw [alphaBetaHardMin_cons, alphaBetaHard_eq a b hab t, minValue_cons, min_top_left,
      minValue_eq_min]
    split_ifs with h
    · grind
    · rw [alphaBetaHardMin_eq a _ (by grind) ts]
      grind

end

/-- With the full window `[⊥, ⊤]`, fail-hard alpha-beta search returns the minimax value. -/
@[simp] theorem alphaBetaHard_bot_top (t : GameTree α) : alphaBetaHard ⊥ ⊤ t = t.minimax := by
  simp [alphaBetaHard_eq ⊥ ⊤ bot_le t]

/-! ## Fail-soft alpha-beta -/

mutual

/-- Fail-soft alpha-beta search of a tree with the window `[a, b]` ([RussellNorvig2020],
Section 5.2.3, `ALPHA-BETA-SEARCH`, which starts it with the window `[-∞, +∞]`). A leaf returns
its value; see `alphaBetaSoftMax` and `alphaBetaSoftMin` for inner nodes. -/
@[expose] def alphaBetaSoft (a b : α) : GameTree α → α
  | leaf x => x
  | node .max ts => alphaBetaSoftMax a b ⊥ ts
  | node .min ts => alphaBetaSoftMin a b ⊤ ts

/-- Fail-soft alpha-beta search of the subtrees `ts` of a node of MAX with the window `[a, b]` and
best value `v` found so far (`MAX-VALUE`): each subtree is searched with the current window, its
value raises `v` and the lower end `a`; the remaining subtrees are skipped once `v` reaches `b`. -/
@[expose] def alphaBetaSoftMax (a b v : α) : List (GameTree α) → α
  | [] => v
  | t :: ts =>
    let v' := max v (alphaBetaSoft a b t)
    if b ≤ v' then v' else alphaBetaSoftMax (max a v') b v' ts

/-- Fail-soft alpha-beta search of the subtrees `ts` of a node of MIN with the window `[a, b]` and
best value `v` found so far (`MIN-VALUE`): each subtree is searched with the current window, its
value lowers `v` and the upper end `b`; the remaining subtrees are skipped once `v` reaches `a`. -/
@[expose] def alphaBetaSoftMin (a b v : α) : List (GameTree α) → α
  | [] => v
  | t :: ts =>
    let v' := min v (alphaBetaSoft a b t)
    if v' ≤ a then v' else alphaBetaSoftMin a (min b v') v' ts

end

@[simp] theorem alphaBetaSoft_leaf (a b x : α) : alphaBetaSoft a b (leaf x) = x := by
  simp [alphaBetaSoft]

@[simp] theorem alphaBetaSoft_node_max (a b : α) (ts : List (GameTree α)) :
    alphaBetaSoft a b (node .max ts) = alphaBetaSoftMax a b ⊥ ts := by
  simp [alphaBetaSoft]

@[simp] theorem alphaBetaSoft_node_min (a b : α) (ts : List (GameTree α)) :
    alphaBetaSoft a b (node .min ts) = alphaBetaSoftMin a b ⊤ ts := by
  simp [alphaBetaSoft]

@[simp] theorem alphaBetaSoftMax_nil (a b v : α) : alphaBetaSoftMax a b v [] = v := by
  simp [alphaBetaSoftMax]

theorem alphaBetaSoftMax_cons (a b v : α) (t : GameTree α) (ts : List (GameTree α)) :
    alphaBetaSoftMax a b v (t :: ts) =
      if b ≤ max v (alphaBetaSoft a b t) then max v (alphaBetaSoft a b t)
      else alphaBetaSoftMax (max a (max v (alphaBetaSoft a b t))) b
        (max v (alphaBetaSoft a b t)) ts := by
  simp [alphaBetaSoftMax]

@[simp] theorem alphaBetaSoftMin_nil (a b v : α) : alphaBetaSoftMin a b v [] = v := by
  simp [alphaBetaSoftMin]

theorem alphaBetaSoftMin_cons (a b v : α) (t : GameTree α) (ts : List (GameTree α)) :
    alphaBetaSoftMin a b v (t :: ts) =
      if min v (alphaBetaSoft a b t) ≤ a then min v (alphaBetaSoft a b t)
      else alphaBetaSoftMin a (min b (min v (alphaBetaSoft a b t)))
        (min v (alphaBetaSoft a b t)) ts := by
  simp [alphaBetaSoftMin]

/-- Knuth and Moore's specification of a fail-soft result `r` for the true value `v` and the
window `[a, b]`, with bounds: `v ≤ r ≤ a` if `v ≤ a`, `r = v` if `a < v < b`, and `b ≤ r ≤ v` if
`b ≤ v`. -/
private def SoftSpec (a b v r : α) : Prop :=
  (v ≤ a → v ≤ r ∧ r ≤ a) ∧ (a < v → v < b → r = v) ∧ (b ≤ v → b ≤ r ∧ r ≤ v)

mutual

private theorem softSpec_alphaBetaSoft (a b : α) (hab : a < b) :
    (t : GameTree α) → SoftSpec a b t.minimax (alphaBetaSoft a b t)
  | leaf x => by simp [SoftSpec]
  | node .max ts => by simpa using softSpec_alphaBetaSoftMax a b ⊥ hab bot_le ts
  | node .min ts => by simpa using softSpec_alphaBetaSoftMin a b ⊤ hab le_top ts

private theorem softSpec_alphaBetaSoftMax (a b v : α) (hab : a < b) (hv : v ≤ a) :
    (ts : List (GameTree α)) → SoftSpec a b (maxValue v ts) (alphaBetaSoftMax a b v ts)
  | [] => by simp [SoftSpec]
  | t :: ts => by
    have hc := softSpec_alphaBetaSoft a b hab t
    rw [alphaBetaSoftMax_cons, maxValue_cons]
    set c := alphaBetaSoft a b t
    split_ifs with h
    · rw [maxValue_eq_max]
      unfold SoftSpec at hc ⊢
      grind
    · have ih := softSpec_alphaBetaSoftMax (max a (max v c)) b (max v c) (by grind)
        (le_max_right _ _) ts
      rw [maxValue_eq_max] at ih ⊢
      unfold SoftSpec at hc ih ⊢
      grind

private theorem softSpec_alphaBetaSoftMin (a b v : α) (hab : a < b) (hv : b ≤ v) :
    (ts : List (GameTree α)) → SoftSpec a b (minValue v ts) (alphaBetaSoftMin a b v ts)
  | [] => by simp [SoftSpec]
  | t :: ts => by
    have hc := softSpec_alphaBetaSoft a b hab t
    rw [alphaBetaSoftMin_cons, minValue_cons]
    set c := alphaBetaSoft a b t
    split_ifs with h
    · rw [minValue_eq_min]
      unfold SoftSpec at hc ⊢
      grind
    · have ih := softSpec_alphaBetaSoftMin a (min b (min v c)) (min v c) (by grind)
        (min_le_right _ _) ts
      rw [minValue_eq_min] at ih ⊢
      unfold SoftSpec at hc ih ⊢
      grind

end

/-- **Correctness of fail-soft alpha-beta, inside the window** ([KnuthMoore1975]): if the minimax
value lies strictly inside the window `(a, b)`, fail-soft alpha-beta search returns it. -/
theorem alphaBetaSoft_eq_minimax {a b : α} {t : GameTree α} (ha : a < t.minimax)
    (hb : t.minimax < b) : alphaBetaSoft a b t = t.minimax :=
  (softSpec_alphaBetaSoft a b (ha.trans hb) t).2.1 ha hb

/-- **Correctness of fail-soft alpha-beta, failing low**: for a window `a < b`, if the minimax value
is at most `a`, fail-soft alpha-beta search returns an upper bound for it that is at most `a`.
Knuth and Moore's specification ([KnuthMoore1975]) asks only for the result to be at most `a`. -/
theorem alphaBetaSoft_mem_Icc_of_minimax_le {a b : α} {t : GameTree α} (hab : a < b)
    (h : t.minimax ≤ a) : alphaBetaSoft a b t ∈ Set.Icc t.minimax a :=
  (softSpec_alphaBetaSoft a b hab t).1 h

/-- **Correctness of fail-soft alpha-beta, failing high**: for a window `a < b`, if the minimax
value is at least `b`, fail-soft alpha-beta search returns a lower bound for it that is at least
`b`. Knuth and Moore's specification ([KnuthMoore1975]) asks only for the result to be at least
`b`. -/
theorem alphaBetaSoft_mem_Icc_of_le_minimax {a b : α} {t : GameTree α} (hab : a < b)
    (h : b ≤ t.minimax) : alphaBetaSoft a b t ∈ Set.Icc b t.minimax :=
  (softSpec_alphaBetaSoft a b hab t).2.2 h

/-- With the full window `[⊥, ⊤]`, fail-soft alpha-beta search returns the minimax value. -/
@[simp] theorem alphaBetaSoft_bot_top (t : GameTree α) : alphaBetaSoft ⊥ ⊤ t = t.minimax := by
  rcases eq_or_lt_of_le (bot_le : (⊥ : α) ≤ ⊤) with h | h
  · have hx (x : α) : x = ⊥ := le_antisymm (h ▸ le_top) bot_le
    rw [hx (alphaBetaSoft ⊥ ⊤ t), hx t.minimax]
  · have hs := softSpec_alphaBetaSoft ⊥ ⊤ h t
    unfold SoftSpec at hs
    rcases eq_or_lt_of_le (bot_le : ⊥ ≤ t.minimax) with h₁ | h₁
    · grind
    rcases eq_or_lt_of_le (le_top : t.minimax ≤ ⊤) with h₂ | h₂
    · grind
    · exact hs.2.1 h₁ h₂

end Cslib.Algorithms.Lean.Search.GameTree
