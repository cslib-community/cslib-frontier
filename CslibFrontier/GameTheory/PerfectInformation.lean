/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.SetTheory.Descriptive.Tree

/-!
# Finite two-person games of perfect information

A two-person game of perfect information (`PerfectInfoGame`) is given by its legal positions, the
finite sequences of moves played so far, together with the player to move at each position and the
victor of each finished play. The positions form a tree in the sense of descriptive set theory
(Mathlib's `Descriptive.tree`: a set of finite sequences closed under prefixes) that contains the
empty sequence, the initial position. The game is over at a position that no legal move continues
(`PerfectInfoGame.IsOver`). Players are `true` (the first player) and `false` (the second); the
player to move (`turn`) is an arbitrary function of the position, so alternating play is the case
`turn x = decide (Even x.length)`. Each position may have any set of legal moves, finite or not.

A strategy for player `b` (`PerfectInfoGame.Strategy`) chooses a legal move at every position that
some legal move continues; only its choices at positions where `b` is to move matter. A play
follows the strategy when every move made at such a position is the strategy's choice, and the
strategy is winning when every finished play that follows it is won by `b`.

`PerfectInfoGame.CanWin` is backward induction: `G.CanWin b k x` says that from position `x`,
player `b` can force a win when at most `k` further moves are played.

## Main results

* `PerfectInfoGame.not_canWin_iff`: at every position and depth, exactly one player can force a
  win.
* `PerfectInfoGame.exists_isWinning_iff_canWin`: if every play ends after at most `n` moves, then
  `b` has a winning strategy exactly when backward induction to depth `n` from the initial position
  says so.
* `PerfectInfoGame.exists_isWinning_iff_not_exists_isWinning`: in such a game, `b` has a winning
  strategy exactly when the other player has none.
* `PerfectInfoGame.exists_isWinning`: **Zermelo's theorem** [Arora and Barak, Chapter 4,
  Exercise 8][AroraBarak07]: in every such game one of the two players has a winning strategy.

The source's finiteness is "an a priori upperbound `n` on the number of moves after which the game
is over and one of the two players is declared the victor — there are no draws" (printed p. 89 /
PDF p. 105). It is the hypothesis `∀ x ∈ G.tree, x.length ≤ n`, and the absence of draws is the
type `Bool` of `winner`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Chapter 4,
  Exercise 8.
-/

public section

namespace Cslib.GameTheory

/-- A two-person game of perfect information. Its legal positions are the finite sequences of moves
played so far, starting from the empty sequence; the player to move and, on finished plays, the
victor are functions of the position. Players are `true` (the first player) and `false` (the
second). -/
structure PerfectInfoGame (M : Type*) where
  /-- The legal positions: the sequences of moves played so far, closed under prefixes. -/
  tree : Descriptive.tree M
  /-- The initial position, before any move, is legal. -/
  nil_mem : [] ∈ tree
  /-- The player to move at a position. -/
  turn : List M → Bool
  /-- The victor of a finished play; there are no draws. -/
  winner : List M → Bool

namespace PerfectInfoGame

variable {M : Type*} (G : PerfectInfoGame M)

/-- The game is over at the position `x` when no legal move continues it. -/
@[expose] def IsOver (x : List M) : Prop :=
  ∀ a, x ++ [a] ∉ G.tree

/-- A strategy for player `b`: a legal move at every position that some legal move continues. Only
its choices at the positions where `b` is to move matter. -/
structure Strategy (b : Bool) where
  /-- The move chosen at a position that some legal move continues. -/
  move : (x : List M) → (∃ a, x ++ [a] ∈ G.tree) → M
  /-- The chosen move is legal. -/
  move_mem : ∀ x h, x ++ [move x h] ∈ G.tree

variable {G} {b : Bool}

/-- A sequence of moves follows the strategy `σ` of player `b` when every move made at a position
where `b` is to move is the move `σ` chooses there. -/
@[expose] def Strategy.Follows (σ : G.Strategy b) (p : List M) : Prop :=
  ∀ k (hk : k < p.length), G.turn (p.take k) = b → ∀ h, p[k] = σ.move (p.take k) h

/-- A strategy of player `b` is winning when `b` wins every finished play that follows it. -/
@[expose] def Strategy.IsWinning (σ : G.Strategy b) : Prop :=
  ∀ p ∈ G.tree, G.IsOver p → σ.Follows p → G.winner p = b

variable (G) in
/-- Backward induction: `G.CanWin b k x` says that player `b` can force a win from the position `x`
when at most `k` further moves are played. A finished position is won by its victor. At an
unfinished one, `b` needs one move to a position from which `b` can force a win when `b` is to move,
and every move must lead to such a position otherwise. With no move left (`k = 0`) the position is
judged by its victor. -/
@[expose] def CanWin (b : Bool) : ℕ → List M → Prop
  | 0, x => G.winner x = b
  | k + 1, x => (G.IsOver x → G.winner x = b) ∧
      (¬ G.IsOver x → if G.turn x = b then ∃ a, x ++ [a] ∈ G.tree ∧ CanWin b k (x ++ [a])
        else ∀ a, x ++ [a] ∈ G.tree → CanWin b k (x ++ [a]))

theorem canWin_iff_of_isOver {k : ℕ} {x : List M} (hx : G.IsOver x) :
    G.CanWin b k x ↔ G.winner x = b := by
  cases k with
  | zero => rfl
  | succ k => simp only [CanWin, hx, forall_const, not_true_eq_false, false_implies, and_true]

/-- **Determinacy of backward induction**: at every position and depth, exactly one player can
force a win. -/
theorem not_canWin_iff {k : ℕ} {x : List M} : ¬ G.CanWin b k x ↔ G.CanWin (!b) k x := by
  induction k generalizing x b with
  | zero => cases b <;> simp [CanWin]
  | succ k ih =>
    by_cases hx : G.IsOver x
    · rw [canWin_iff_of_isOver hx, canWin_iff_of_isOver hx]
      cases b <;> simp
    · simp only [CanWin, hx, false_implies, true_and, not_false_eq_true, true_implies]
      have hturn : (G.turn x = !b) ↔ ¬ G.turn x = b := by cases b <;> simp
      split_ifs with ht ht' ht'
      · exact absurd ht (hturn.1 ht')
      · push Not
        simp only [ih]
      · push Not
        simp only [ih]
      · exact absurd (hturn.2 ht) ht'

private theorem Strategy.move_congr (σ : G.Strategy b) {x y : List M} (e : x = y) (hx hy) :
    σ.move x hx = σ.move y hy := by
  subst e
  rfl

theorem Strategy.follows_append_singleton {σ : G.Strategy b} {x : List M} {a : M}
    (hx : σ.Follows x) (ha : G.turn x = b → ∀ h, a = σ.move x h) : σ.Follows (x ++ [a]) := by
  intro k hk ht h
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · have e := List.take_append_of_le_length (l₂ := [a]) hk.le
    rw [e] at ht
    rw [List.getElem_append_left hk, σ.move_congr e h (e ▸ h)]
    exact hx k hk ht _
  · have e : (x ++ [a]).take x.length = x := List.take_left
    rw [e] at ht
    rw [σ.move_congr e h (e ▸ h)]
    simpa using ha ht _

/-- Under a move bound `n`, a winning strategy of `b` lets `b` force a win by backward induction
from every legal position that follows it, with enough moves left. -/
theorem Strategy.IsWinning.canWin {σ : G.Strategy b} (hσ : σ.IsWinning) {n : ℕ}
    (hn : ∀ x ∈ G.tree, x.length ≤ n) :
    ∀ k x, x ∈ G.tree → σ.Follows x → n ≤ x.length + k → G.CanWin b k x := by
  intro k
  induction k with
  | zero =>
    intro x hx hf hle
    have hover : G.IsOver x := fun a ha => by
      have := hn _ ha
      simp only [List.length_append, List.length_singleton] at this
      omega
    exact (canWin_iff_of_isOver hover).2 (hσ x hx hover hf)
  | succ k ih =>
    intro x hx hf hle
    refine ⟨fun hover => hσ x hx hover hf, fun hover => ?_⟩
    have hne : ∃ a, x ++ [a] ∈ G.tree := by
      simpa [IsOver] using hover
    split_ifs with ht
    · exact ⟨σ.move x hne, σ.move_mem x hne,
        ih _ (σ.move_mem x hne) (σ.follows_append_singleton hf fun _ _ => rfl)
          (by simp; omega)⟩
    · exact fun a ha => ih _ ha (σ.follows_append_singleton hf fun h => absurd h ht)
        (by simp; omega)

/-- Under a move bound `n`, player `b` has a winning strategy exactly when backward induction to
depth `n` from the initial position says that `b` can force a win. -/
theorem exists_isWinning_iff_canWin {n : ℕ} (hn : ∀ x ∈ G.tree, x.length ≤ n) :
    (∃ σ : G.Strategy b, σ.IsWinning) ↔ G.CanWin b n [] := by
  classical
  refine ⟨fun ⟨σ, hσ⟩ => hσ.canWin hn n [] G.nil_mem (fun k hk => by simp at hk) (by simp),
    fun h => ?_⟩
  -- At every position, move to a position from which `b` can still force a win, if there is one.
  let good (x : List M) : Prop := ∃ a, x ++ [a] ∈ G.tree ∧ G.CanWin b (n - x.length - 1) (x ++ [a])
  let σ : G.Strategy b :=
    { move := fun x h => if hc : good x then hc.choose else h.choose
      move_mem := fun x h => by
        split_ifs with hc
        · exact hc.choose_spec.1
        · exact h.choose_spec }
  refine ⟨σ, fun p hp hover hf => ?_⟩
  -- Along a play that follows `σ`, `b` can force a win from every prefix.
  have key : ∀ j ≤ p.length, G.CanWin b (n - j) (p.take j) := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      intro hj
      have hj' : j < p.length := hj
      have htake : p.take (j + 1) = p.take j ++ [p[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some]
      have hmem : p.take j ++ [p[j]] ∈ G.tree := htake ▸
        Descriptive.Tree.mem_of_prefix (List.take_prefix _ _) hp
      have hlen := hn _ hmem
      simp only [List.length_append, List.length_take, List.length_singleton,
        Nat.min_eq_left hj'.le] at hlen
      have hcan := ih hj'.le
      rw [show n - j = (n - (j + 1)) + 1 by omega] at hcan
      have hnot : ¬ G.IsOver (p.take j) := fun hov => hov _ hmem
      have hcan := hcan.2 hnot
      rw [htake]
      split_ifs at hcan with ht
      · have hgood : good (p.take j) := by
          obtain ⟨a, ha, hwin⟩ := hcan
          refine ⟨a, ha, ?_⟩
          simpa [Nat.min_eq_left hj'.le, Nat.sub_sub] using hwin
        have hpj : p[j] = hgood.choose := by
          rw [hf j hj' ht ⟨_, hmem⟩]
          simp [σ, hgood]
        rw [hpj]
        simpa [Nat.min_eq_left hj'.le, Nat.sub_sub] using hgood.choose_spec.2
      · exact hcan _ hmem
  simpa using (canWin_iff_of_isOver hover).1 (by simpa using key p.length le_rfl)

/-- Under a move bound, player `b` has a winning strategy exactly when the other player has none. -/
theorem exists_isWinning_iff_not_exists_isWinning {n : ℕ} (hn : ∀ x ∈ G.tree, x.length ≤ n) :
    (∃ σ : G.Strategy b, σ.IsWinning) ↔ ¬ ∃ τ : G.Strategy (!b), τ.IsWinning := by
  rw [exists_isWinning_iff_canWin hn, exists_isWinning_iff_canWin hn, not_canWin_iff,
    Bool.not_not]

/-- **Zermelo's theorem** [Arora and Barak, Chapter 4, Exercise 8][AroraBarak07]: in every
two-person game of perfect information with an a priori bound `n` on the number of moves after which
the game is over and one of the players is declared the victor, one of the two players has a winning
strategy. By `exists_isWinning_iff_not_exists_isWinning`, exactly one of them has one. -/
theorem exists_isWinning {n : ℕ} (hn : ∀ x ∈ G.tree, x.length ≤ n) :
    (∃ σ : G.Strategy true, σ.IsWinning) ∨ ∃ σ : G.Strategy false, σ.IsWinning := by
  by_cases h : ∃ σ : G.Strategy false, σ.IsWinning
  · exact .inr h
  · exact .inl ((exists_isWinning_iff_not_exists_isWinning hn).2 h)

end PerfectInfoGame

end Cslib.GameTheory
