/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.PerfectInformation

/-! Checked instance of Zermelo's theorem (`Cslib.GameTheory.PerfectInfoGame.exists_isWinning`):
in sequential matching pennies the first player names a bit, the second player names a bit, and the
first player wins when the bits agree. Every play has two moves, so the move bound holds with
`n = 2`; backward induction shows that the second player, and only the second player, has a winning
strategy. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PerfectInformation

open Cslib.GameTheory PerfectInfoGame

/-- The positions of sequential matching pennies: at most two bits. -/
def penniesTree : Descriptive.tree Bool :=
  ⟨{x | x.length ≤ 2}, fun x a h => by
    simp only [Set.mem_ofPred_eq, List.length_append, List.length_singleton] at h ⊢
    omega⟩

theorem mem_penniesTree {x : List Bool} : x ∈ penniesTree ↔ x.length ≤ 2 := Iff.rfl

/-- Sequential matching pennies: the first player moves first, and wins when the bits agree. -/
def pennies : PerfectInfoGame Bool where
  tree := penniesTree
  nil_mem := by simp [mem_penniesTree]
  turn x := decide (x.length = 0)
  winner x := decide (x[0]? = x[1]?)

theorem pennies_bound : ∀ x ∈ pennies.tree, x.length ≤ 2 := fun _ hx => hx

example : (∃ σ : pennies.Strategy true, σ.IsWinning) ∨ ∃ σ : pennies.Strategy false, σ.IsWinning :=
  exists_isWinning pennies_bound

/-- The second player wins by naming the other bit. -/
theorem canWin_false : pennies.CanWin false 2 [] := by
  refine ⟨fun h => absurd (h true) (by simp [pennies, mem_penniesTree]), fun _ => ?_⟩
  simp only [pennies, List.length_nil, decide_true, Bool.true_eq_false, ↓reduceIte]
  intro a _
  refine ⟨fun h => absurd (h (!a)) (by simp [mem_penniesTree]), fun _ => ?_⟩
  simp only [List.nil_append, List.length_singleton, Nat.one_ne_zero, decide_false, ↓reduceIte]
  exact ⟨!a, by simp [mem_penniesTree], by cases a <;> rfl⟩

example : ∃ σ : pennies.Strategy false, σ.IsWinning :=
  (exists_isWinning_iff_canWin pennies_bound).2 canWin_false

example : ¬ ∃ σ : pennies.Strategy true, σ.IsWinning :=
  (exists_isWinning_iff_not_exists_isWinning (b := false) pennies_bound).1
    ((exists_isWinning_iff_canWin pennies_bound).2 canWin_false)

end CslibFrontierTests.PerfectInformation
