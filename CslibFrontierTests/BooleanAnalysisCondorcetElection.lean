/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.CondorcetElection
public import CslibFrontier.Foundations.Data.BitString.Threshold

/-! # Dictators, negated dictators and the majority of three voters in Condorcet elections

A dictator `x ↦ x_i` is unanimous and always gives a Condorcet winner, the top candidate of voter
`i`, so the hypotheses of Arrow's Theorem
(`Cslib.BitString.exists_eq_of_forall_exists_isCondorcetWinner`) hold together. A negated dictator
`x ↦ ¬x_i` also always gives a Condorcet winner, voter `i`'s bottom candidate, but is not
unanimous: Arrow's Theorem needs unanimity to exclude it. A dictator attains the bound
`7/9 + 2/9 W^1` of Corollary 2.59 with equality. For the majority of three voters the probability
of a Condorcet winner is `17/18` [O'Donnell, Exercise 2.50][ODonnell2014], `204` of the `216`
profiles.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisCondorcetElection

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- Every ranking has a candidate ranked above its successor and below its predecessor: its top
candidate. -/
theorem exists_top (σ : Equiv.Perm (Fin 3)) :
    ∃ c : Fin 3, σ c < σ (c + 1) ∧ ¬ σ (c - 1) < σ c := by
  revert σ
  decide

/-- Every ranking has a candidate ranked below its successor and above its predecessor: its bottom
candidate. -/
theorem exists_bottom (σ : Equiv.Perm (Fin 3)) :
    ∃ c : Fin 3, ¬ σ c < σ (c + 1) ∧ σ (c - 1) < σ c := by
  revert σ
  decide

variable {ι : Type*}

/-- A dictator always gives a Condorcet winner, so Arrow's hypotheses are satisfiable. -/
theorem dictator_exists_isCondorcetWinner (i : ι) (π : ι → Equiv.Perm (Fin 3)) :
    ∃ c, IsCondorcetWinner (fun x => x i) π c := by
  obtain ⟨c, h₁, h₂⟩ := exists_top (π i)
  exact ⟨c, by simp only [IsCondorcetWinner, condorcetVotes, decide_eq_true_eq,
    decide_eq_false_iff_not, sub_add_cancel]; exact ⟨h₁, h₂⟩⟩

-- Arrow's Theorem recovers the dictator from its own hypotheses.
example [Finite ι] (i : ι) : ∃ j, (fun x : ι → Bool => x i) = fun x => x j :=
  exists_eq_of_forall_exists_isCondorcetWinner rfl (dictator_exists_isCondorcetWinner i)

/-- A negated dictator always gives a Condorcet winner. -/
theorem negDictator_exists_isCondorcetWinner (i : ι) (π : ι → Equiv.Perm (Fin 3)) :
    ∃ c, IsCondorcetWinner (fun x => !x i) π c := by
  obtain ⟨c, h₁, h₂⟩ := exists_bottom (π i)
  exact ⟨c, by simp only [IsCondorcetWinner, condorcetVotes, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, sub_add_cancel]; exact ⟨h₁, h₂⟩⟩

/-- A negated dictator is not unanimous, so Arrow's Theorem does not apply to it. -/
theorem negDictator_not_unanimous (i : ι) : (fun x : ι → Bool => !x i) (fun _ => true) ≠ true := by
  simp

/-- A dictator has probability one of a Condorcet winner, so Corollary 2.59's bound
`7/9 + 2/9 W^1 = 1` is attained. -/
theorem condorcetWinnerProb_dictator [Fintype ι] [DecidableEq ι] (i : ι) :
    condorcetWinnerProb (fun x : ι → Bool => x i) = 1 := by
  simp [condorcetWinnerProb, dictator_exists_isCondorcetWinner i]

/-- **The majority of three voters** [O'Donnell, Exercise 2.50][ODonnell2014]: `204` of the `216`
profiles of rankings have a Condorcet winner. -/
theorem card_majority_three :
    #{π : Fin 3 → Equiv.Perm (Fin 3) | ∃ c, IsCondorcetWinner (majority 3) π c} = 204 := by
  decide +kernel

/-- **The majority of three voters** [O'Donnell, Exercise 2.50][ODonnell2014]: the probability of
a Condorcet winner is `17/18`. -/
theorem condorcetWinnerProb_majority_three : condorcetWinnerProb (majority 3) = 17 / 18 := by
  rw [condorcetWinnerProb, Fintype.expect_eq_sum_div_card, ← sum_filter, sum_const,
    card_majority_three, Fintype.card_fun, Fintype.card_perm]
  norm_num [Nat.factorial]

end CslibFrontierTests.BooleanAnalysisCondorcetElection
