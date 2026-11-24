/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Evolutionary.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Evolutionarily stable strategies: checked instances

Ordinary `module` client of `CslibFrontier.GameTheory.Evolutionary.Basic` exercising:

1. Hawks and Doves (`hawkDove`, [Suri2007], Figure 29.1, p. 719, and Exercise 29.2, p. 735):
   * `V = 4, C = 2`: pure Hawk `![1, 0]` is the unique ESS, Dove is not an ESS, `(![1, 0], ![1, 0])`
     is a symmetric Nash equilibrium via `isESS_iff_isNash_and_forall_lt`, and `isESS_iff` directly
     yields the invasion threshold of Definition 29.1;
   * `V = 2, C = 4`: mixed strategy `![1 / 2, 1 / 2]` is the unique ESS (neither pure strategy is);
   * boundary `V = C = 2`: pure Hawk `![1, 0]` is the unique ESS (tie in the first condition);
   * boundary `V = C = 0`: no ESS exists, showing `0 < V` cannot be dropped.
2. Prisoner's Dilemma ([Suri2007], Exercise 29.1, p. 735): pure Defect `![0, 1]` is the unique ESS.
3. Symmetric Nash equilibrium that is not an ESS, and non-uniqueness of ESS: in the `2 × 2`
   coordination game `!![1, 0; 0, 1]`, `![1 / 2, 1 / 2]` is a symmetric Nash equilibrium that is
   not an ESS, whereas both pure strategies `![1, 0]` and `![0, 1]` are ESSs.
4. Games with a Nash equilibrium and no ESS ([Suri2007], Exercise 29.4, p. 735, and counterexamples
   to the literal second sentence of Exercise 29.3, p. 735):
   * the `2 × 2` zero game `⟨0, 0⟩` and a nonzero constant-column symmetric game `!![1, 2; 1, 2]`
     have symmetric Nash equilibria but no ESS;
   * Rock–Paper–Scissors (a standard witness for Exercise 29.4, not printed in [Suri2007]) has
     symmetric Nash equilibrium `![1 / 3, 1 / 3, 1 / 3]` and no ESS.
5. Model boundaries: an asymmetric game (`G.B ≠ G.Aᵀ`) where `G.IsESS ![1, 0]` holds yet
   `¬ G.IsNash ![1, 0] ![1, 0]` (showing `hG : G.B = G.Aᵀ` cannot be dropped from Theorem 29.2),
   an empty strategy set (`Empty`, no ESS), and a singleton strategy set (`Fin 1`, unique ESS).
-/

public section

namespace CslibFrontierTests.GameTheory.Evolutionary

open Cslib.GameTheory Cslib.GameTheory.BimatrixGame Matrix

private theorem isMixedStrategy_fin2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    IsMixedStrategy ![a, b] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> simpa, by simpa [Fin.sum_univ_two] using h⟩

private theorem isMixedStrategy_fin3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : IsMixedStrategy ![a, b, c] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> simpa,
    by simpa [Fin.sum_univ_three] using h⟩

/-! ### Hawks and Doves -/

theorem hawkDove_gt_isESS_hawk : (hawkDove 4 2).IsESS ![1, 0] :=
  (isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)).2 rfl

theorem hawkDove_gt_not_isESS_dove : ¬ (hawkDove 4 2).IsESS ![0, 1] := by
  intro h
  have h0 := congrFun ((isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)).1 h) 0
  norm_num at h0

theorem hawkDove_gt_isNash_hawk : (hawkDove 4 2).IsNash ![1, 0] ![1, 0] :=
  ((isESS_iff_isNash_and_forall_lt (hawkDove_B 4 2)).1 hawkDove_gt_isESS_hawk).1

/-- Direct Definition 29.1 (`isESS_iff`) access from an ordinary `module` client. -/
theorem hawkDove_gt_invasion_threshold :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      (1 - ε) * (hawkDove 4 2).payoff₁ ![0, 1] ![1, 0] +
        ε * (hawkDove 4 2).payoff₁ ![0, 1] ![0, 1] <
      (1 - ε) * (hawkDove 4 2).payoff₁ ![1, 0] ![1, 0] +
        ε * (hawkDove 4 2).payoff₁ ![1, 0] ![0, 1] := by
  have hne : (![0, 1] : Fin 2 → ℝ) ≠ ![1, 0] := fun h => by
    have h0 := congrFun h 0
    norm_num at h0
  exact (isESS_iff.1 hawkDove_gt_isESS_hawk).2 ![0, 1]
    (isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num)) hne

theorem hawkDove_lt_isESS_mixed : (hawkDove 2 4).IsESS ![1 / 2, 1 / 2] := by
  rw [isESS_hawkDove_iff_of_le (by norm_num) (by norm_num)]
  ext i
  fin_cases i <;> norm_num

theorem hawkDove_lt_not_isESS_hawk : ¬ (hawkDove 2 4).IsESS ![1, 0] := by
  intro h
  have h0 := congrFun ((isESS_hawkDove_iff_of_le (by norm_num) (by norm_num)).1 h) 0
  norm_num at h0

theorem hawkDove_lt_not_isESS_dove : ¬ (hawkDove 2 4).IsESS ![0, 1] := by
  intro h
  have h0 := congrFun ((isESS_hawkDove_iff_of_le (by norm_num) (by norm_num)).1 h) 0
  norm_num at h0

/-- Boundary `V = C > 0`: pure Hawk is the unique ESS via the tie-breaking branch. -/
theorem hawkDove_eq_isESS_hawk : (hawkDove 2 2).IsESS ![1, 0] := by
  rw [isESS_hawkDove_iff_of_le (by norm_num) le_rfl]
  ext i
  fin_cases i <;> norm_num

/-- Boundary `V = C = 0`: `hawkDove 0 0` is the zero game and has no ESS (`0 < V` is necessary). -/
theorem hawkDove_zero_not_exists_isESS : ¬ ∃ s, (hawkDove 0 0).IsESS s := by
  rw [exists_isESS_fin_two_iff]
  norm_num [hawkDove_A]

/-! ### Prisoner's Dilemma (Exercise 29.1) -/

/-- A symmetric Prisoner's Dilemma (`0` = Cooperate, `1` = Defect, payoffs `0 < 1 < 3 < 5`). -/
def prisonersDilemma : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![3, 0; 5, 1], !![3, 0; 5, 1]ᵀ⟩

theorem prisonersDilemma_isESS_iff {s : Fin 2 → ℝ} :
    prisonersDilemma.IsESS s ↔ s = ![0, 1] := by
  rw [isESS_fin_two_iff]
  simp only [prisonersDilemma, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
  constructor
  · rintro ⟨hs, ⟨-, h | ⟨h, -⟩⟩ | ⟨h0, -⟩ | ⟨-, h, -⟩⟩
    · linarith
    · linarith
    · have hsum := hs.sum_eq_one
      rw [Fin.sum_univ_two, h0, zero_add] at hsum
      ext i
      fin_cases i
      · exact h0
      · exact hsum
    · linarith
  · rintro rfl
    refine ⟨isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num),
      Or.inr (Or.inl ⟨rfl, Or.inl (by norm_num)⟩)⟩

theorem prisonersDilemma_not_isESS_cooperate : ¬ prisonersDilemma.IsESS ![1, 0] := by
  intro h
  have h0 := congrFun (prisonersDilemma_isESS_iff.1 h) 0
  norm_num at h0

/-! ### Symmetric Nash equilibrium that is not an ESS, and multiple ESSs -/

/-- The `2 × 2` coordination game. -/
def coordGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![1, 0; 0, 1], !![1, 0; 0, 1]ᵀ⟩

theorem coordGame_isNash_half : coordGame.IsNash ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] := by
  have hmix := isMixedStrategy_fin2 (by norm_num) (by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  refine isNash_iff.2
    ⟨isBestResponse₁_iff.2 ⟨hmix, fun i _ => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
      isBestResponse₂_iff.2 ⟨hmix, fun j _ => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · fin_cases i <;> fin_cases i' <;> norm_num [coordGame, mulVec, dotProduct, Fin.sum_univ_two]
  · fin_cases j <;> fin_cases j' <;> norm_num [coordGame, vecMul, dotProduct, Fin.sum_univ_two]

theorem coordGame_not_isESS_half : ¬ coordGame.IsESS ![1 / 2, 1 / 2] := by
  rw [isESS_fin_two_iff]
  simp only [coordGame, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩⟩ <;> linarith

theorem coordGame_isESS_zero : coordGame.IsESS ![1, 0] := by
  rw [isESS_fin_two_iff]
  refine ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num), Or.inl ⟨rfl, Or.inl ?_⟩⟩
  norm_num [coordGame]

theorem coordGame_isESS_one : coordGame.IsESS ![0, 1] := by
  rw [isESS_fin_two_iff]
  refine ⟨isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num), Or.inr (Or.inl ⟨rfl, Or.inl ?_⟩)⟩
  norm_num [coordGame]

/-! ### Counterexamples to literal Exercise 29.3 (`2 × 2` games with no ESS) -/

/-- The `2 × 2` zero game: symmetric, has a symmetric Nash equilibrium, and has no ESS. -/
def zeroGame : BimatrixGame (Fin 2) (Fin 2) := ⟨0, 0⟩

theorem zeroGame_symm : zeroGame.B = zeroGame.Aᵀ := by
  simp only [zeroGame, transpose_zero]

theorem zeroGame_isNash_pure : zeroGame.IsNash ![1, 0] ![1, 0] := by
  have hmix := isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num)
  refine isNash_iff.2
    ⟨isBestResponse₁_iff.2 ⟨hmix, fun _ _ => isPureBestResponse₁_iff.2 fun _ => ?_⟩,
      isBestResponse₂_iff.2 ⟨hmix, fun _ _ => isPureBestResponse₂_iff.2 fun _ => ?_⟩⟩ <;>
    simp only [zeroGame, zero_mulVec, vecMul_zero, Pi.zero_apply, le_rfl]

theorem zeroGame_not_exists_isESS : ¬ ∃ s, zeroGame.IsESS s := by
  rw [exists_isESS_fin_two_iff, zeroGame]
  rintro (h | h) <;> exact h rfl

/-- A nonzero `2 × 2` symmetric game whose columns are both constant also has no ESS. -/
def constColGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![1, 2; 1, 2], !![1, 2; 1, 2]ᵀ⟩

theorem constColGame_symm : constColGame.B = constColGame.Aᵀ := by
  rw [constColGame]

theorem constColGame_not_exists_isESS : ¬ ∃ s, constColGame.IsESS s := by
  rw [exists_isESS_fin_two_iff]
  norm_num [constColGame]

/-! ### Rock–Paper–Scissors (witness for Exercise 29.4; not printed in [Suri2007]) -/

/-- Rock–Paper–Scissors: a symmetric `3 × 3` game with a symmetric Nash equilibrium and no ESS. -/
def rps : BimatrixGame (Fin 3) (Fin 3) :=
  ⟨!![0, -1, 1; 1, 0, -1; -1, 1, 0], !![0, -1, 1; 1, 0, -1; -1, 1, 0]ᵀ⟩

theorem rps_symm : rps.B = rps.Aᵀ := by
  rw [rps]

private theorem rps_payoff₁_skew (x y : Fin 3 → ℝ) :
    rps.payoff₁ x y + rps.payoff₁ y x = 0 := by
  simp only [payoff₁_eq_dotProduct, rps, dotProduct, mulVec, Fin.sum_univ_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, cons_val_fin_one, tail_cons, vecHead]
  ring

private theorem rps_payoff₁_uniform_left (s : Fin 3 → ℝ) :
    rps.payoff₁ ![1 / 3, 1 / 3, 1 / 3] s = 0 := by
  simp only [payoff₁_eq_dotProduct, rps, dotProduct, mulVec, Fin.sum_univ_three, of_apply,
    cons_val', cons_val_zero, cons_val_one, cons_val_two, cons_val_fin_one, tail_cons, vecHead]
  ring

theorem rps_isNash_uniform :
    rps.IsNash ![1 / 3, 1 / 3, 1 / 3] ![1 / 3, 1 / 3, 1 / 3] := by
  have hmix := isMixedStrategy_fin3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1)
  refine isNash_iff.2
    ⟨isBestResponse₁_iff.2 ⟨hmix, fun i _ => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
      isBestResponse₂_iff.2 ⟨hmix, fun j _ => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · fin_cases i <;> fin_cases i' <;> norm_num [rps, mulVec, dotProduct, Fin.sum_univ_three]
  · fin_cases j <;> fin_cases j' <;> norm_num [rps, vecMul, dotProduct, Fin.sum_univ_three]

theorem rps_not_isESS (s : Fin 3 → ℝ) : ¬ rps.IsESS s := by
  intro h
  have hcond := (isESS_iff_forall_lt_or.1 h).2
  have hself : rps.payoff₁ s s = 0 := by linarith [rps_payoff₁_skew s s]
  have hlt : ∀ t, IsMixedStrategy t → t ≠ s → rps.payoff₁ t s < 0 := fun t ht hne => by
    rcases hcond t ht hne with h1 | ⟨h1, h2⟩
    · linarith
    · have hskew := rps_payoff₁_skew t s
      have hself_t : rps.payoff₁ t t = 0 := by linarith [rps_payoff₁_skew t t]
      linarith
  by_cases hs : s = ![1 / 3, 1 / 3, 1 / 3]
  · subst hs
    have hmix : IsMixedStrategy ![1, 0, 0] :=
      isMixedStrategy_fin3 zero_le_one le_rfl le_rfl (by norm_num)
    have hne : (![1, 0, 0] : Fin 3 → ℝ) ≠ ![1 / 3, 1 / 3, 1 / 3] := fun heq => by
      have h0 := congrFun heq 0
      norm_num at h0
    have h0 := hlt ![1, 0, 0] hmix hne
    have hzero : rps.payoff₁ ![1, 0, 0] ![1 / 3, 1 / 3, 1 / 3] = 0 := by
      linarith [rps_payoff₁_skew ![1, 0, 0] ![1 / 3, 1 / 3, 1 / 3],
        rps_payoff₁_uniform_left ![1, 0, 0]]
    linarith
  · have hmix := isMixedStrategy_fin3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1)
    have h0 := hlt ![1 / 3, 1 / 3, 1 / 3] hmix (Ne.symm hs)
    linarith [rps_payoff₁_uniform_left s]

/-! ### Model boundaries -/

/-- An asymmetric bimatrix game (`G.B ≠ G.Aᵀ`): `![1, 0]` satisfies `IsESS` (which reads only
`G.A`), yet `(![1, 0], ![1, 0])` is not a Nash equilibrium (`hG : G.B = G.Aᵀ` is needed in
`isESS_iff_isNash_and_forall_lt`). -/
def asymGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![2, 0; 0, 2], !![0, 1; 0, 0]⟩

theorem asymGame_isESS_zero : asymGame.IsESS ![1, 0] := by
  rw [isESS_fin_two_iff]
  refine ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num), Or.inl ⟨rfl, Or.inl ?_⟩⟩
  norm_num [asymGame]

theorem asymGame_not_isNash_zero : ¬ asymGame.IsNash ![1, 0] ![1, 0] := by
  intro h
  have hbr := (isBestResponse₂_iff.1 (isNash_iff.1 h).2).2 0 (by norm_num)
  have h1 := (isPureBestResponse₂_iff.1 hbr) 1
  norm_num [asymGame, vecMul, dotProduct, Fin.sum_univ_two] at h1

/-- On an empty strategy set, no strategy is evolutionarily stable. -/
theorem not_isESS_empty (G : BimatrixGame Empty Empty) (s : Empty → ℝ) : ¬ G.IsESS s :=
  fun h => Empty.elim h.isMixedStrategy.exists_pos.choose

/-- On a singleton strategy set, the unique mixed strategy is evolutionarily stable. -/
theorem isESS_fin_one (G : BimatrixGame (Fin 1) (Fin 1)) : G.IsESS (fun _ => 1) := by
  rw [isESS_iff_forall_lt_or]
  refine ⟨isMixedStrategy_iff.2 ⟨fun _ => zero_le_one, by simp⟩, fun t ht hne => ?_⟩
  exfalso
  apply hne
  ext i
  fin_cases i
  simpa using ht.sum_eq_one

end CslibFrontierTests.GameTheory.Evolutionary
