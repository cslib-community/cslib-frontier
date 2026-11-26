/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.MachineLearning.OnlineLearning.ConstantSum
import CslibFrontier.MachineLearning.OnlineLearning.InternalRegret
import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Worked examples and boundary tests for internal regret, swap regret, and constant-sum games

Ordinary-module client tests for `InternalRegret` and `ConstantSum` (compiled without seeing
unexposed definition bodies):

* `InternalRegret`:
  - boundary witness showing why `id ∈ internalRules` is required when every strict switch has
    negative regret;
  - composition of `modRegret_univ_le_iff` with `blumMansour_swap_regret_le_sqrt`;
  - Exercise 4.1 (`N = 4` tightness witness achieving internal regret `1` and swap regret `3`);
  - Exercise 4.2 (`N = 3` zero-external-regret / large-swap-regret separation and unbounded real
    ratio `swap / external > 100`);
  - Exercise 4.8 (`hedgeFactor` and `mwFactor` cumulative weight bounds, a `Fin 3` variance-penalty
    boundary witness showing `prob (mwFactor (1 / 2))` increases weight on a mixed-dominated action
    when `η > 2 ε` so `mwFactor` requires pure dominance, and the `Fin 3` external-regret
    counterexample putting `1 / 2` average weight on an `ε`-dominated action).
* `ConstantSum`:
  - asymmetric `Fin 2 × Fin 3` `[0, 1]` constant-sum game (`c = 1`, `v₁ = 1 / 3`, `v₂ = 2 / 3`)
    exercising `isMinimaxValue_swap_of_add_eq`, `ciSup_ciInf_eq_ciInf_ciSup`,
    `isMinimaxValue_ciInf_ciSup`, `average_loss_le_of_isMinimaxValue`,
    `constantSum_col_average_loss_le`, and `constantSum_average_loss_mem_Icc` with
    `mw_regret_le_sqrt_of_mem_Icc`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.InternalRegret

open Finset Function Real Convexity Cslib.Probability Cslib.MachineLearning.OnlineLearning.Experts
open scoped BigOperators

/-! ### Modification-rule regret (`modRegret`) and bridges -/

/-- Boundary witness for `id ∈ internalRules`: over `T = 2` rounds on `Fin 2`, playing `(1, 0)` on
`(0, 1)` and `(0, 1)` on `(1, 0)` gives every strict switch `0 → 1` and `1 → 0` regret `-1 < 0`,
while `id ∈ internalRules (Fin 2)` keeps internal regret equal to `0` so Exercise 4.1
(`0 ≤ 2 * 0`) remains valid. -/
example :
    let p : ℕ → Fin 2 → ℝ := fun t => if t = 0 then ![1, 0] else ![0, 1]
    let ℓ : ℕ → Fin 2 → ℝ := fun t => if t = 0 then ![0, 1] else ![1, 0]
    (∑ t ∈ range 2, p t 0 * (ℓ t 0 - ℓ t 1) = -1) ∧
      (∑ t ∈ range 2, p t 1 * (ℓ t 1 - ℓ t 0) = -1) ∧
      modRegret (internalRules (Fin 2)) p ℓ 2 = 0 ∧
      modRegret Set.univ p ℓ 2 = 0 := by
  intro p ℓ
  have h01 : ∑ t ∈ range 2, p t 0 * (ℓ t 0 - ℓ t 1) = -1 := by
    norm_num [p, ℓ, sum_range_succ]
  have h10 : ∑ t ∈ range 2, p t 1 * (ℓ t 1 - ℓ t 0) = -1 := by
    norm_num [p, ℓ, sum_range_succ]
  have hint : modRegret (internalRules (Fin 2)) p ℓ 2 = 0 := by
    apply le_antisymm
    · rw [modRegret_internalRules_le_iff]
      intro a b
      fin_cases a <;> fin_cases b <;> norm_num [p, ℓ, sum_range_succ]
    · exact modRegret_nonneg_of_id_mem
        (mem_internalRules.mpr ⟨0, 0, (update_eq_self 0 id).symm⟩) p ℓ 2
  have hswap : modRegret Set.univ p ℓ 2 = 0 := by
    apply le_antisymm
    · exact (modRegret_univ_le_card_mul_internalRules p ℓ 2).trans_eq (by rw [hint, mul_zero])
    · exact modRegret_nonneg_of_id_mem (Set.mem_univ id) p ℓ 2
  exact ⟨h01, h10, hint, hswap⟩

/-- Bridge check: `modRegret_univ_le_iff` composes directly with `blumMansour_swap_regret_le_sqrt`
from `SwapRegret.lean` on `Fin 3`, `T = 16`. -/
example (ℓ : ℕ → Fin 3 → ℝ) (hℓ : ∀ s < 16, ∀ i, |ℓ s i| ≤ 1) :
    modRegret Set.univ (blumMansourProb √(3 * log 3 / 16) ℓ) ℓ 16 ≤
      2 * √(16 * (3 * log 3)) := by
  have hT : (Fintype.card (Fin 3) : ℝ) * log (Fintype.card (Fin 3)) ≤ (16 : ℕ) := by
    rw [Fintype.card_fin]
    have hlog3 : log (3 : ℝ) ≤ 3 - 1 := log_le_sub_one_of_pos (by norm_num)
    norm_num at hlog3 ⊢
    linarith
  rw [modRegret_univ_le_iff]
  intro δ
  have h := blumMansour_swap_regret_le_sqrt (ι := Fin 3) (T := 16) (by decide) hT hℓ δ
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

/-! ### Exercise 4.1 (`N = 4` tightness) and Exercise 4.2 (`N = 3` unbounded ratio) -/

/-- Exercise 4.1 tightness at `N = 4`: internal regret `1`, swap regret `3`, and `3 ≤ 4 * 1`. -/
example :
    ∃ (p ℓ : ℕ → Fin 4 → ℝ),
      (∀ t < 4, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      (∀ t < 4, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      modRegret (internalRules (Fin 4)) p ℓ 4 = 1 ∧
      modRegret Set.univ p ℓ 4 = 3 ∧
      modRegret Set.univ p ℓ 4 ≤ 4 * modRegret (internalRules (Fin 4)) p ℓ 4 := by
  obtain ⟨p, ℓ, hp, hℓ, hint, hswap⟩ :=
    exists_modRegret_univ_eq_sub_one (N := 4) (by decide)
  refine ⟨p, ℓ, hp, hℓ, hint, by norm_num at hswap; exact hswap, ?_⟩
  have hle := modRegret_univ_le_card_mul_internalRules p ℓ 4
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using hle

/-- Exercise 4.2 on `Fin 3`: zero external regret with swap regret `30`, and positive external
regret with real ratio `swap / external > 100`. -/
example :
    (∃ p ℓ : ℕ → Fin 3 → ℝ,
      (∀ t < 60, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t < 60, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      modRegret (Set.range (Function.const (Fin 3))) p ℓ 60 = 0 ∧
      modRegret Set.univ p ℓ 60 = 30) ∧
    (∃ (T : ℕ) (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t < T, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      0 < modRegret (Set.range (Function.const (Fin 3))) p ℓ T ∧
      100 < modRegret Set.univ p ℓ T /
        modRegret (Set.range (Function.const (Fin 3))) p ℓ T) := by
  refine ⟨?_, exists_unbounded_modRegret_univ_div_const 100⟩
  obtain ⟨p, ℓ, hp, hℓ, hext, hswap⟩ := exists_modRegret_const_zero_and_univ_eq 10
  exact ⟨p, ℓ, hp, hℓ, hext, by norm_num at hswap; exact hswap⟩

/-! ### Exercise 4.8: Dominated-action weight decay and boundaries -/

/-- Hedge cumulative weight bound on an action `(1 / 4)`-dominated by the mixed strategy
`![1 / 2, 1 / 2, 0]` on `Fin 3`, over any horizon `T : ℕ`. -/
example (T : ℕ) :
    let ℓ : ℕ → Fin 3 → ℝ := fun t =>
      if t % 2 = 0 then ![0, 1, 3 / 4] else ![1, 0, 3 / 4]
    ∑ t ∈ range T, prob (hedgeFactor 1) ℓ t 2 ≤ 1 / (1 - exp (-(1 / 4 : ℝ))) := by
  intro ℓ
  have h := sum_prob_hedgeFactor_le_of_dominated (η := 1) (ε := 1 / 4) (y := ![1 / 2, 1 / 2, 0])
    (j := (2 : Fin 3)) (ℓ := ℓ) (T := T) zero_lt_one (by norm_num)
    (fun i => by fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_three])
    (fun s _ => by
      dsimp only [ℓ]
      by_cases he : s % 2 = 0 <;> norm_num [he, Fin.sum_univ_three])
  simpa only [one_mul] using h

/-- Polynomial Weights (`mwFactor (1 / 2)`) cumulative weight bound on a pure `(1 / 2)`-dominated
action over `T = 100` rounds (total weight `≤ 4`, average `≤ 1 / 25`) and at `T = 0`. -/
example :
    let ℓ : ℕ → Bool → ℝ := fun _ b => if b then 3 / 4 else 1 / 4
    (∑ t ∈ range 100, prob (mwFactor (1 / 2)) ℓ t true ≤ 4) ∧
      (∑ t ∈ range 0, prob (mwFactor (1 / 2)) ℓ t true ≤ 4) := by
  intro ℓ
  have hpos : ∀ T, ∀ s < T, ∀ b, 0 < mwFactor (1 / 2) (ℓ s b) := fun _ _ _ b => by
    rw [mwFactor_apply]
    cases b <;> norm_num [ℓ]
  have h100 := sum_prob_mwFactor_le_of_dominated (η := 1 / 2) (ε := 1 / 2) (j := true) (k := false)
    (ℓ := ℓ) (T := 100) (by norm_num) (by norm_num) (hpos 100)
    (fun _ _ => by norm_num [ℓ]) (fun _ _ => by norm_num [ℓ])
  have h0 := sum_prob_mwFactor_le_of_dominated (η := 1 / 2) (ε := 1 / 2) (j := true) (k := false)
    (ℓ := ℓ) (T := 0) (by norm_num) (by norm_num) (hpos 0)
    (fun _ _ => by norm_num [ℓ]) (fun _ _ => by norm_num [ℓ])
  exact ⟨by norm_num at h100; exact h100, by linarith [h0]⟩

/-- Boundary witness for `sum_prob_mwFactor_le_of_dominated`: when action `2` is only `ε`-dominated
by a *mixed* strategy (`y = ![1 / 2, 1 / 2, 0]`, `ε = 1 / 20`, `η = 1 / 2`), Polynomial Weights'
quadratic variance penalty makes action `2`'s probability strictly *increase* above `1 / 3` (and
exceed both non-dominated actions `0` and `1`) after `2` rounds, showing pure dominance is
essential at fixed `η`. -/
example :
    let ℓ : ℕ → Fin 3 → ℝ := fun t =>
      if t % 2 = 0 then ![0, 1, 11 / 20] else ![1, 0, 11 / 20]
    let y : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]
    (∀ s < 2, ∑ i, y i * ℓ s i + 1 / 20 ≤ ℓ s 2) ∧
      prob (mwFactor (1 / 2)) ℓ 0 2 < prob (mwFactor (1 / 2)) ℓ 2 2 ∧
      prob (mwFactor (1 / 2)) ℓ 2 0 < prob (mwFactor (1 / 2)) ℓ 2 2 := by
  intro ℓ y
  refine ⟨fun s _ => by by_cases he : s % 2 = 0 <;> norm_num [ℓ, y, he, Fin.sum_univ_three], ?_, ?_⟩
  · norm_num [prob, potential, weight, mwFactor_apply, ℓ, prod_range_succ, Fin.sum_univ_three]
  · norm_num [prob, potential, weight, mwFactor_apply, ℓ, prod_range_succ, Fin.sum_univ_three]

/-- Exercise 4.8 counterexample at `ε = 1 / 4`, `m = 50` (`T = 100`): nonpositive external regret
while placing cumulative weight `50` (average weight `1 / 2`) on `(1 / 4)`-dominated action `2`. -/
example :
    ∃ p ℓ : ℕ → Fin 3 → ℝ,
      (∀ t, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, ℓ t 0 + 1 / 4 ≤ ℓ t 2) ∧
      modRegret (Set.range (Function.const (Fin 3))) p ℓ 100 ≤ 0 ∧
      ∑ t ∈ range 100, p t 2 = 50 := by
  simpa only [Nat.cast_ofNat] using
    exists_nonpos_external_regret_dominated_weight (ε := 1 / 4) (by norm_num) (by norm_num) 50

/-! ### Theorem 4.9 and §4.4.2 on a non-square `Fin 2 × Fin 3` constant-sum game -/

/-- Asymmetric `2 × 3` `[0, 1]` matrix `asymGame` with minimax value `1 / 3`:
row `0` is `(0, 1, 1 / 3)` and row `1` is `(1 / 2, 0, 1 / 3)`. -/
private noncomputable def asymGame (i : Fin 2) (j : Fin 3) : ℝ :=
  if i = 0 then ![0, 1, 1 / 3] j else ![1 / 2, 0, 1 / 3] j

private lemma asymGame_mem_Icc (i : Fin 2) (j : Fin 3) : asymGame i j ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [asymGame]

private lemma isMinimaxValue_asymGame : IsMinimaxValue asymGame (1 / 3) := by
  let p_opt : StdSimplex ℝ (Fin 2) :=
    { weights := Finsupp.equivFunOnFinite.symm ![1 / 3, 2 / 3]
      nonneg := fun i => by fin_cases i <;> simp [Finsupp.equivFunOnFinite] <;> norm_num
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp [Fin.sum_univ_two, Finsupp.equivFunOnFinite]
        norm_num }
  let q_opt : StdSimplex ℝ (Fin 3) := StdSimplex.single 2
  refine ⟨⟨p_opt, fun j => ?_⟩, q_opt, fun i => ?_⟩
  · fin_cases j <;> simp [p_opt, asymGame, Fin.sum_univ_two, Finsupp.equivFunOnFinite] <;> norm_num
  · fin_cases i <;> simp [q_opt, asymGame, Fin.sum_univ_three, StdSimplex.single]

/-- Non-square `Fin 2 × Fin 3` check of `isMinimaxValue_swap_of_add_eq`,
`ciSup_ciInf_eq_ciInf_ciSup`, and `isMinimaxValue_ciInf_ciSup`: `v_min^1 = v_max^1 = 1 / 3`, and
for `s₂ = 1 - asymGame` (`c = 1`), `Function.swap s₂ : Fin 3 → Fin 2 → ℝ` has value `2 / 3`. -/
example :
    IsMinimaxValue (swap fun i j => 1 - asymGame i j) (2 / 3) ∧
      (⨆ q : StdSimplex ℝ (Fin 3), ⨅ i : Fin 2, ∑ j, q.weights j * asymGame i j) = 1 / 3 ∧
      (⨅ p : StdSimplex ℝ (Fin 2), ⨆ j : Fin 3, ∑ i, p.weights i * asymGame i j) = 1 / 3 := by
  have hswap := isMinimaxValue_swap_of_add_eq (s₁ := asymGame) (s₂ := fun i j => 1 - asymGame i j)
    (c := 1) (fun i j => by ring) isMinimaxValue_asymGame
  have hv_eq : (⨅ p : StdSimplex ℝ (Fin 2), ⨆ j : Fin 3, ∑ i, p.weights i * asymGame i j) = 1 / 3 :=
    (isMinimaxValue_ciInf_ciSup asymGame).unique isMinimaxValue_asymGame
  refine ⟨by norm_num at hswap; exact hswap, ?_, hv_eq⟩
  rw [ciSup_ciInf_eq_ciInf_ciSup, hv_eq]

/-- Theorem 4.9 (`average_loss_le_of_isMinimaxValue`, `constantSum_col_average_loss_le`, and
`constantSum_average_loss_mem_Icc`) instantiated with `mw_regret_le_sqrt_of_mem_Icc` on the
non-square `Fin 2 × Fin 3` constant-sum game `(asymGame, 1 - asymGame)` over `T = 16` rounds. -/
example (q : ℕ → Fin 3 → ℝ) (hq0 : ∀ t < 16, ∀ j, 0 ≤ q t j) (hq1 : ∀ t < 16, ∑ j, q t j = 1) :
    let ℓ₁ : ℕ → Fin 2 → ℝ := fun t i => ∑ j, q t j * asymGame i j
    let p : ℕ → Fin 2 → ℝ := prob (mwFactor (min √(log 2 / 16) (1 / 2))) ℓ₁
    (∑ t ∈ range 16, ∑ i, p t i * ∑ j, q t j * asymGame i j) / (16 : ℕ) ≤
      1 / 3 + 2 * √(16 * log 2) / 16 := by
  intro ℓ₁ p
  have hℓ₁_Icc : ∀ s < 16, ∀ i, ℓ₁ s i ∈ Set.Icc (0 : ℝ) 1 := fun s hs i => by
    dsimp only [ℓ₁]
    refine ⟨sum_nonneg fun j _ => mul_nonneg (hq0 s hs j) (asymGame_mem_Icc i j).1, ?_⟩
    calc ∑ j, q s j * asymGame i j ≤ ∑ j, q s j * 1 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (asymGame_mem_Icc i j).2 (hq0 s hs j)
      _ = 1 := by simp only [mul_one, hq1 s hs]
  have hreg : ∀ i : Fin 2, ∑ t ∈ range 16, ∑ i', p t i' * ∑ j, q t j * asymGame i' j ≤
      (∑ t ∈ range 16, ∑ j, q t j * asymGame i j) + 2 * √((16 : ℕ) * log (Fintype.card (Fin 2))) :=
    fun i => mw_regret_le_sqrt_of_mem_Icc hℓ₁_Icc i
  have h := average_loss_le_of_isMinimaxValue isMinimaxValue_asymGame (T := 16) (by decide)
    hq0 hq1 (fun i => by simpa only [Fintype.card_fin, Nat.cast_ofNat, p, ℓ₁] using hreg i)
  simpa only [Nat.cast_ofNat] using h

end CslibFrontierTests.InternalRegret
