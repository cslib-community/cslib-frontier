/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.MachineLearning.OnlineLearning.Bandit
import CslibFrontier.MachineLearning.OnlineLearning.ConstantSum
import CslibFrontier.MachineLearning.OnlineLearning.FPL
import CslibFrontier.MachineLearning.OnlineLearning.Greedy
import CslibFrontier.MachineLearning.OnlineLearning.InternalRegret
import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
import CslibFrontier.Probability.BitString.Khintchine
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Worked examples and regression tests for NRTV Chapter 4 online regret

Nonvacuous concrete checks across all seven modules in this PR:

* `Probability.BitString.Khintchine`: exact weighted and unweighted Rademacher `L¹` comparisons.
* `MachineLearning.OnlineLearning.Greedy`: Greedy (Theorem 4.2) tightness and missing-leader
  failure, Randomized Greedy (Theorem 4.4) harmonic calculation, RWM (Theorem 4.5 & Exercise 4.3)
  update/counterexample, payoff MW (Exercise 4.4), and anytime Hedge.
* `MachineLearning.OnlineLearning.InternalRegret`: pushforward shift, Exercise 4.1 tightness witness
  on `Fin 3`, Exercise 4.2 separation, and Exercise 4.6 tuned Polynomial Weights condition.
* `MachineLearning.OnlineLearning.LowerBounds`: Theorems 4.1, 4.3, 4.7, 4.8 and Exercise 4.5 on
  concrete finite action types and horizons.
* `MachineLearning.OnlineLearning.ConstantSum`: shifted matching pennies (`s₁ + s₂ = 5`), value
  duality, no-regret proof of the minimax value `1 / 2`, and non-constant-sum counterexample.
* `MachineLearning.OnlineLearning.FPL`: lexicographic leader step and concrete `2 √(N T)` experts
  bound.
* `MachineLearning.OnlineLearning.Bandit`: cyclic exploration schedule on `Fin 3`, exact
  `mabPlay_apply_explore`/`mabPlay_apply_exploit`, partial-information invariance when changing
  unobserved/exploitation losses, non-divisible horizon `T = 7 = 2 * 3 + 1`, small-horizon `T = 2`
  branch of `optBlockCount`, and concrete Theorem 4.17 RWM / anytime-Hedge / textbook bounds.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.OnlineRegretNRTV

open Finset Real
open Cslib.BitString
open Cslib.MachineLearning.OnlineLearning.Experts
open Cslib.MachineLearning.OnlineLearning.FPL
open Cslib.Probability Convexity
open scoped BigOperators

/-! ### Khintchine `L¹` lower bound -/

/-- Exact weighted Khintchine check on `Bool` with weights `(2, 1)`:
`(2² + 1²) / 3 = 5 / 3 ≤ 4 = (𝔼 |2 * sign(x₀) + sign(x₁)|)²`. -/
example : (∑ i : Bool, (if i then (2 : ℝ) else 1) ^ 2) / 3 ≤
    (𝔼 x : Bool → Bool, |∑ i : Bool, (if i then (2 : ℝ) else 1) * signVal (x i)|) ^ 2 :=
  sum_sq_div_three_le_sq_expect_abs_sum_mul_signVal (fun i : Bool => if i then 2 else 1)

/-- Concrete numerical value: for weights `(2, 1)` on `Bool`, `√(5 / 3) < 2 = 𝔼 |Y|`. -/
example : √((5 : ℝ) / 3) < 2 := by
  have hsq : (5 : ℝ) / 3 < 2 ^ 2 := by norm_num
  calc √((5 : ℝ) / 3) < √(2 ^ 2) := sqrt_lt_sqrt (by norm_num) hsq
    _ = 2 := sqrt_sq (by norm_num)

/-- Unweighted Khintchine lower bound on `Fin 3`: `1 ≤ 𝔼 |∑ i : Fin 3, signVal (x i)|`. -/
example : (1 : ℝ) ≤ 𝔼 x : Fin 3 → Bool, |∑ i : Fin 3, signVal (x i)| := by
  have h := sqrt_card_div_three_le_expect_abs_sum_signVal (ι := Fin 3)
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  have h1 : √((3 : ℝ) / 3) = 1 := by norm_num
  linarith

/-! ### Greedy, Randomized Greedy, RWM, payoff MW, and anytime Hedge -/

/-- Alternating two-expert binary losses `(1, 0), (0, 1), (1, 0), (0, 1), …` forcing `greedyPlay`
to suffer loss `1` in every single round (`L_Greedy^4 = 4 = 2 * L_min^4`). -/
private def altLoss (t : ℕ) (i : Fin 2) : ℝ :=
  if t % 2 = 0 then (if i = 0 then 1 else 0) else (if i = 1 then 1 else 0)

private lemma altLoss_mem_Icc (t : ℕ) (i : Fin 2) : altLoss t i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold altLoss
  split_ifs <;> norm_num

private lemma altLoss_binary (t : ℕ) (i : Fin 2) : altLoss t i = 0 ∨ altLoss t i = 1 := by
  unfold altLoss
  split_ifs <;> simp

/-- `greedyPlay` against `altLoss` over `T = 4` satisfies Theorem 4.2
(`total loss ≤ 2 * L_min + 1`). -/
example : ∑ t ∈ range 4, altLoss t (greedyPlay altLoss t) ≤
    (2 : ℝ) * minCumLoss altLoss 4 + (2 - 1) := by
  have h := greedyPlay_loss_le (ι := Fin 2) (ℓ := altLoss) (T := 4) fun t _ i => altLoss_mem_Icc t i
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

/-- Concrete computation of `minCumLoss altLoss 4 = 2`. -/
example : minCumLoss altLoss 4 = 2 := by
  have h0 : cumLoss altLoss 4 0 = 2 := by
    simp only [cumLoss, sum_range_succ, range_zero, sum_empty, zero_add]
    norm_num [altLoss]
  have h1 : cumLoss altLoss 4 1 = 2 := by
    simp only [cumLoss, sum_range_succ, range_zero, sum_empty, zero_add]
    norm_num [altLoss]
  apply le_antisymm
  · exact (minCumLoss_le altLoss 4 0).trans_eq h0
  · refine le_minCumLoss_iff.mpr fun i => ?_
    fin_cases i
    · exact h0.ge
    · exact h1.ge

/-- Missing-leader hypothesis is necessary for Theorem 4.2: a non-greedy play that always picks
expert `1` against constant losses `(0, 1)` suffers loss `4 > 2 * 0 + (2 - 1) = 1`. -/
example : ¬ (∑ _t ∈ range 4, (fun (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 1 ≤
    (Fintype.card (Fin 2) : ℝ) * minCumLoss (fun _ (i : Fin 2) => if i = 0 then 0 else 1) 4 +
      ((Fintype.card (Fin 2) : ℝ) - 1)) := by
  have hmin : minCumLoss (fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 4 ≤ 0 := by
    have h0 := minCumLoss_le (fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1) 4 0
    simpa [cumLoss] using h0
  simp only [Fintype.card_fin, Nat.cast_ofNat, sum_const, card_range, nsmul_eq_mul]
  norm_num at hmin ⊢
  linarith

/-- Concrete Theorem 4.4 harmonic check on `altLoss` over `T = 2`: `H_2 = 3 / 2`. -/
example : ∑ t ∈ range 2, ∑ i : Fin 2, randGreedyProb altLoss t i * altLoss t i ≤
    ((harmonic 2 : ℝ) - 1) + harmonic 2 * minCumLoss altLoss 2 := by
  simpa only [Fintype.card_fin] using
    randGreedy_loss_le_harmonic (ι := Fin 2) (ℓ := altLoss) (T := 2) fun t _ i =>
      altLoss_binary t i

/-- Concrete `rwmFactor` identity against `mwFactor` on `{0, 1}`, and non-equality at `1 / 2`. -/
example : rwmFactor (1 / 2) 1 = mwFactor (1 / 2) 1 ∧
    rwmFactor (1 / 2) (1 / 2) ≠ mwFactor (1 / 2) (1 / 2) := by
  refine ⟨rwmFactor_eq_mwFactor_of_binary (Or.inr rfl), ?_⟩
  rw [rwmFactor_apply, mwFactor_apply]
  intro h
  have hsq : ((1 - (1 / 2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 = (1 - 1 / 2 * (1 / 2 : ℝ)) ^ 2 :=
    congrArg (· ^ 2) h
  rw [← rpow_natCast, ← rpow_mul (by norm_num)] at hsq
  norm_num at hsq

/-- Tuned RWM on `altLoss` over `T = 4`: `L_RWM ≤ 2 + 2 √(4 ln 2)`. -/
example : ∑ t ∈ range 4, ∑ j : Fin 2,
      prob (rwmFactor (tunedStep (log (Fintype.card (Fin 2))) 4)) altLoss t j * altLoss t j ≤
    minCumLoss altLoss 4 + 2 * √((4 : ℕ) * log (Fintype.card (Fin 2))) :=
  rwm_loss_le_tunedStep (by simp) fun t _ i => altLoss_mem_Icc t i

/-- Exercise 4.4 payoff-maximizing PW on `Bool` with constant gains `(1, -1)` over `T = 4`. -/
example : (4 : ℝ) - (2 * √(4 * log 2) + 2 * log 2) ≤
    ∑ t ∈ range 4, ∑ j : Bool,
      prob (mwPayoffFactor (tunedStep (log 2) 4)) (fun _ i => if i then 1 else -1) t j *
        (if j then (1 : ℝ) else -1) := by
  have h := mw_payoff_ge_sub_sqrt_qmax (ι := Bool) (by simp) (Q_max := 4) (by norm_num)
    (g := fun _ i => if i then (1 : ℝ) else -1) (T := 4)
    (fun _ _ j => by cases j <;> norm_num)
    (k := true) (by norm_num [sum_range_succ])
  simpa only [Fintype.card_bool, Nat.cast_ofNat, ↓reduceIte, sum_const, card_range,
    nsmul_eq_mul, mul_one] using h

/-- Horizon-free `anytimeHedgeProb` regret on `altLoss` at `T = 4`. -/
example : ∑ t ∈ range 4, ∑ j : Fin 2, anytimeHedgeProb altLoss t j * altLoss t j ≤
    cumLoss altLoss 4 0 + 3 * √((4 : ℕ) * log 2) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    anytimeHedge_regret_le (ι := Fin 2) (by simp) (T := 4)
      (fun t _ i => altLoss_mem_Icc t i) 0

/-- Exercise 4.8: RWM (`η = 1 / 2`) places summed weight at most `4` on an `1 / 2`-dominated action
over any horizon `T`. -/
example (T : ℕ) :
    ∑ t ∈ range T,
      prob (rwmFactor (1 / 2)) (fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1 / 2) t 1 ≤ 4 := by
  have h := rwm_sum_prob_le_of_dominated_mixed (ι := Fin 2) (η := 1 / 2) (ε := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ℓ := fun _ (i : Fin 2) => if i = 0 then (0 : ℝ) else 1 / 2) (T := T) (j := 1)
    (y := ![1, 0]) (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    (fun _ _ => by norm_num [Fin.sum_univ_two])
  linarith

/-- Exercise 4.8 separation at `ε = 1 / 2`, `m = 5` (`T = 10` on `Fin 3`): nonpositive external
regret while placing total weight `5` (`1 / 2` average) on the `1 / 2`-dominated action `2`. -/
example : ∃ (p ℓ : ℕ → Fin 3 → ℝ),
    (∀ t, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
    (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t, ℓ t 0 + 1 / 2 ≤ ℓ t 2) ∧
    ∑ t ∈ range 10, ∑ i, p t i * ℓ t i ≤ minCumLoss ℓ 10 ∧
    ∑ t ∈ range 10, p t 2 = 5 := by
  simpa using exists_low_external_regret_dominated_weight (ε := 1 / 2)
    (by norm_num) (by norm_num) 5

/-! ### Internal regret, swap regret, and Exercises 4.1, 4.2, and 4.6 -/

/-- `pushforwardProb` of `(1 / 2, 1 / 4, 1 / 4)` under `switchRule 0 1` moves `1 / 2` to `1`. -/
example : pushforwardProb (switchRule (0 : Fin 3) 1) ![1 / 2, 1 / 4, 1 / 4] 0 = 0 ∧
    pushforwardProb (switchRule (0 : Fin 3) 1) ![1 / 2, 1 / 4, 1 / 4] 1 = 3 / 4 := by
  simp only [pushforwardProb_apply, switchRule_apply, sum_filter, Fin.sum_univ_three]
  norm_num

/-- Exercise 4.1 tightness at `N = 3`: there exist `p, ℓ` over `T = 3` with `internalRegret = 1`
and `swapRegret = 2 = N - 1`. -/
example : ∃ (p ℓ : ℕ → Fin 3 → ℝ),
    (∀ t < 3, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
    (∀ t < 3, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    internalRegret p ℓ 3 = 1 ∧ swapRegret p ℓ 3 = 2 := by
  obtain ⟨p, ℓ, hp, hℓ, hi, hs⟩ :=
    exists_swapRegret_eq_pred_card_mul_internalRegret (N := 3) (by omega)
  exact ⟨p, ℓ, hp, hℓ, hi, by norm_num at hs ⊢; linarith⟩

/-- Exercise 4.2 separation at `m = 2` (`T = 12` on `Fin 3`): zero external regret with swap regret
`6`. -/
example : ∃ (p ℓ : ℕ → Fin 3 → ℝ),
    (∀ t < 12, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
    (∀ t < 12, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    externalRegret p ℓ 12 = 0 ∧ swapRegret p ℓ 12 = 6 := by
  obtain ⟨p, ℓ, hp, hℓ, he, hs⟩ := exists_externalRegret_zero_and_swapRegret_eq 2
  exact ⟨p, ℓ, hp, hℓ, he, by norm_num at hs ⊢; exact hs⟩

/-- Exercise 4.6 Polynomial Weights copies: with `2` actions, `T = 6` already satisfies
`4 * (2 * ln 2) ≤ T`. -/
example (ℓ : ℕ → Bool → ℝ) (hℓ : ∀ s < 6, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    swapRegret (blumMansourPWProb √(2 * log 2 / 6) ℓ) ℓ 6 ≤ 2 * √(6 * (2 * log 2)) := by
  have hlog := log_two_lt_d9
  have h := blumMansourPW_swap_regret_le_sqrt (ι := Bool) (T := 6) (by simp)
    (by simp only [Fintype.card_bool, Nat.cast_ofNat]; linarith) hℓ
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using h

/-! ### Regret lower bounds (Theorems 4.1, 4.3, 4.7, 4.8, and Exercise 4.5) -/

/-- Theorem 4.1 on `randGreedyProb` with `3` actions and `T = 6`: dynamic regret at least `4`. -/
example : ∃ (ℓ : ℕ → Fin 3 → ℝ) (g : ℕ → Fin 3),
    (∀ t < 6, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    (∑ t ∈ range 6, ℓ t (g t) = 0) ∧
    (4 : ℝ) ≤ ∑ t ∈ range 6, ∑ i, randGreedyProb ℓ t i * ℓ t i := by
  obtain ⟨ℓ, g, h01, hg, hlb⟩ :=
    exists_dynamic_regret_ge (ι := Fin 3) (H := randGreedyProb) isOnlineAlg_randGreedy 6
  refine ⟨ℓ, g, h01, hg, ?_⟩
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hlb
  linarith

/-- Theorem 4.3 on `greedyPlay` with `3` actions and `T = 7`: total loss `7` and exact best action
loss `⌊7 / 3⌋ = 2`. -/
example : ∃ ℓ : ℕ → Fin 3 → ℝ,
    (∀ t < 7, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
    (∑ t ∈ range 7, ℓ t (greedyPlay ℓ t) = 7) ∧
    minCumLoss ℓ 7 = 2 := by
  obtain ⟨ℓ, h01, hloss, hmin⟩ := exists_deterministic_loss_eq_and_minCumLoss_eq (ι := Fin 3)
    (D := greedyPlay) (fun {_ _ _} h => greedyPlay_congr h) 7
  refine ⟨ℓ, h01, by simpa using hloss, ?_⟩
  simp only [Fintype.card_fin] at hmin
  norm_num at hmin
  exact hmin

/-- Theorem 4.7 boundary case `N = 8 = 2 ^ 3`, `T = 3`: expected loss `3 / 2` and deterministic
minimum loss `0` for every causal online algorithm. -/
example : ∃ ℓ : (Fin 3 → Bool) → ℕ → Fin 8 → ℝ,
    (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
    (∀ w, minCumLoss (ℓ w) 3 = 0) ∧
    ∀ H : (ℕ → Fin 8 → ℝ) → ℕ → Fin 8 → ℝ, IsOnlineAlg H →
      (𝔼 w, ∑ t ∈ range 3, ∑ i, H (ℓ w) t i * ℓ w t i) = 3 / 2 := by
  obtain ⟨ℓ, h01, hmin, hexp⟩ :=
    exists_stochastic_loss_eq_half_minCumLoss_zero (ι := Fin 8) (T := 3) (by decide)
  exact ⟨ℓ, h01, hmin, fun H hH => by have := hexp H hH; norm_num at this ⊢; exact this⟩

/-- Theorem 4.8 at `N = 2`, `T = 12`: `1 / (2 √3) * √12 = 1` expected regret lower bound. -/
example : ∃ ℓ : (Fin 12 → Bool) → ℕ → Bool → ℝ,
    (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
    ∀ H : (ℕ → Bool → ℝ) → ℕ → Bool → ℝ, IsOnlineAlg H →
      (1 : ℝ) ≤ 𝔼 w, ((∑ t ∈ range 12, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) 12) := by
  obtain ⟨ℓ, h01, hspec⟩ := exists_two_experts_stochastic_regret_ge (ι := Bool) (by simp) 12
  refine ⟨ℓ, h01, fun H hH => ?_⟩
  have hlb := (hspec H hH).2
  have hval : (1 / (2 * √3)) * √((12 : ℕ) : ℝ) = 1 := by
    have h12 : √(12 : ℝ) = 2 * √3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, sqrt_mul (by norm_num),
        sqrt_sq (by norm_num)]
    have h3 : √(3 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
    simp only [Nat.cast_ofNat, h12]
    field_simp
  linarith

/-! ### Constant-sum games and the online-learning minimax theorem -/

private def penniesRow (i j : Bool) : ℝ := if i = j then 1 else 0
private def penniesColShift (i j : Bool) : ℝ := 5 - penniesRow i j

/-- `penniesRow` and `penniesColShift` form a constant-sum game with constant `5`. -/
example : IsConstantSum penniesRow penniesColShift 5 := fun i j => by
  unfold penniesColShift
  ring

/-- Non-constant-sum counterexample: both players lose `penniesRow i j` (sums `0` and `2`). -/
example : ¬ ∃ c, IsConstantSum penniesRow penniesRow c := by
  rintro ⟨c, hc⟩
  have h0 := hc true true
  have h1 := hc true false
  norm_num [penniesRow] at h0 h1
  linarith

/-- By coupled no-regret learning (`isMinimaxValue_minmaxValue_of_noRegret`), matching pennies has
value `1 / 2`, and the constant-`5` column player's value is `9 / 2`. -/
example : minmaxValue penniesRow = 1 / 2 ∧ maxminValue penniesRow = 1 / 2 := by
  have h1 : IsMinimaxValue penniesRow (1 / 2) := by
    let u : StdSimplex ℝ Bool :=
      .duple true false (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    refine ⟨⟨u, fun j => ?_⟩, u, fun i => ?_⟩
    · cases j <;> norm_num [u, penniesRow, StdSimplex.duple, Fintype.sum_bool]
    · cases i <;> norm_num [u, penniesRow, StdSimplex.duple, Fintype.sum_bool]
  have h2 := isMinimaxValue_minmaxValue_of_noRegret penniesRow
  have heq : minmaxValue penniesRow = 1 / 2 := h2.unique h1
  exact ⟨heq, (maxminValue_eq_minmaxValue penniesRow).trans heq⟩

/-! ### Follow the Perturbed Leader (Kalai–Vempala 2005) -/

/-- Lexicographic FPL leader on two experts: when costs tie, prefers `0 : Fin 2`. -/
example : fplLeader (expertVec (ι := Fin 2)) ![3, 3] = 0 := by
  rw [fplLeader_eq_iff]
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · fin_cases b <;> norm_num [fplDot_expertVec]
  · exact absurd hb (Fin.not_lt_zero b)

/-- FPL tuned `2 √(N T)` regret bound on `Fin 2`, `T = 8`: at most `8`. -/
example : ∑ t ∈ range 8, ∑ a : Fin 2,
      fplExpertsProb √(1 / (2 * 8)) altLoss t a * altLoss t a ≤
    cumLoss altLoss 8 0 + 8 := by
  have h := fpl_experts_regret_le_sqrt (ι := Fin 2) (ℓ := altLoss) (T := 8) (by omega)
    (fun t _ i => altLoss_mem_Icc t i) 0
  have hsqrt : (2 : ℝ) * √(2 * 8) = 8 := by
    rw [show (2 : ℝ) * 8 = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    norm_num
  simpa only [Fintype.card_fin, Nat.cast_ofNat, hsqrt] using h

/-! ### Partial-information (bandit) block-exploration reduction (Theorem 4.17) -/

/-- Canonical embedding of `Fin 2` into `Fin 3`. -/
private def emb23 : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)

/-- Cyclic-shift exploration schedule for `Fin 2` inside blocks of length `m = 3`. -/
private def sched23 : ExplorationSchedule (Fin 2) 3 (Fin 3) :=
  cyclicExplorationSchedule (by omega : 0 < 3) emb23

/-- Concrete block average over `m = 3`: for `altLoss`, block `0` has rounds `(1,0), (0,1), (1,0)`
giving `(2/3, 1/3)`. -/
example : blockAvgLoss 3 altLoss 0 0 = 2 / 3 ∧ blockAvgLoss 3 altLoss 0 1 = 1 / 3 := by
  simp only [blockAvgLoss_apply, Fin.sum_univ_three]
  norm_num [altLoss]

/-- At shift `ω 0 = 1`, in block `0` action `0` explores at offset `0 + 1 = 1`, action `1`
explores at offset `1 + 1 = 2`, and offset `0` is an exploitation round playing `H`. -/
example (H : (ℕ → Fin 2 → ℝ) → ℕ → Fin 2 → ℝ) :
    let ω : Fin 2 → Fin 3 := ![1, 0]
    mabPlay (by omega : 0 < 3) sched23 H ω altLoss 1 0 = 1 ∧
    mabPlay (by omega : 0 < 3) sched23 H ω altLoss 2 1 = 1 ∧
    mabPlay (by omega : 0 < 3) sched23 H ω altLoss 0 0 =
      H (exploredLoss sched23 ω altLoss) 0 0 := by
  intro ω
  refine ⟨?_, ?_, ?_⟩
  · have h := mabPlay_apply_explore (by omega : 0 < 3) sched23 H ω altLoss 0 0 0
    have h0 : (sched23.time (ω 0) 0).val = 1 := by
      simp only [sched23, cyclicExplorationSchedule_time, emb23, ω]
      decide
    simpa [h0] using h
  · have h := mabPlay_apply_explore (by omega : 0 < 3) sched23 H ω altLoss 0 1 1
    have h1 : (sched23.time (ω 0) 1).val = 2 := by
      simp only [sched23, cyclicExplorationSchedule_time, emb23, ω]
      decide
    simpa [h1] using h
  · have h := mabPlay_apply_exploit (by omega : 0 < 3) sched23 H ω altLoss 0
      (r := (0 : Fin 3)) (fun i => by
        simp only [sched23, cyclicExplorationSchedule_time, emb23, ω]
        fin_cases i <;> decide) 0
    simpa using h

/-- **Partial-information invariance test**: altering `altLoss` on round `0` (exploitation) AND on
the unplayed arm of round `1` (`i = 1`) and round `2` (`i = 0`) leaves `mabPlay` completely
unchanged in block `1` (round `3`). -/
example :
    let ω : Fin 2 → Fin 3 := ![0, 0]
    let ℓ' : ℕ → Fin 2 → ℝ := fun t i =>
      if t = 0 ∧ i = 0 then altLoss 0 0
      else if t = 1 ∧ i = 1 then altLoss 1 1
      else 1 - altLoss t i
    mabPlay (by omega : 0 < 3) sched23 anytimeHedgeProb ω altLoss 3 =
      mabPlay (by omega : 0 < 3) sched23 anytimeHedgeProb ω ℓ' 3 := by
  intro ω ℓ'
  refine mabPlay_bandit_congr (by omega : 0 < 3) sched23 isOnlineAlg_anytimeHedge ω fun σ hσ i => ?_
  fin_cases σ
  · fin_cases i
    · have h0 : (sched23.time (ω 0) 0).val = 0 := by
        simp only [sched23, cyclicExplorationSchedule_time, emb23, ω]; decide
      simp [h0, ℓ']
    · have h1 : (sched23.time (ω 0) 1).val = 1 := by
        simp only [sched23, cyclicExplorationSchedule_time, emb23, ω]; decide
      simp [h1, ℓ']
  · simp at hσ

/-- Non-divisible horizon `T = 7 = 2 * 3 + 1` with `sched23` and `anytimeHedgeProb`. -/
example : (𝔼 ω : Fin 2 → Fin 3,
      ∑ t ∈ range 7, ∑ j, mabPlay (by omega : 0 < 3) sched23 anytimeHedgeProb ω altLoss t j *
        altLoss t j) ≤
    minCumLoss altLoss 7 + 2 * 2 + 1 + 3 * (3 * √(2 * log 2)) := by
  have h := mabPlay_expected_loss_le (ι := Fin 2) (m := 3) (K := 2) (T := 7)
    (by omega) (by omega) sched23 isOnlineAlg_anytimeHedge
    (ℓ := altLoss) (fun t _ i => altLoss_mem_Icc t i)
    (R := 3 * √((2 : ℕ) * log (Fintype.card (Fin 2))))
    (fun c hc k => anytimeHedge_regret_le (by simp) hc k)
  simpa only [Fintype.card_fin, Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub, Nat.cast_one] using h

/-- Small-horizon regime (`T = 2 < 4 ln 2 ≈ 2.77`): `optBlockCount 2 2 = 0`, and
`mabRWM_uniformInj_expected_loss_le` holds cleanly with the uniform fallback. -/
example : optBlockCount 2 2 = 0 := by
  have hlog := log_two_gt_d9
  refine optBlockCount_eq_zero_of_lt ?_
  push_cast
  linarith

/-- Concrete instantiation of `mabRWM_uniformInj_expected_loss_le` on `Fin 2`, `T = 27`. -/
example :
    (𝔼 ω : Fin (optBlockCount (Fintype.card (Fin 2)) 27) →
        (Fin 2 ↪ Fin (optBlockLen (Fintype.card (Fin 2)) 27)),
        ∑ t ∈ range 27, ∑ j,
          mabPlay (optBlockLen_pos (by simp : 2 ≤ Fintype.card (Fin 2)))
            (uniformInjExplorationSchedule (ι := Fin 2)
              (optBlockLen_pos (by simp : 2 ≤ Fintype.card (Fin 2)))
              (le_optBlockLen (by simp : 2 ≤ Fintype.card (Fin 2))))
            (prob (rwmFactor (tunedStep (log (Fintype.card (Fin 2)))
              (optBlockCount (Fintype.card (Fin 2)) 27))))
            ω altLoss t j * altLoss t j) ≤
      minCumLoss altLoss 27 + (9 / 2) * (27 : ℝ) ^ ((2 : ℝ) / 3) * (2 * log 2) ^ ((1 : ℝ) / 3) := by
  have h := mabRWM_uniformInj_expected_loss_le (ι := Fin 2) (by simp) 27
    (fun t _ i => altLoss_mem_Icc t i)
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

end CslibFrontierTests.OnlineRegretNRTV
