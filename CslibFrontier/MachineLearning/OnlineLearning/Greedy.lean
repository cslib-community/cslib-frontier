/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.Defs
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic
import CslibFrontier.Foundations.NumberTheory.Harmonic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Greedy, randomized greedy, randomized weighted majority, and horizon-free experts

This module formalizes the external-regret algorithms and exercises of [BlumMansour2007AGT, §4.3.1,
§4.3.2, and Exercises 4.3, 4.4, and 4.8] in the experts setting (`OnlineLearning.Experts`),
together with a horizon-free decreasing-step-size Hedge learner.

## Overview and source mapping

* **Cumulative losses and current leaders** (`cumLoss`, `minCumLoss`, `leaders`):
  `cumLoss ℓ t i = ∑ s < t, ℓ s i` is the total loss of action `i` before round `t`,
  `minCumLoss ℓ t` is the minimum cumulative loss across actions, and `leaders ℓ t` is the nonempty
  `Finset` of actions attaining `minCumLoss ℓ t` (`S^{t-1}` in [BlumMansour2007AGT, §4.3.1]).
* **Deterministic Greedy / Follow-the-Leader** (`greedyPlay`, `greedy_loss_le`,
  `greedyPlay_loss_le` — [BlumMansour2007AGT, §4.3.1, Theorem 4.2, p. 83]):
  Any sequence `x` choosing `x t ∈ leaders ℓ t` (in particular `greedyPlay`, which breaks ties by a
  linear order on `ι`) satisfies `∑ t < T, ℓ t (x t) ≤ N * minCumLoss ℓ T + (N - 1)` for all
  `[0, 1]`-valued loss sequences (hence in particular for `{0, 1}` losses), proved via the bounded
  window potential `∑ i, max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)`.
* **Randomized Greedy** (`randGreedyProb`, `randGreedy_loss_le_harmonic`, `randGreedy_loss_le_log`
  — [BlumMansour2007AGT, §4.3.1, Theorem 4.4, p. 84]):
  `randGreedyProb ℓ t` plays the uniform distribution on `leaders ℓ t`. On `{0, 1}` loss sequences,
  the harmonic potential `(harmonic N - harmonic |leaders ℓ t|) + harmonic N * minCumLoss ℓ t`
  gives the sharp harmonic bound `L_RG ≤ (H_N - 1) + H_N * L_min` (`randGreedy_loss_le_harmonic`)
  and hence `L_RG ≤ ln N + (1 + ln N) * L_min` (`randGreedy_loss_le_log`). Note: unlike Theorem 4.2,
  exact-tie `randGreedyProb` requires `{0, 1}` losses; infinitesimally perturbed `[0, 1]` losses
  can keep `|leaders ℓ t| = 1` in every round and force deterministic-greedy loss `N * L_min`.
* **Randomized Weighted Majority** (`rwmFactor`, `rwm_loss_le`, `rwm_loss_le_tunedStep`,
  `rwm_loss_le_sqrt_minCumLoss`, `exists_rwm_gt_pw_sq_bound` — [BlumMansour2007AGT, §4.3.2,
  Theorem 4.5, pp. 85–86, and Exercise 4.3, p. 101]):
  `rwmFactor η x = (1 - η) ^ x` updates weights by `(1 - η) ^ (ℓ t i)`. For `[0, 1]` losses and
  `0 < η ≤ 1 / 2`, convexity of `x ↦ (1 - η) ^ x` gives `(1 - η) ^ x ≤ 1 - η x` and yields
  `L_RWM ≤ (1 + η) * L_k + ln N / η` (`rwm_loss_le`), extending Theorem 4.5 to `[0, 1]` losses and
  giving the `2 √(T ln N)` bound of Theorem 4.6 for every `T` via `η = min(√(ln N / T), 1 / 2)`
  (`rwm_loss_le_tunedStep`), as well as the first-order `L_min + 2 √(L_min ln N) + 2 ln N` bound
  when `η = min(√(ln N / L_min), 1 / 2)` (`rwm_loss_le_sqrt_minCumLoss`; note that the `+ 2 ln N`
  term omitted in the parenthetical remark of [BlumMansour2007AGT, p. 85] is needed when
  `L_min = 0`). Regarding Exercise 4.3 (p. 101), while `rwmFactor` achieves Theorem 4.6's
  `2 √(T ln N)` regret bound on `[0, 1]` losses, it does *not* satisfy Theorem 4.6's
  comparator-second-order display `L ≤ L_k + η Q_k + ln N / η` (`exists_rwm_gt_pw_sq_bound`,
  cf. [CesaBianchiMansourStoltz2007]).
* **Payoff maximization in `[-1, +1]`** (`mwPayoffFactor`, `mw_payoff_ge_sub_sq`,
  `mw_payoff_ge_sub_sqrt_qmax` — [BlumMansour2007AGT, Exercise 4.4, p. 101]):
  Running multiplicative weights on negated payoffs (`mwPayoffFactor η x = 1 + η x`) achieves
  expected total payoff at least `∑ t < T, g t k - 2 √(Q_max ln N) - 2 ln N` whenever
  `∑ t < T, g t k ^ 2 ≤ Q_max`.
* **Horizon-free anytime Hedge** (`anytimeHedgeProb`, `anytimeHedge_regret_le` — addressing the
  unknown-horizon note of [BlumMansour2007AGT, pp. 85, 87]):
  Time-varying step sizes `η_t = √(ln N / (t + 1))` achieve external regret at most `3 √(T ln N)`
  simultaneously for every horizon `T` on `[0, 1]` losses without prior knowledge of `T`.
* **Weight on `ε`-dominated actions** (`rwm_prob_le_of_dominated_mixed`,
  `rwm_sum_prob_le_of_dominated_mixed`, `mw_prob_le_of_dominated`, `mw_sum_prob_le_of_dominated`,
  `exists_low_external_regret_dominated_weight` — [BlumMansour2007AGT, Exercise 4.8,
  p. 101]):
  Both RWM (`rwmFactor`) and Polynomial Weights (`mwFactor`) assign exponentially decaying weight
  at most `(1 - η ε)^t` to any `ε`-dominated action (giving total summed weight at most `1 / (η ε)`
  over *any* horizon `T`, and `rwmFactor` directly covers *mixed-strategy* `ε`-domination). In
  contrast, on `Fin 3` over `T = 2 m` rounds there are `[0, 1]` losses where action `2` is
  `ε`-dominated by action `0` in every round (`ε ∈ (0, 1 / 2]`), yet a deterministic play sequence
  has nonpositive external regret (`≤ minCumLoss ℓ (2 m)`) while placing time-average weight `1 / 2`
  on action `2`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.cumLoss`,
  `Cslib.MachineLearning.OnlineLearning.Experts.minCumLoss`,
  `Cslib.MachineLearning.OnlineLearning.Experts.leaders`: cumulative losses, best cumulative loss,
  and the set of current minimum-loss leaders.
* `Cslib.MachineLearning.OnlineLearning.Experts.greedyPlay`: deterministic Greedy (FTL) action
  selection breaking ties by a linear order.
* `Cslib.MachineLearning.OnlineLearning.Experts.randGreedyProb`: Randomized Greedy uniform leader
  distribution.
* `Cslib.MachineLearning.OnlineLearning.Experts.rwmFactor`,
  `Cslib.MachineLearning.OnlineLearning.Experts.tunedStep`: RWM update factor `(1 - η) ^ x` and
  capped step size `min (1 / 2) √(L / Q)`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mwPayoffFactor`: payoff-maximizing PW factor
  `1 + η x`.
* `Cslib.MachineLearning.OnlineLearning.Experts.anytimeHedgeProb`: horizon-free Hedge distribution
  with step size `√(ln N / (t + 1))`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.greedy_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.greedyPlay_loss_le`: [BlumMansour2007AGT,
  Theorem 4.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_harmonic`,
  `Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_log`: [BlumMansour2007AGT,
  Theorem 4.4].
* `Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le_tunedStep`,
  `Cslib.MachineLearning.OnlineLearning.Experts.rwm_loss_le_sqrt_minCumLoss`: [BlumMansour2007AGT,
  Theorem 4.5 and Exercise 4.3].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_rwm_gt_pw_sq_bound`: counterexample showing
  RWM with `(1 - η) ^ ℓ` violates the comparator-second-order `Q_k` bound of PW on `[0, 1]` losses.
* `Cslib.MachineLearning.OnlineLearning.Experts.mw_payoff_ge_sub_sq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mw_payoff_ge_sub_sqrt_qmax`: [BlumMansour2007AGT,
  Exercise 4.4].
* `Cslib.MachineLearning.OnlineLearning.Experts.anytimeHedge_regret_le`: horizon-free `3 √(T ln N)`
  regret of `anytimeHedgeProb`.
* `Cslib.MachineLearning.OnlineLearning.Experts.rwm_prob_le_of_dominated_mixed`,
  `Cslib.MachineLearning.OnlineLearning.Experts.rwm_sum_prob_le_of_dominated_mixed`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mw_prob_le_of_dominated`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mw_sum_prob_le_of_dominated`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_low_external_regret_dominated_weight`:
  [BlumMansour2007AGT, Exercise 4.8].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [N. Littlestone and M. K. Warmuth, *The weighted majority algorithm*][LittlestoneWarmuth1994]
* [N. Cesa-Bianchi, Y. Mansour, and G. Stoltz, *Improved second-order bounds for prediction with
  expert advice*][CesaBianchiMansourStoltz2007]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*} [Fintype ι]

/-! ### Cumulative losses and minimum-loss leaders -/

omit [Fintype ι] in
/-- Cumulative loss `∑ s < t, ℓ s i` of expert `i` before round `t`. -/
@[expose] noncomputable def cumLoss (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ s ∈ range t, ℓ s i

omit [Fintype ι] in
@[simp] theorem cumLoss_zero (ℓ : ℕ → ι → ℝ) (i : ι) : cumLoss ℓ 0 i = 0 := by
  simp only [cumLoss, range_zero, sum_empty]

omit [Fintype ι] in
theorem cumLoss_succ (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    cumLoss ℓ (t + 1) i = cumLoss ℓ t i + ℓ t i :=
  sum_range_succ _ _

omit [Fintype ι] in
theorem cumLoss_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    cumLoss ℓ t = cumLoss ℓ' t := by
  funext i
  exact sum_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]

/-- Minimum cumulative loss `min_i cumLoss ℓ t i` before round `t` (`L_min^t`). -/
noncomputable def minCumLoss [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  univ.inf' univ_nonempty (cumLoss ℓ t)

@[simp] theorem minCumLoss_zero [Nonempty ι] (ℓ : ℕ → ι → ℝ) : minCumLoss ℓ 0 = 0 := by
  unfold minCumLoss
  apply le_antisymm
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact (inf'_le _ (mem_univ i₀)).trans_eq (cumLoss_zero ℓ i₀)
  · exact le_inf' _ _ fun i _ => (cumLoss_zero ℓ i).symm.le

theorem minCumLoss_le [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    minCumLoss ℓ t ≤ cumLoss ℓ t i :=
  inf'_le _ (mem_univ i)

theorem le_minCumLoss_iff [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {c : ℝ} :
    c ≤ minCumLoss ℓ t ↔ ∀ i, c ≤ cumLoss ℓ t i := by
  unfold minCumLoss
  simp only [le_inf'_iff, mem_univ, forall_true_left]

theorem exists_cumLoss_eq_minCumLoss [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∃ i, cumLoss ℓ t i = minCumLoss ℓ t := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_inf' univ_nonempty (cumLoss ℓ t)
  exact ⟨i, hi.symm⟩

theorem minCumLoss_nonneg [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ s < t, ∀ i, 0 ≤ ℓ s i) : 0 ≤ minCumLoss ℓ t :=
  le_minCumLoss_iff.mpr fun i => sum_nonneg fun s hs => hℓ s (mem_range.mp hs) i

theorem minCumLoss_mono_succ [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ i, 0 ≤ ℓ t i) : minCumLoss ℓ t ≤ minCumLoss ℓ (t + 1) :=
  le_minCumLoss_iff.mpr fun i => by
    rw [cumLoss_succ]
    linarith [minCumLoss_le ℓ t i, hℓ i]

theorem minCumLoss_congr [Nonempty ι] {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    minCumLoss ℓ t = minCumLoss ℓ' t := by
  simp only [minCumLoss, cumLoss_congr h]

/-- The set `S^t` of current minimum-cumulative-loss leaders before round `t`. -/
noncomputable def leaders [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : Finset ι :=
  univ.filter fun i => cumLoss ℓ t i = minCumLoss ℓ t

theorem mem_leaders [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {i : ι} :
    i ∈ leaders ℓ t ↔ cumLoss ℓ t i = minCumLoss ℓ t := by
  simp only [leaders, mem_filter, mem_univ, true_and]

theorem leaders_nonempty [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : (leaders ℓ t).Nonempty := by
  obtain ⟨i, hi⟩ := exists_cumLoss_eq_minCumLoss ℓ t
  exact ⟨i, mem_leaders.mpr hi⟩

@[simp] theorem leaders_zero [Nonempty ι] (ℓ : ℕ → ι → ℝ) : leaders ℓ 0 = univ := by
  ext i
  simp only [mem_leaders, cumLoss_zero, minCumLoss_zero, mem_univ]

theorem leaders_congr [Nonempty ι] {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    leaders ℓ t = leaders ℓ' t := by
  ext i
  simp only [mem_leaders, cumLoss_congr h, minCumLoss_congr h]

/-! ### Deterministic Greedy (Follow-the-Leader) and Theorem 4.2 -/

/-- **Deterministic Greedy (Follow-the-Leader)** [BlumMansour2007AGT, §4.3.1, p. 83]: in round `t`,
select the minimum-index action among `leaders ℓ t`. -/
noncomputable def greedyPlay [Nonempty ι] [LinearOrder ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι :=
  (leaders ℓ t).min' (leaders_nonempty ℓ t)

theorem greedyPlay_mem_leaders [Nonempty ι] [LinearOrder ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    greedyPlay ℓ t ∈ leaders ℓ t :=
  min'_mem _ _

theorem greedyPlay_congr [Nonempty ι] [LinearOrder ι] {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) : greedyPlay ℓ t = greedyPlay ℓ' t := by
  simp only [greedyPlay, leaders_congr h]

/-- Window potential `∑ i, max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)` for the `[0, 1]` Greedy
analysis. -/
private noncomputable def greedyPotential [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)

private theorem greedyPotential_zero [Nonempty ι] (ℓ : ℕ → ι → ℝ) :
    greedyPotential ℓ 0 = Fintype.card ι := by
  simp only [greedyPotential, minCumLoss_zero, cumLoss_zero, add_zero, sub_zero,
    max_eq_right zero_le_one, sum_const, card_univ, nsmul_eq_mul, mul_one]

private theorem one_le_greedyPotential [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    1 ≤ greedyPotential ℓ t := by
  obtain ⟨i₀, hi₀⟩ := exists_cumLoss_eq_minCumLoss ℓ t
  calc (1 : ℝ) = max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i₀) := by
        rw [hi₀, add_sub_cancel_right, max_eq_right zero_le_one]
    _ ≤ greedyPotential ℓ t :=
        single_le_sum (f := fun j => max (0 : ℝ) (1 + minCumLoss ℓ t - cumLoss ℓ t j))
          (fun j _ => le_max_left (0 : ℝ) _) (mem_univ i₀)

private theorem greedyPotential_step [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {x : ι}
    (hx : x ∈ leaders ℓ t) (hℓ : ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    ℓ t x + greedyPotential ℓ (t + 1) - greedyPotential ℓ t ≤
      Fintype.card ι * (minCumLoss ℓ (t + 1) - minCumLoss ℓ t) := by
  classical
  have hx_eq : cumLoss ℓ t x = minCumLoss ℓ t := mem_leaders.mp hx
  set Δm := minCumLoss ℓ (t + 1) - minCumLoss ℓ t
  have hΔm_nn : 0 ≤ Δm := sub_nonneg.mpr (minCumLoss_mono_succ fun i => (hℓ i).1)
  have hΔm_le : Δm ≤ ℓ t x := by
    have h1 := minCumLoss_le ℓ (t + 1) x
    rw [cumLoss_succ, hx_eq] at h1
    linarith
  have hterm_x : max 0 (1 + minCumLoss ℓ (t + 1) - cumLoss ℓ (t + 1) x) -
      max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t x) = Δm - ℓ t x := by
    have h0 : 0 ≤ 1 + minCumLoss ℓ (t + 1) - cumLoss ℓ (t + 1) x := by
      rw [cumLoss_succ, hx_eq]
      linarith [(hℓ x).2]
    rw [max_eq_right h0, hx_eq, add_sub_cancel_right, max_eq_right zero_le_one, cumLoss_succ, hx_eq]
    ring
  have hterm_other : ∀ i, max 0 (1 + minCumLoss ℓ (t + 1) - cumLoss ℓ (t + 1) i) -
      max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i) ≤ Δm := fun i => by
    rw [cumLoss_succ]
    have hli := (hℓ i).1
    have h1 : max 0 (1 + minCumLoss ℓ (t + 1) - (cumLoss ℓ t i + ℓ t i)) ≤
        max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i) + Δm := by
      apply max_le
      · linarith [le_max_left 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)]
      · linarith [le_max_right 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)]
    linarith
  have hdiff : greedyPotential ℓ (t + 1) - greedyPotential ℓ t =
      ∑ i, (max 0 (1 + minCumLoss ℓ (t + 1) - cumLoss ℓ (t + 1) i) -
        max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)) := by
    simp only [greedyPotential, sum_sub_distrib]
  rw [add_sub_assoc, hdiff, ← add_sum_erase _ _ (mem_univ x), hterm_x]
  have herase : ∑ i ∈ univ.erase x,
      (max 0 (1 + minCumLoss ℓ (t + 1) - cumLoss ℓ (t + 1) i) -
        max 0 (1 + minCumLoss ℓ t - cumLoss ℓ t i)) ≤ ((Fintype.card ι : ℝ) - 1) * Δm := by
    calc ∑ i ∈ univ.erase x, _ ≤ ∑ _i ∈ univ.erase x, Δm :=
          sum_le_sum fun i _ => hterm_other i
      _ = ((univ.erase x).card : ℝ) * Δm := by rw [sum_const, nsmul_eq_mul]
      _ = ((Fintype.card ι : ℝ) - 1) * Δm := by
          have hc : 1 ≤ Fintype.card ι := Fintype.card_pos
          rw [card_erase_of_mem (mem_univ x), card_univ, Nat.cast_sub hc, Nat.cast_one]
  linarith

/-- **Greedy external-regret bound** [BlumMansour2007AGT, Theorem 4.2, p. 83]: for any tie-breaking
sequence `x` selecting `x t ∈ leaders ℓ t` and any `[0, 1]`-valued loss sequence `ℓ` (in particular
any `{0, 1}` loss sequence), the Greedy learner's total loss satisfies
`∑ t < T, ℓ t (x t) ≤ N * minCumLoss ℓ T + (N - 1)`. -/
theorem greedy_loss_le [Nonempty ι] {ℓ : ℕ → ι → ℝ} {x : ℕ → ι} {T : ℕ}
    (hx : ∀ t < T, x t ∈ leaders ℓ t) (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ t ∈ range T, ℓ t (x t) ≤
      Fintype.card ι * minCumLoss ℓ T + (Fintype.card ι - 1) := by
  have htel : ∑ t ∈ range T, ℓ t (x t) + greedyPotential ℓ T - greedyPotential ℓ 0 ≤
      Fintype.card ι * (minCumLoss ℓ T - minCumLoss ℓ 0) := by
    induction T with
    | zero => simp only [range_zero, sum_empty, zero_add, sub_self, mul_zero, le_rfl]
    | succ T ih =>
      have ih' := ih (fun t ht => hx t (by omega)) (fun t ht => hℓ t (by omega))
      have hstep := greedyPotential_step (hx T (by omega)) (hℓ T (by omega))
      rw [sum_range_succ]
      linarith
  rw [greedyPotential_zero, minCumLoss_zero, sub_zero] at htel
  linarith [one_le_greedyPotential ℓ T]

/-- **Greedy external-regret bound** for `greedyPlay` [BlumMansour2007AGT, Theorem 4.2, p. 83]. -/
theorem greedyPlay_loss_le [Nonempty ι] [LinearOrder ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ t ∈ range T, ℓ t (greedyPlay ℓ t) ≤
      Fintype.card ι * minCumLoss ℓ T + (Fintype.card ι - 1) :=
  greedy_loss_le (fun t _ => greedyPlay_mem_leaders ℓ t) hℓ

/-! ### Randomized Greedy and Theorem 4.4 -/

/-- **Randomized Greedy (RG)** [BlumMansour2007AGT, §4.3.1, p. 84]: in round `t`, play the uniform
distribution over `leaders ℓ t`. -/
noncomputable def randGreedyProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  open Classical in
  if i ∈ leaders ℓ t then 1 / (leaders ℓ t).card else 0

theorem randGreedyProb_nonneg [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ randGreedyProb ℓ t i := by
  unfold randGreedyProb
  split_ifs <;> positivity

theorem sum_randGreedyProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, randGreedyProb ℓ t i = 1 := by
  classical
  have hpos : (0 : ℝ) < (leaders ℓ t).card := Nat.cast_pos.mpr (leaders_nonempty ℓ t).card_pos
  have hdec : (∑ i, randGreedyProb ℓ t i) =
      ∑ i, if i ∈ leaders ℓ t then (1 : ℝ) / (leaders ℓ t).card else 0 :=
    sum_congr rfl fun i _ => by
      unfold randGreedyProb
      congr 1
  rw [hdec]
  simp only [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  field_simp

theorem randGreedyProb_congr [Nonempty ι] {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) : randGreedyProb ℓ t = randGreedyProb ℓ' t := by
  funext i
  have hl := leaders_congr h
  unfold randGreedyProb
  rw [hl]

omit [Fintype ι] in
private theorem cumLoss_nat_of_binary {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ s < t, ∀ i, ℓ s i = 0 ∨ ℓ s i = 1) (i : ι) :
    ∃ n : ℕ, cumLoss ℓ t i = n := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
    obtain ⟨n, hn⟩ := ih fun s hs => hℓ s (by omega)
    rcases hℓ t (by omega) i with h0 | h1
    · exact ⟨n, by rw [cumLoss_succ, hn, h0, add_zero]⟩
    · exact ⟨n + 1, by rw [cumLoss_succ, hn, h1]; push_cast; ring⟩

private theorem add_one_le_cumLoss_of_notMem_leaders [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ s < t, ∀ i, ℓ s i = 0 ∨ ℓ s i = 1) {i : ι} (hi : i ∉ leaders ℓ t) :
    minCumLoss ℓ t + 1 ≤ cumLoss ℓ t i := by
  obtain ⟨j, hj⟩ := exists_cumLoss_eq_minCumLoss ℓ t
  obtain ⟨ni, hni⟩ := cumLoss_nat_of_binary hℓ i
  obtain ⟨nj, hnj⟩ := cumLoss_nat_of_binary hℓ j
  have hle : cumLoss ℓ t j ≤ cumLoss ℓ t i := hj.trans_le (minCumLoss_le ℓ t i)
  have hne : cumLoss ℓ t i ≠ minCumLoss ℓ t := mt mem_leaders.mpr hi
  rw [← hj] at hne ⊢
  rw [hni, hnj] at hle hne ⊢
  have hlt : nj < ni := lt_of_le_of_ne (by exact_mod_cast hle) (fun h => hne (by rw [h]))
  exact_mod_cast hlt

/-- Exact inductive invariant for Randomized Greedy on `{0, 1}` losses
[BlumMansour2007AGT, proof of Theorem 4.4, p. 84]:
`L_RG^T ≤ (H_N - H_{|S^T|}) + H_N * L_min^T`. -/
theorem randGreedy_loss_le_sub_harmonic [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) :
    ∑ t ∈ range T, ∑ i, randGreedyProb ℓ t i * ℓ t i ≤
      ((harmonic (Fintype.card ι) : ℝ) - harmonic (leaders ℓ T).card) +
        harmonic (Fintype.card ι) * minCumLoss ℓ T := by
  classical
  induction T with
  | zero =>
    simp only [range_zero, sum_empty, leaders_zero, card_univ, sub_self, minCumLoss_zero,
      mul_zero, add_zero, le_rfl]
  | succ t ih =>
    have hℓ_prev : ∀ s < t, ∀ i, ℓ s i = 0 ∨ ℓ s i = 1 := fun s hs => hℓ s (by omega)
    have ih' := ih hℓ_prev
    have hℓ_t : ∀ i, ℓ t i = 0 ∨ ℓ t i = 1 := hℓ t (by omega)
    set S := leaders ℓ t
    set S' := leaders ℓ (t + 1)
    set A := S.filter fun i => ℓ t i = 0
    have hS_ne : S.Nonempty := leaders_nonempty ℓ t
    have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS_ne.card_pos
    have hstep_loss : ∑ i, randGreedyProb ℓ t i * ℓ t i = ((S.card : ℝ) - A.card) / S.card := by
      have hexp : ∑ i, randGreedyProb ℓ t i * ℓ t i = (∑ i ∈ S, ℓ t i) / S.card := by
        have hdec : ∑ i, randGreedyProb ℓ t i * ℓ t i =
            ∑ i, (if i ∈ S then (1 : ℝ) / S.card else 0) * ℓ t i :=
          sum_congr rfl fun i _ => by
            dsimp only [S]
            unfold randGreedyProb
            congr 2
        rw [hdec]
        simp only [ite_mul, zero_mul, ← sum_filter, filter_mem_eq_inter, univ_inter,
          one_div, inv_mul_eq_div, ← sum_div]
      rw [hexp]
      congr 1
      have hpart := sum_filter_add_sum_filter_not S (fun i => ℓ t i = 0) (fun _ => (1 : ℝ))
      simp only [sum_const, nsmul_eq_mul, mul_one] at hpart
      have hsum1 : ∑ i ∈ S, ℓ t i = (S.filter fun i => ¬ ℓ t i = 0).card := by
        calc ∑ i ∈ S, ℓ t i = ∑ i ∈ S, if ¬ ℓ t i = 0 then (1 : ℝ) else 0 :=
              sum_congr rfl fun i _ => by
                rcases hℓ_t i with h0 | h1
                · simp [h0]
                · simp [h1]
          _ = (S.filter fun i => ¬ ℓ t i = 0).card := by
              rw [← sum_filter]
              simp only [sum_const, nsmul_eq_mul, mul_one]
      rw [hsum1]
      linarith
    rw [sum_range_succ, hstep_loss]
    by_cases hA : A.Nonempty
    · -- At least one leader incurs loss `0`: `minCumLoss` stays unchanged and `S' = A`.
      obtain ⟨i₀, hi₀⟩ := hA
      have hi₀S : i₀ ∈ S := (mem_filter.mp hi₀).1
      have hi₀0 : ℓ t i₀ = 0 := (mem_filter.mp hi₀).2
      have hm_eq : minCumLoss ℓ (t + 1) = minCumLoss ℓ t := by
        apply le_antisymm
        · calc minCumLoss ℓ (t + 1) ≤ cumLoss ℓ (t + 1) i₀ := minCumLoss_le ℓ (t + 1) i₀
            _ = minCumLoss ℓ t := by rw [cumLoss_succ, mem_leaders.mp hi₀S, hi₀0, add_zero]
        · exact minCumLoss_mono_succ fun i => by rcases hℓ_t i with h | h <;> linarith
      have hS'_eq : S' = A := by
        ext i
        simp only [S', mem_leaders, hm_eq, A, mem_filter, S, cumLoss_succ]
        constructor
        · intro hi
          by_cases hmem : i ∈ leaders ℓ t
          · rw [mem_leaders.mp hmem] at hi
            exact ⟨mem_leaders.mp hmem, by linarith⟩
          · have hge := add_one_le_cumLoss_of_notMem_leaders hℓ_prev hmem
            have hnn : 0 ≤ ℓ t i := by rcases hℓ_t i with h | h <;> linarith
            linarith
        · rintro ⟨hi1, hi2⟩
          linarith
      have hcard_le : S'.card ≤ S.card := by
        rw [hS'_eq]
        exact card_filter_le _ _
      have hharm : ((S.card : ℝ) - S'.card) / S.card ≤
          (harmonic S.card : ℝ) - harmonic S'.card := by
        have hq : ((((S.card : ℚ) - S'.card) / S.card : ℚ) : ℝ) ≤
            ((harmonic S.card - harmonic S'.card : ℚ) : ℝ) := by
          exact_mod_cast sub_div_le_harmonic_sub hcard_le
        push_cast at hq
        exact hq
      rw [hm_eq, ← hS'_eq]
      linarith
    · -- Every current leader incurs loss `1`: `minCumLoss` increases by `1`.
      rw [not_nonempty_iff_eq_empty] at hA
      have hA_card : A.card = 0 := by rw [hA, card_empty]
      have hm_eq : minCumLoss ℓ (t + 1) = minCumLoss ℓ t + 1 := by
        apply le_antisymm
        · obtain ⟨i₀, hi₀⟩ := hS_ne
          have h1 : ℓ t i₀ = 1 := by
            rcases hℓ_t i₀ with h0 | h1
            · exfalso
              have : i₀ ∈ A := mem_filter.mpr ⟨hi₀, h0⟩
              rw [hA] at this
              exact notMem_empty _ this
            · exact h1
          calc minCumLoss ℓ (t + 1) ≤ cumLoss ℓ (t + 1) i₀ := minCumLoss_le ℓ (t + 1) i₀
            _ = minCumLoss ℓ t + 1 := by rw [cumLoss_succ, mem_leaders.mp hi₀, h1]
        · rw [le_minCumLoss_iff]
          intro i
          rw [cumLoss_succ]
          by_cases hmem : i ∈ S
          · have h1 : ℓ t i = 1 := by
              rcases hℓ_t i with h0 | h1
              · exfalso
                have : i ∈ A := mem_filter.mpr ⟨hmem, h0⟩
                rw [hA] at this
                exact notMem_empty _ this
              · exact h1
            rw [mem_leaders.mp hmem, h1]
          · have hge := add_one_le_cumLoss_of_notMem_leaders hℓ_prev hmem
            have hnn : 0 ≤ ℓ t i := by rcases hℓ_t i with h | h <;> linarith
            linarith
      have h1_le_HS : (1 : ℝ) ≤ harmonic S.card := by
        exact_mod_cast one_le_harmonic hS_ne.card_pos.ne'
      have hHS'_le : (harmonic S'.card : ℝ) ≤ harmonic (Fintype.card ι) := by
        exact_mod_cast harmonic_mono (card_le_univ S')
      rw [hA_card, Nat.cast_zero, sub_zero, div_self hS_pos.ne', hm_eq, mul_add, mul_one]
      linarith

/-- **Harmonic bound for Randomized Greedy**: on `{0, 1}` loss sequences,
`L_RG^T ≤ (H_N - 1) + H_N * L_min^T`. -/
theorem randGreedy_loss_le_harmonic [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) :
    ∑ t ∈ range T, ∑ i, randGreedyProb ℓ t i * ℓ t i ≤
      ((harmonic (Fintype.card ι) : ℝ) - 1) + harmonic (Fintype.card ι) * minCumLoss ℓ T := by
  have h := randGreedy_loss_le_sub_harmonic hℓ
  have h1 : (1 : ℝ) ≤ harmonic (leaders ℓ T).card := by
    exact_mod_cast one_le_harmonic (leaders_nonempty ℓ T).card_pos.ne'
  linarith

/-- **Logarithmic bound for Randomized Greedy** [BlumMansour2007AGT, Theorem 4.4, p. 84]: on
`{0, 1}` loss sequences, `L_RG^T ≤ ln N + (1 + ln N) * L_min^T`. -/
theorem randGreedy_loss_le_log [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) :
    ∑ t ∈ range T, ∑ i, randGreedyProb ℓ t i * ℓ t i ≤
      log (Fintype.card ι) + (1 + log (Fintype.card ι)) * minCumLoss ℓ T := by
  have h := randGreedy_loss_le_harmonic hℓ
  have hlog : (harmonic (Fintype.card ι) : ℝ) ≤ 1 + log (Fintype.card ι) :=
    harmonic_le_one_add_log (Fintype.card ι)
  have hm_nn : 0 ≤ minCumLoss ℓ T :=
    minCumLoss_nonneg fun s hs i => by rcases hℓ s hs i with h0 | h1 <;> linarith
  nlinarith

/-! ### Randomized Weighted Majority, Theorem 4.5, and Exercises 4.3–4.4 -/

/-- The update factor `(1 - η) ^ x` of Randomized Weighted Majority on `[0, 1]` losses
[BlumMansour2007AGT, §4.3.2, p. 85, and Exercise 4.3, p. 101]. -/
noncomputable def rwmFactor (η x : ℝ) : ℝ := (1 - η) ^ x

@[simp] theorem rwmFactor_apply (η x : ℝ) : rwmFactor η x = (1 - η) ^ x := by
  rw [rwmFactor]

/-- On `{0, 1}` losses, `rwmFactor` coincides with `mwFactor`. -/
theorem rwmFactor_eq_mwFactor_of_binary {η x : ℝ} (hx : x = 0 ∨ x = 1) :
    rwmFactor η x = mwFactor η x := by
  rcases hx with rfl | rfl <;> simp [rwmFactor_apply, mwFactor_apply]

/-- Convexity estimate `(1 - η) ^ x ≤ 1 - η x` for `η < 1` and `x ∈ [0, 1]`. -/
private theorem rwmFactor_le_mwFactor {η x : ℝ} (hη : η < 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    rwmFactor η x ≤ 1 - η * x := by
  have h1η : 0 < 1 - η := by linarith
  rw [rwmFactor_apply, rpow_def_of_pos h1η, mul_comm (log (1 - η)) x]
  have hconv := convexOn_exp.2 (Set.mem_univ (log (1 - η))) (Set.mem_univ 0)
    hx.1 (sub_nonneg.mpr hx.2) (by ring : x + (1 - x) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one, exp_log h1η] at hconv
  linarith

/-- **Randomized Weighted Majority on `[0, 1]` losses** [BlumMansour2007AGT, Theorem 4.5 and
Exercise 4.3]: for `0 < η ≤ 1 / 2`, `[0, 1]` losses, and every expert `i`,
`L_RWM^T ≤ (1 + η) * cumLoss ℓ T i + ln N / η`. -/
theorem rwm_loss_le {η : ℝ} {ℓ : ℕ → ι → ℝ} {T : ℕ} (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hℓ : ∀ s < T, ∀ j, ℓ s j ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j ≤
      (1 + η) * cumLoss ℓ T i + log (Fintype.card ι) / η := by
  have : Nonempty ι := ⟨i⟩
  have h1η : 0 < 1 - η := by linarith
  have hφ : ∀ s < T, ∀ j, 0 < rwmFactor η (ℓ s j) := fun _ _ _ => rpow_pos_of_pos h1η _
  have hmaster := sum_log_le_log_card_add hφ i
  have hlow : -((η + η ^ 2) * cumLoss ℓ T i) ≤ ∑ s ∈ range T, log (rwmFactor η (ℓ s i)) := by
    rw [cumLoss, mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun s hs => ?_
    rw [rwmFactor_apply, log_rpow h1η]
    have hlog := neg_sub_sq_le_log_one_sub hη'
    have hs0 := (hℓ s (mem_range.mp hs) i).1
    nlinarith
  have hup : ∑ s ∈ range T, log (∑ j, prob (rwmFactor η) ℓ s j * rwmFactor η (ℓ s j)) ≤
      -(η * ∑ t ∈ range T, ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun t ht => ?_
    have ht' := mem_range.mp ht
    have hφt : ∀ s < t, ∀ j, 0 < rwmFactor η (ℓ s j) := fun s hs => hφ s (by omega)
    have hpos := sum_prob_mul_pos (φ := rwmFactor η) (ℓ := ℓ) (t := t)
      fun s hs => hφ s (by omega)
    have hle : ∑ j, prob (rwmFactor η) ℓ t j * rwmFactor η (ℓ t j) ≤
        1 - η * ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j := by
      calc ∑ j, prob (rwmFactor η) ℓ t j * rwmFactor η (ℓ t j)
          ≤ ∑ j, prob (rwmFactor η) ℓ t j * (1 - η * ℓ t j) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
              (rwmFactor_le_mwFactor (by linarith) (hℓ t ht' j)) (prob_nonneg hφt j)
        _ = 1 - η * ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j := by
            simp only [mul_sub, mul_one, sum_sub_distrib, sum_prob hφt, mul_sum]
            congr 1
            exact sum_congr rfl fun j _ => by ring
    linarith [log_le_sub_one_of_pos hpos]
  have key : η * ∑ t ∈ range T, ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j ≤
      η * ((1 + η) * cumLoss ℓ T i + log (Fintype.card ι) / η) := by
    rw [mul_add, mul_div_cancel₀ _ hη.ne']
    nlinarith
  exact le_of_mul_le_mul_left key hη

/-- Capped step size `min (1 / 2) √(L / Q)` (defined as `1 / 2` when `Q < 4 * L` so `Q = 0` avoids
division by zero). -/
noncomputable def tunedStep (L Q : ℝ) : ℝ :=
  if 4 * L ≤ Q then √(L / Q) else 1 / 2

theorem tunedStep_pos {L : ℝ} (hL : 0 < L) (Q : ℝ) : 0 < tunedStep L Q := by
  unfold tunedStep
  split_ifs with h
  · have hQ : 0 < Q := by linarith
    exact sqrt_pos.mpr (div_pos hL hQ)
  · norm_num

theorem tunedStep_le_half {L : ℝ} (hL : 0 ≤ L) (Q : ℝ) : tunedStep L Q ≤ 1 / 2 := by
  unfold tunedStep
  split_ifs with h
  · rcases eq_or_lt_of_le hL with rfl | hLpos
    · simp
    · have hQ : 0 < Q := by linarith
      rw [show (1 / 2 : ℝ) = √(1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by rw [div_le_iff₀ hQ]; linarith)
  · exact le_rfl

/-- Balancing inequality for `tunedStep`: for `L > 0` and `0 ≤ q ≤ Q`,
`tunedStep L Q * q + L / tunedStep L Q ≤ 2 * √(Q * L) + 2 * L`. -/
theorem tunedStep_mul_add_div_le {L q Q : ℝ} (hL : 0 < L) (hqQ : q ≤ Q) (hQ : 0 ≤ Q) :
    tunedStep L Q * q + L / tunedStep L Q ≤ 2 * √(Q * L) + 2 * L := by
  unfold tunedStep
  split_ifs with h
  · have hQpos : 0 < Q := by linarith
    have hηpos : 0 < √(L / Q) := sqrt_pos.mpr (div_pos hL hQpos)
    have hbal := sqrt_div_mul_add_div_sqrt_div hL hQpos
    nlinarith [mul_le_mul_of_nonneg_left hqQ hηpos.le]
  · push Not at h
    have hq_le : Q ≤ 2 * √(Q * L) := by
      have hsq : Q ^ 2 ≤ (2 * √(Q * L)) ^ 2 := by
        rw [mul_pow, sq_sqrt (mul_nonneg hQ hL.le)]
        nlinarith
      exact le_of_sq_le_sq hsq (by positivity)
    linarith

/-- **Horizon-tuned RWM bound** [BlumMansour2007AGT, Theorem 4.5 and Exercise 4.3]: setting
`η = tunedStep (ln N) T` (`= min {√(ln N / T), 1 / 2}`) achieves
`L_RWM^T ≤ minCumLoss ℓ T + 2 √(T ln N)` for all `N ≥ 2` and all `T : ℕ` on `[0, 1]` losses. -/
theorem rwm_loss_le_tunedStep (hn : 2 ≤ Fintype.card ι) {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ j, ℓ s j ∈ Set.Icc (0 : ℝ) 1) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    ∑ t ∈ range T, ∑ j, prob (rwmFactor (tunedStep (log (Fintype.card ι)) T)) ℓ t j * ℓ t j ≤
      minCumLoss ℓ T + 2 * √(T * log (Fintype.card ι)) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set L := log (Fintype.card ι)
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  rcases eq_or_lt_of_le (Nat.zero_le T) with rfl | hT0
  · simp
  · have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT0
    by_cases h4 : 4 * L ≤ T
    · obtain ⟨i₀, hi₀⟩ := exists_cumLoss_eq_minCumLoss ℓ T
      have hη := tunedStep_pos hL T
      have hη' := tunedStep_le_half hL.le T
      have h := rwm_loss_le hη hη' hℓ i₀
      rw [hi₀] at h
      have hm_le_T : minCumLoss ℓ T ≤ T := by
        rw [← hi₀]
        calc cumLoss ℓ T i₀ ≤ ∑ _s ∈ range T, (1 : ℝ) :=
              sum_le_sum fun s hs => (hℓ s (mem_range.mp hs) i₀).2
          _ = T := by simp
      have hstep_eq : tunedStep L T = √(L / T) := by simp [tunedStep, h4]
      rw [hstep_eq] at h hη ⊢
      have hbal := sqrt_div_mul_add_div_sqrt_div hL hTr
      nlinarith [mul_le_mul_of_nonneg_left hm_le_T hη.le]
    · push Not at h4
      have hloss_le_T : ∑ t ∈ range T, ∑ j,
          prob (rwmFactor (tunedStep L T)) ℓ t j * ℓ t j ≤ T := by
        calc ∑ t ∈ range T, _ ≤ ∑ _t ∈ range T, (1 : ℝ) := sum_le_sum fun t ht => by
              have hφ : ∀ s < t, ∀ j, 0 < rwmFactor (tunedStep L T) (ℓ s j) := fun _ _ _ =>
                rpow_pos_of_pos (by linarith [tunedStep_le_half hL.le T]) _
              calc ∑ j, prob (rwmFactor (tunedStep L T)) ℓ t j * ℓ t j
                  ≤ ∑ j, prob (rwmFactor (tunedStep L T)) ℓ t j * 1 :=
                    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
                      (hℓ t (mem_range.mp ht) j).2 (prob_nonneg hφ j)
                _ = 1 := by simp [sum_prob hφ]
          _ = T := by simp
      have hT_le_sqrt : (T : ℝ) ≤ 2 * √(T * L) := by
        have hsq : (T : ℝ) ^ 2 ≤ (2 * √(T * L)) ^ 2 := by
          rw [mul_pow, sq_sqrt (by positivity)]
          nlinarith
        exact le_of_sq_le_sq hsq (by positivity)
      have hm_nn : 0 ≤ minCumLoss ℓ T := minCumLoss_nonneg fun s hs j => (hℓ s hs j).1
      linarith

/-- **First-order `L_min`-tuned RWM bound** [BlumMansour2007AGT, Note to Theorem 4.5, p. 85]:
with `η = tunedStep (ln N) (minCumLoss ℓ T)` (`= min {√(ln N / L_min), 1 / 2}`), RWM satisfies
`L_RWM^T ≤ L_min^T + 2 √(L_min^T ln N) + 2 ln N` for all `N ≥ 2` and `[0, 1]` losses. -/
theorem rwm_loss_le_sqrt_minCumLoss (hn : 2 ≤ Fintype.card ι) {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ j, ℓ s j ∈ Set.Icc (0 : ℝ) 1) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    ∑ t ∈ range T, ∑ j,
        prob (rwmFactor (tunedStep (log (Fintype.card ι)) (minCumLoss ℓ T))) ℓ t j * ℓ t j ≤
      minCumLoss ℓ T + 2 * √(minCumLoss ℓ T * log (Fintype.card ι)) +
        2 * log (Fintype.card ι) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set L := log (Fintype.card ι)
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  obtain ⟨i₀, hi₀⟩ := exists_cumLoss_eq_minCumLoss ℓ T
  have hm_nn : 0 ≤ minCumLoss ℓ T := minCumLoss_nonneg fun s hs j => (hℓ s hs j).1
  have h := rwm_loss_le (tunedStep_pos hL (minCumLoss ℓ T))
    (tunedStep_le_half hL.le (minCumLoss ℓ T)) hℓ i₀
  rw [hi₀] at h
  have hbal := tunedStep_mul_add_div_le hL le_rfl hm_nn
  linarith

/-- **Counterexample to the comparator-second-order `Q_k` bound for RWM** (clarifying
[BlumMansour2007AGT, Exercise 4.3, p. 101]): there exist `N = 5`, `0 < η ≤ 1 / 2`, `T = 240`, a
`[0, 1]`-valued loss sequence `ℓ`, and an action `k : Fin 5` such that `rwmFactor η` strictly
exceeds the Polynomial Weights bound `cumLoss ℓ T k + η * ∑ t < T, ℓ t k ^ 2 + ln N / η` of
Theorem 4.6 (`mw_regret_le_sq`). -/
theorem exists_rwm_gt_pw_sq_bound :
    ∃ (η : ℝ) (T : ℕ) (ℓ : ℕ → Fin 5 → ℝ) (k : Fin 5),
      0 < η ∧ η ≤ 1 / 2 ∧ (∀ t < T, ∀ j, ℓ t j ∈ Set.Icc (0 : ℝ) 1) ∧
      cumLoss ℓ T k + η * (∑ t ∈ range T, ℓ t k ^ 2) + log (Fintype.card (Fin 5)) / η <
        ∑ t ∈ range T, ∑ j, prob (rwmFactor η) ℓ t j * ℓ t j := by
  let u : ℝ := 6 / 7
  let η : ℝ := 1 - u ^ 4
  let ℓ : ℕ → Fin 5 → ℝ := fun t j =>
    if j = 0 then 1 / 4 else if j.val = t % 4 + 1 then 1 else 0
  refine ⟨η, 240, ℓ, 0, ?_, ?_, ?_, ?_⟩
  · norm_num [η, u]
  · norm_num [η, u]
  · intro t _ j
    dsimp only [ℓ]
    split_ifs <;> norm_num
  · -- Period-4 invariance of cumulative losses modulo an additive constant `b` every 4 steps:
    have hu_pos : (0 : ℝ) < u := by norm_num [u]
    have h1η_eq : 1 - η = u ^ 4 := by ring
    have h1η_pos : 0 < 1 - η := by rw [h1η_eq]; positivity
    have hrpow_quarter : ∀ b r : ℕ, r < 4 →
        (1 - η) ^ ((b : ℝ) + (r : ℝ) * (1 / 4)) = (u ^ 4) ^ b * u ^ r := fun b r _ => by
      rw [h1η_eq, rpow_add (by positivity), rpow_natCast]
      congr 1
      rw [← rpow_natCast u 4, ← rpow_mul hu_pos.le]
      have hexp : ((4 : ℕ) : ℝ) * ((r : ℝ) * (1 / 4)) = (r : ℝ) := by push_cast; ring
      rw [hexp, rpow_natCast]
    have hcum0 : ∀ b r, r < 4 → cumLoss ℓ (4 * b + r) 0 = (b : ℝ) + (r : ℝ) * (1 / 4) := by
      intro b r _
      have : ∀ t, ℓ t 0 = 1 / 4 := fun t => by simp [ℓ]
      simp only [cumLoss, this, sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    have hcum_j : ∀ b r (j : Fin 5), r < 4 → j ≠ 0 →
        cumLoss ℓ (4 * b + r) j = (b : ℝ) + if j.val ≤ r then 1 else 0 := by
      intro b r j hr hj0
      induction b with
      | zero =>
        rw [Nat.mul_zero, Nat.zero_add, Nat.cast_zero, zero_add, cumLoss]
        have hℓj : ∀ t, ℓ t j = if j.val = t % 4 + 1 then 1 else 0 := fun t => by
          simp only [ℓ, hj0, ↓reduceIte]
        fin_cases j
        · exact absurd rfl hj0
        all_goals
          interval_cases r <;>
            (simp only [range_zero, sum_empty, sum_range_succ, hℓj]; norm_num)
      | succ b ih =>
        have hsplit : 4 * (b + 1) + r = (4 * b + r) + 4 := by omega
        rw [hsplit, cumLoss, sum_range_add, ← cumLoss, ih]
        have hblock4 : ∑ x ∈ range 4, ℓ (4 * b + r + x) j = 1 := by
          rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one]
          have hm : ∀ x, (4 * b + r + x) % 4 = (r + x) % 4 := fun x => by
            rw [Nat.add_assoc, Nat.mul_add_mod_self_left]
          dsimp only [ℓ]
          simp only [hj0, ↓reduceIte, hm]
          fin_cases j
          · exact absurd rfl hj0
          all_goals
            interval_cases r <;> norm_num
        rw [hblock4]
        push_cast
        ring
    -- Weight of expert `j` at step `4 * b + r` (`r < 4`) equals `(u ^ 4) ^ b * w0 r j`.
    let w0 : ℕ → Fin 5 → ℝ := fun r j =>
      if j = 0 then u ^ r else if j.val ≤ r then u ^ 4 else 1
    have hweight : ∀ b r, r < 4 → ∀ j : Fin 5,
        weight (rwmFactor η) ℓ (4 * b + r) j = (u ^ 4) ^ b * w0 r j := by
      intro b r hr j
      have hprod : weight (rwmFactor η) ℓ (4 * b + r) j = (1 - η) ^ cumLoss ℓ (4 * b + r) j := by
        unfold weight cumLoss
        induction (4 * b + r) with
        | zero => simp [rwmFactor]
        | succ n ihn =>
          rw [prod_range_succ, sum_range_succ, rpow_add h1η_pos, ihn, rwmFactor_apply]
      rw [hprod]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [w0, ↓reduceIte, hcum0 b r hr, hrpow_quarter b r hr]
      · simp only [w0, hj0, ↓reduceIte, hcum_j b r j hr hj0]
        rw [h1η_eq, rpow_add (by positivity), rpow_natCast]
        congr 1
        split_ifs <;> simp
    have hprob_period : ∀ b r, r < 4 → ∀ j : Fin 5,
        prob (rwmFactor η) ℓ (4 * b + r) j = w0 r j / ∑ m : Fin 5, w0 r m := by
      intro b r hr j
      have hc_ne : ((u ^ 4) ^ b : ℝ) ≠ 0 := by positivity
      simp only [prob, potential, hweight b r hr, ← mul_sum]
      exact mul_div_mul_left _ _ hc_ne
    have hblock_loss : ∀ b, ∑ x ∈ range 4, ∑ j : Fin 5,
        prob (rwmFactor η) ℓ (4 * b + x) j * ℓ (4 * b + x) j =
        ∑ r ∈ range 4, ∑ j : Fin 5, (w0 r j / ∑ m : Fin 5, w0 r m) * ℓ r j := by
      intro b
      refine sum_congr rfl fun r hr => ?_
      have hr' := mem_range.mp hr
      refine sum_congr rfl fun j _ => ?_
      rw [hprob_period b r hr' j]
      congr 1
      dsimp only [ℓ]
      have hmod : (4 * b + r) % 4 = r % 4 := Nat.mul_add_mod_self_left 4 b r
      rw [hmod]
    have hsum60 : ∑ t ∈ range 240, ∑ j : Fin 5, prob (rwmFactor η) ℓ t j * ℓ t j =
        60 * ∑ r ∈ range 4, ∑ j : Fin 5, (w0 r j / ∑ m : Fin 5, w0 r m) * ℓ r j := by
      have h60 : ∀ K : ℕ, ∑ t ∈ range (4 * K), ∑ j : Fin 5, prob (rwmFactor η) ℓ t j * ℓ t j =
          (K : ℝ) * ∑ r ∈ range 4, ∑ j : Fin 5, (w0 r j / ∑ m : Fin 5, w0 r m) * ℓ r j := by
        intro K
        induction K with
        | zero => simp
        | succ K ihK =>
          rw [show 4 * (K + 1) = 4 * K + 4 by omega, sum_range_add, ihK, hblock_loss K]
          push_cast
          ring
      simpa using h60 60
    have hL0 : cumLoss ℓ 240 0 = 60 := by
      have := hcum0 60 0 (by omega)
      norm_num at this
      exact this
    have hQ0 : ∑ t ∈ range 240, ℓ t 0 ^ 2 = 15 := by
      have : ∀ t, ℓ t 0 ^ 2 = 1 / 16 := fun t => by norm_num [ℓ]
      simp only [this, sum_const, card_range, nsmul_eq_mul]
      norm_num
    have hlog5 : log (Fintype.card (Fin 5)) ≤ 2 := by
      rw [Fintype.card_fin, Nat.cast_ofNat, log_le_iff_le_exp (by norm_num)]
      have hq := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    rw [hsum60, hL0, hQ0]
    have hdiv : log (Fintype.card (Fin 5)) / η ≤ 2 / η :=
      div_le_div_of_nonneg_right hlog5 (by norm_num [η, u])
    have hval : 60 + η * 15 + 2 / η <
        60 * ∑ r ∈ range 4, ∑ j : Fin 5, (w0 r j / ∑ m : Fin 5, w0 r m) * ℓ r j := by
      norm_num [sum_range_succ, Fin.sum_univ_five, w0, ℓ, η, u]
    linarith

/-! ### Exercise 4.4: Payoff maximization in `[-1, +1]` -/

/-- Update factor `1 + η x = mwFactor η (-x)` of modified Polynomial Weights for maximizing payoffs
in `[-1, +1]` [BlumMansour2007AGT, Exercise 4.4, p. 101]. -/
def mwPayoffFactor (η x : ℝ) : ℝ := 1 + η * x

@[simp] theorem mwPayoffFactor_apply (η x : ℝ) : mwPayoffFactor η x = 1 + η * x := by
  rw [mwPayoffFactor]

private theorem prob_mwPayoffFactor_eq (η : ℝ) (g : ℕ → ι → ℝ) (t : ℕ) :
    prob (mwPayoffFactor η) g t = prob (mwFactor η) (fun s j => -g s j) t := by
  funext i
  have hw : ∀ j, weight (mwPayoffFactor η) g t j =
      weight (mwFactor η) (fun s k => -g s k) t j := fun j =>
    prod_congr rfl fun s _ => by
      simp only [mwPayoffFactor_apply, mwFactor_apply, mul_neg, sub_neg_eq_add]
  simp only [prob, potential, hw]

/-- **Second-order payoff regret of modified Polynomial Weights** [BlumMansour2007AGT,
Exercise 4.4, p. 101]: for payoffs `g` with `g s j ≥ -1` (in particular `g s j ∈ [-1, 1]`) and
`0 < η ≤ 1 / 2`, for every action `k`,
`∑ t < T, g t k - η * ∑ t < T, g t k ^ 2 - ln N / η ≤ ∑ t < T, ⟨p t, g t⟩`. -/
theorem mw_payoff_ge_sub_sq {η : ℝ} {g : ℕ → ι → ℝ} {T : ℕ} (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hg : ∀ s < T, ∀ j, -1 ≤ g s j) (k : ι) :
    (∑ t ∈ range T, g t k) - η * (∑ t ∈ range T, g t k ^ 2) - log (Fintype.card ι) / η ≤
      ∑ t ∈ range T, ∑ j, prob (mwPayoffFactor η) g t j * g t j := by
  have h := mw_regret_le_sq (ℓ := fun s j => -g s j) (T := T) hη
    (fun s hs j => by have := hg s hs j; nlinarith) k
  simp only [← prob_mwPayoffFactor_eq, mul_neg, sum_neg_distrib, neg_sq] at h
  linarith

/-- **Tuned `Q_max` payoff regret of modified Polynomial Weights** [BlumMansour2007AGT,
Exercise 4.4, p. 101]: for `N ≥ 2` actions, payoffs in `[-1, +1]`, and `Q_max ≥ 0` bounding
`∑ t < T, g t k ^ 2 ≤ Q_max`, setting `η = tunedStep (ln N) Q_max` guarantees expected payoff at
least `∑ t < T, g t k - (2 √(Q_max ln N) + 2 ln N)`. -/
theorem mw_payoff_ge_sub_sqrt_qmax (hn : 2 ≤ Fintype.card ι) {g : ℕ → ι → ℝ} {T : ℕ} {Q_max : ℝ}
    (hQ0 : 0 ≤ Q_max) (hg : ∀ s < T, ∀ j, -1 ≤ g s j)
    {k : ι} (hk : ∑ t ∈ range T, g t k ^ 2 ≤ Q_max) :
    (∑ t ∈ range T, g t k) - (2 * √(Q_max * log (Fintype.card ι)) + 2 * log (Fintype.card ι)) ≤
      ∑ t ∈ range T, ∑ j,
        prob (mwPayoffFactor (tunedStep (log (Fintype.card ι)) Q_max)) g t j * g t j := by
  set L := log (Fintype.card ι)
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  have h := mw_payoff_ge_sub_sq (tunedStep_pos hL Q_max) (tunedStep_le_half hL.le Q_max) hg k
  have hbal := tunedStep_mul_add_div_le hL hk hQ0
  linarith

/-! ### Horizon-free anytime Hedge (`η_t = √(ln N / (t + 1))`) -/

/-- Step size `η_t = √(ln N / (t + 1))` of horizon-free anytime Hedge. -/
noncomputable def anytimeStep (N t : ℕ) : ℝ :=
  √(log N / (t + 1 : ℝ))

/-- **Horizon-free anytime Hedge** (addressing the unknown-`T` remark of [BlumMansour2007AGT,
pp. 85, 87]): in round `t`, weight expert `i` by `exp (-η_t * cumLoss ℓ t i)` with
`η_t = √(ln N / (t + 1))`. -/
noncomputable def anytimeHedgeProb (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  exp (-(anytimeStep (Fintype.card ι) t * cumLoss ℓ t i)) /
    ∑ j, exp (-(anytimeStep (Fintype.card ι) t * cumLoss ℓ t j))

theorem anytimeHedgeProb_nonneg (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ anytimeHedgeProb ℓ t i :=
  div_nonneg (exp_pos _).le (sum_nonneg fun _ _ => (exp_pos _).le)

theorem sum_anytimeHedgeProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, anytimeHedgeProb ℓ t i = 1 := by
  unfold anytimeHedgeProb
  rw [← sum_div]
  exact div_self (sum_pos (fun _ _ => exp_pos _) univ_nonempty).ne'

theorem anytimeHedgeProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    anytimeHedgeProb ℓ t = anytimeHedgeProb ℓ' t := by
  funext i
  simp only [anytimeHedgeProb, cumLoss_congr h]

private theorem sum_inv_sqrt_succ_le (T : ℕ) :
    ∑ t ∈ range T, (1 / √((t : ℝ) + 1)) ≤ 2 * √(T : ℝ) := by
  induction T with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hs1 : 0 < √((t : ℝ) + 1) := sqrt_pos.mpr ht1
    have hstep : 2 * √(t : ℝ) + 1 / √((t : ℝ) + 1) ≤ 2 * √((t : ℝ) + 1) := by
      rw [← mul_le_mul_iff_left₀ hs1, add_mul, div_mul_cancel₀ _ hs1.ne']
      rw [mul_assoc, ← sqrt_mul (Nat.cast_nonneg t), mul_assoc 2, mul_self_sqrt ht1.le]
      have hsq : √((t : ℝ) * ((t : ℝ) + 1)) ≤ (t : ℝ) + 1 / 2 := by
        have h1 : (t : ℝ) * ((t : ℝ) + 1) ≤ ((t : ℝ) + 1 / 2) ^ 2 := by nlinarith
        exact (sqrt_le_sqrt h1).trans_eq (sqrt_sq (by positivity))
      linarith
    linarith

/-- Normalized log-sum-exp potential `(1 / η) * log ((1 / N) * ∑ i, exp (-η * cumLoss ℓ t i))`. -/
private noncomputable def anytimePot [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (η : ℝ) : ℝ :=
  log ((∑ i, exp (-(η * cumLoss ℓ t i))) / Fintype.card ι) / η

private theorem anytimePot_antitone [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) {η₁ η₂ : ℝ}
    (h1 : 0 < η₁) (h12 : η₁ ≤ η₂) :
    anytimePot ℓ t η₁ ≤ anytimePot ℓ t η₂ := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h2 : 0 < η₂ := h1.trans_le h12
  set p := η₂ / η₁
  have hp : 1 ≤ p := (one_le_div h1).mpr h12
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  set w : ι → ℝ := fun _ => 1 / Fintype.card ι
  set z : ι → ℝ := fun i => exp (-(η₁ * cumLoss ℓ t i))
  have hw0 : ∀ i ∈ (univ : Finset ι), 0 ≤ w i := fun _ _ => by positivity
  have hw1 : ∑ i ∈ (univ : Finset ι), w i = 1 := by
    simp only [w, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hz0 : ∀ i ∈ (univ : Finset ι), 0 ≤ z i := fun _ _ => (exp_pos _).le
  have hmean := arith_mean_le_rpow_mean univ w z hw0 hw1 hz0 hp
  have hzp : ∀ i, z i ^ p = exp (-(η₂ * cumLoss ℓ t i)) := fun i => by
    dsimp only [z, p]
    rw [← exp_mul]
    congr 1
    field_simp
  simp only [w, one_div, inv_mul_eq_div, ← sum_div, hzp] at hmean
  have hpos1 : 0 < (∑ i, exp (-(η₁ * cumLoss ℓ t i))) / Fintype.card ι :=
    div_pos (sum_pos (fun _ _ => exp_pos _) univ_nonempty) hN
  have hpos2 : 0 < (∑ i, exp (-(η₂ * cumLoss ℓ t i))) / Fintype.card ι :=
    div_pos (sum_pos (fun _ _ => exp_pos _) univ_nonempty) hN
  have hlog := log_le_log hpos1 hmean
  rw [log_rpow hpos2] at hlog
  unfold anytimePot
  rw [div_le_div_iff₀ h1 h2]
  have hp_inv : p⁻¹ = η₁ / η₂ := by dsimp [p]; field_simp
  rw [hp_inv, div_mul_eq_mul_div, le_div_iff₀ h2] at hlog
  linarith

/-- **Horizon-free external regret of `anytimeHedgeProb`**: for `N ≥ 2` experts, any horizon
`T : ℕ`, any `[0, 1]`-valued loss sequence `ℓ`, and every expert `k`,
`∑ t < T, ⟨anytimeHedgeProb ℓ t, ℓ t⟩ ≤ cumLoss ℓ T k + 3 √(T ln N)`. -/
theorem anytimeHedge_regret_le (hn : 2 ≤ Fintype.card ι) {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ j, ℓ s j ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    ∑ t ∈ range T, ∑ j, anytimeHedgeProb ℓ t j * ℓ t j ≤
      cumLoss ℓ T k + 3 * √(T * log (Fintype.card ι)) := by
  have : Nonempty ι := ⟨k⟩
  rcases eq_or_lt_of_le (Nat.zero_le T) with rfl | hT0
  · simp
  set N := Fintype.card ι
  set L := log N
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  have hη_pos : ∀ t, 0 < anytimeStep N t := fun t =>
    sqrt_pos.mpr (div_pos hL (by positivity))
  have hη_anti : ∀ t, anytimeStep N (t + 1) ≤ anytimeStep N t := fun t => by
    unfold anytimeStep
    gcongr
    linarith
  -- Step inequality: `anytimePot ℓ (t + 1) (η t) - anytimePot ℓ t (η t) ≤ -⟨p t, ℓ t⟩ + η t`
  have hstep : ∀ t < T,
      anytimePot ℓ (t + 1) (anytimeStep N t) - anytimePot ℓ t (anytimeStep N t) ≤
        -(∑ j, anytimeHedgeProb ℓ t j * ℓ t j) + anytimeStep N t := by
    intro t ht
    set η := anytimeStep N t
    have hη := hη_pos t
    set Z := ∑ j, exp (-(η * cumLoss ℓ t j))
    have hZ : 0 < Z := sum_pos (fun _ _ => exp_pos _) univ_nonempty
    set Z' := ∑ j, exp (-(η * cumLoss ℓ (t + 1) j))
    have hZ' : 0 < Z' := sum_pos (fun _ _ => exp_pos _) univ_nonempty
    have hratio : Z' / Z = ∑ j, anytimeHedgeProb ℓ t j * exp (-(η * ℓ t j)) := by
      dsimp only [Z', Z, η]
      simp only [cumLoss_succ, mul_add, neg_add, exp_add, anytimeHedgeProb, N]
      rw [sum_div]
      exact sum_congr rfl fun j _ => by ring
    have hratio_le : Z' / Z ≤ 1 - η * (∑ j, anytimeHedgeProb ℓ t j * ℓ t j) + η ^ 2 := by
      rw [hratio]
      calc ∑ j, anytimeHedgeProb ℓ t j * exp (-(η * ℓ t j))
          ≤ ∑ j, anytimeHedgeProb ℓ t j * (1 - η * ℓ t j + (η * ℓ t j) ^ 2) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
              (exp_neg_le_one_sub_add_sq (by
                have := (hℓ t ht j).1
                nlinarith))
              (anytimeHedgeProb_nonneg ℓ t j)
        _ ≤ ∑ j, anytimeHedgeProb ℓ t j * (1 - η * ℓ t j + η ^ 2) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
              have h0 := (hℓ t ht j).1
              have h1 := (hℓ t ht j).2
              have hsq : ℓ t j ^ 2 ≤ 1 := by nlinarith
              rw [mul_pow]
              nlinarith [sq_nonneg η]) (anytimeHedgeProb_nonneg ℓ t j)
        _ = 1 - η * (∑ j, anytimeHedgeProb ℓ t j * ℓ t j) + η ^ 2 := by
            simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib,
              sum_anytimeHedgeProb ℓ t, mul_sum, ← sum_mul, one_mul]
            congr 1
            congr 1
            exact sum_congr rfl fun j _ => by ring
    have hlog_diff : log (Z' / N) - log (Z / N) = log (Z' / Z) := by
      rw [← log_div (div_pos hZ' hN_pos).ne' (div_pos hZ hN_pos).ne',
        div_div_div_cancel_right₀ hN_pos.ne']
    have hlog_le : log (Z' / Z) ≤ -(η * ∑ j, anytimeHedgeProb ℓ t j * ℓ t j) + η ^ 2 := by
      linarith [log_le_sub_one_of_pos (div_pos hZ' hZ)]
    unfold anytimePot
    rw [← sub_div, hlog_diff, div_le_iff₀ hη]
    nlinarith
  -- Induction across `m = 1, ..., T`: `anytimePot ℓ m (η (m - 1)) ≤ ∑_{t < m} (-loss_t + η_t)`
  have hind : ∀ m, 1 ≤ m → m ≤ T →
      anytimePot ℓ m (anytimeStep N (m - 1)) ≤
        ∑ t ∈ range m, (-(∑ j, anytimeHedgeProb ℓ t j * ℓ t j) + anytimeStep N t) := by
    intro m hm1 hmT
    induction m with
    | zero => omega
    | succ m ihm =>
      rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hmpos
      · rw [Nat.zero_add, Nat.sub_self, range_one, sum_singleton]
        have h0 : anytimePot ℓ 0 (anytimeStep N 0) = 0 := by
          unfold anytimePot
          simp only [cumLoss_zero, mul_zero, neg_zero, exp_zero, sum_const, card_univ,
            nsmul_eq_mul, mul_one]
          rw [div_self hN_pos.ne', log_one, zero_div]
        linarith [hstep 0 (by omega)]
      · have ihm' := ihm hmpos (by omega)
        have hanti : anytimePot ℓ m (anytimeStep N m) ≤
            anytimePot ℓ m (anytimeStep N (m - 1)) :=
          anytimePot_antitone ℓ m (hη_pos m) (by
            convert hη_anti (m - 1) using 2
            omega)
        have hst := hstep m (by omega)
        rw [sum_range_succ, Nat.add_sub_cancel]
        linarith
  have hT_pot := hind T hT0 le_rfl
  -- Lower bound `anytimePot ℓ T (η (T - 1))` by `-cumLoss ℓ T k - L / η (T - 1)`:
  set η_last := anytimeStep N (T - 1)
  have hη_last : 0 < η_last := hη_pos (T - 1)
  have hlow : -cumLoss ℓ T k - L / η_last ≤ anytimePot ℓ T η_last := by
    unfold anytimePot
    rw [le_div_iff₀ hη_last]
    have hsingle : exp (-(η_last * cumLoss ℓ T k)) / N ≤
        (∑ i, exp (-(η_last * cumLoss ℓ T i))) / N :=
      div_le_div_of_nonneg_right
        (single_le_sum (f := fun i => exp (-(η_last * cumLoss ℓ T i)))
          (fun i _ => (exp_pos _).le) (mem_univ k)) hN_pos.le
    have hlog := log_le_log (div_pos (exp_pos _) hN_pos) hsingle
    rw [log_div (exp_pos _).ne' hN_pos.ne', log_exp] at hlog
    have hcalc : (-cumLoss ℓ T k - L / η_last) * η_last = -(η_last * cumLoss ℓ T k) - L := by
      rw [sub_mul, div_mul_cancel₀ _ hη_last.ne']
      ring
    linarith
  -- Bound `L / η_last = √(T * L)` and `∑_{t < T} η_t ≤ 2 * √(T * L)`:
  have hlast_eq : L / η_last = √(T * L) := by
    have hsub1 : ((T - 1 : ℕ) : ℝ) + 1 = T := by exact_mod_cast Nat.sub_add_cancel hT0
    have hsL : 0 < √L := sqrt_pos.mpr hL
    have hsT : 0 < √(T : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hT0)
    calc L / η_last = (√L * √L) / (√L / √(T : ℝ)) := by
          dsimp only [η_last, anytimeStep]
          rw [hsub1, sqrt_div hL.le, mul_self_sqrt hL.le]
      _ = √(T : ℝ) * √L := by field_simp
      _ = √(T * L) := (sqrt_mul (Nat.cast_nonneg T) L).symm
  have hsum_η : ∑ t ∈ range T, anytimeStep N t ≤ 2 * √(T * L) := by
    have heq : ∀ t, anytimeStep N t = √L * (1 / √((t : ℝ) + 1)) := fun t => by
      unfold anytimeStep
      rw [sqrt_div hL.le, mul_one_div]
    simp_rw [heq, ← mul_sum]
    have hinv := sum_inv_sqrt_succ_le T
    calc √L * ∑ t ∈ range T, (1 / √((t : ℝ) + 1))
        ≤ √L * (2 * √(T : ℝ)) := mul_le_mul_of_nonneg_left hinv (sqrt_nonneg L)
      _ = 2 * (√(T : ℝ) * √L) := by ring
      _ = 2 * √(T * L) := by rw [← sqrt_mul (Nat.cast_nonneg T)]
  rw [sum_add_distrib, sum_neg_distrib] at hT_pot
  linarith

/-! ### Exercise 4.8: Weight on `ε`-dominated actions -/

omit [Fintype ι] in
private theorem weight_rwmFactor_eq {η : ℝ} (hη : η < 1) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    weight (rwmFactor η) ℓ t i = (1 - η) ^ cumLoss ℓ t i := by
  have h1η : 0 < 1 - η := by linarith
  induction t with
  | zero => simp [weight_zero]
  | succ t ih =>
    rw [weight_succ, ih, cumLoss_succ, rwmFactor_apply, ← rpow_add h1η]

private theorem sum_geom_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    ∑ t ∈ range T, r ^ t ≤ 1 / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  have hmul : (1 - r) * ∑ t ∈ range T, r ^ t = 1 - r ^ T := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, mul_add, ih]
      ring
  have hpow : 0 ≤ r ^ T := pow_nonneg hr0 T
  rw [le_div_iff₀ h1r, mul_comm, hmul]
  linarith

/-- **Exponential decay of RWM weight on a mixed-strategy `ε`-dominated action**
[BlumMansour2007AGT, Exercise 4.8, p. 101]: if `0 ≤ η < 1`, `ε ≥ 0`, and action `j` has per-round
loss at least `ε` above the fixed mixed action `y` (`∑ i, y i * ℓ s i + ε ≤ ℓ s j`) in all rounds
`s < t`, then `prob (rwmFactor η) ℓ t j ≤ (1 - η) ^ ((t : ℝ) * ε)`. -/
theorem rwm_prob_le_of_dominated_mixed {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} {j : ι} {y : ι → ℝ} (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hdom : ∀ s < t, ∑ i, y i * ℓ s i + ε ≤ ℓ s j) :
    prob (rwmFactor η) ℓ t j ≤ (1 - η) ^ ((t : ℝ) * ε) := by
  have : Nonempty ι := ⟨j⟩
  have h1η : 0 < 1 - η := by linarith
  have h1η_le : 1 - η ≤ 1 := by linarith
  have hφ : ∀ s < t, ∀ i, 0 < rwmFactor η (ℓ s i) := fun _ _ _ => by
    rw [rwmFactor_apply]; exact rpow_pos_of_pos h1η _
  obtain ⟨k, hk⟩ := exists_cumLoss_eq_minCumLoss ℓ t
  have hcum_dom : cumLoss ℓ t k + (t : ℝ) * ε ≤ cumLoss ℓ t j := by
    have hsum : ∑ s ∈ range t, (∑ i, y i * ℓ s i + ε) ≤ cumLoss ℓ t j :=
      sum_le_sum fun s hs => hdom s (mem_range.mp hs)
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm] at hsum
    have hy_sum : ∑ i, ∑ s ∈ range t, y i * ℓ s i = ∑ i, y i * cumLoss ℓ t i :=
      sum_congr rfl fun i _ => by rw [← mul_sum]; rfl
    have hmin_le : cumLoss ℓ t k ≤ ∑ i, y i * cumLoss ℓ t i := by
      calc cumLoss ℓ t k = ∑ i, y i * cumLoss ℓ t k := by rw [← sum_mul, hy1, one_mul]
        _ ≤ ∑ i, y i * cumLoss ℓ t i := sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (by rw [hk]; exact minCumLoss_le ℓ t i) (hy0 i)
    linarith
  have hwk_pos : 0 < weight (rwmFactor η) ℓ t k := weight_pos hφ k
  have hwk_le : weight (rwmFactor η) ℓ t k ≤ potential (rwmFactor η) ℓ t :=
    single_le_sum (fun i _ => (weight_pos hφ i).le) (mem_univ k)
  calc prob (rwmFactor η) ℓ t j
      = weight (rwmFactor η) ℓ t j / potential (rwmFactor η) ℓ t := rfl
    _ ≤ weight (rwmFactor η) ℓ t j / weight (rwmFactor η) ℓ t k :=
        div_le_div_of_nonneg_left (weight_pos hφ j).le hwk_pos hwk_le
    _ = (1 - η) ^ (cumLoss ℓ t j - cumLoss ℓ t k) := by
        rw [weight_rwmFactor_eq hη1, weight_rwmFactor_eq hη1, rpow_sub h1η]
    _ ≤ (1 - η) ^ ((t : ℝ) * ε) :=
        rpow_le_rpow_of_exponent_ge h1η h1η_le (by linarith)

/-- **Total cumulative RWM weight on a mixed-strategy `ε`-dominated action**
[BlumMansour2007AGT, Exercise 4.8, p. 101]: for `0 < η < 1` and `ε ∈ (0, 1]`, the summed
probability assigned to action `j` over *any* horizon `T` is at most `1 / (η * ε)`. -/
theorem rwm_sum_prob_le_of_dominated_mixed {η ε : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {ℓ : ℕ → ι → ℝ} {T : ℕ} {j : ι} {y : ι → ℝ}
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hdom : ∀ s < T, ∑ i, y i * ℓ s i + ε ≤ ℓ s j) :
    ∑ t ∈ range T, prob (rwmFactor η) ℓ t j ≤ 1 / (η * ε) := by
  have h1η : 0 < 1 - η := by linarith
  have hbase : (1 - η) ^ ε ≤ 1 - η * ε := by
    simpa [rwmFactor_apply] using rwmFactor_le_mwFactor hη1 ⟨hε0.le, hε1⟩
  have hstep : ∀ t ∈ range T, prob (rwmFactor η) ℓ t j ≤ (1 - η * ε) ^ t := fun t ht => by
    have hlt := mem_range.mp ht
    calc prob (rwmFactor η) ℓ t j
        ≤ (1 - η) ^ ((t : ℝ) * ε) :=
          rwm_prob_le_of_dominated_mixed hη0.le hη1 hy0 hy1 fun s hs => hdom s (by omega)
      _ = ((1 - η) ^ ε) ^ t := by
          rw [mul_comm, rpow_mul h1η.le, rpow_natCast]
      _ ≤ (1 - η * ε) ^ t := pow_le_pow_left₀ (rpow_nonneg h1η.le ε) hbase t
  have hηε_lt : η * ε < 1 := by nlinarith
  have hsum := sum_geom_le_inv (r := 1 - η * ε) (by linarith) (by linarith [mul_pos hη0 hε0]) T
  have hrew : 1 - (1 - η * ε) = η * ε := by ring
  rw [hrew] at hsum
  exact (sum_le_sum hstep).trans hsum

/-- **Exponential decay of Polynomial Weights (`mwFactor`) on an `ε`-dominated action**
[BlumMansour2007AGT, Exercise 4.8, p. 101]: if `0 < η`, `0 ≤ ε`, and in every round `s < t` the
losses lie in `[0, ∞)` with `η * ℓ s j < 1` and `ℓ s k + ε ≤ ℓ s j`, then
`prob (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t`. -/
theorem mw_prob_le_of_dominated {η ε : ℝ} (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} {j k : ι}
    (hpos : ∀ s < t, ∀ i, 0 < mwFactor η (ℓ s i))
    (hk0 : ∀ s < t, 0 ≤ ℓ s k) (hdom : ∀ s < t, ℓ s k + ε ≤ ℓ s j) :
    prob (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t := by
  have hwk_pos : 0 < weight (mwFactor η) ℓ t k := weight_pos hpos k
  have hwk_le : weight (mwFactor η) ℓ t k ≤ potential (mwFactor η) ℓ t :=
    single_le_sum (fun i _ => (weight_pos hpos i).le) (mem_univ k)
  have hprod : weight (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t * weight (mwFactor η) ℓ t k := by
    induction t with
    | zero => simp [weight_zero]
    | succ s ih =>
      rw [weight_succ, weight_succ, pow_succ]
      have hsub := ih (fun u hu i => hpos u (by omega) i) (fun u hu => hk0 u (by omega))
        (fun u hu => hdom u (by omega))
      have hfactor : mwFactor η (ℓ s j) ≤ (1 - η * ε) * mwFactor η (ℓ s k) := by
        simp only [mwFactor_apply]
        have hd := hdom s (by omega)
        have hk := hk0 s (by omega)
        nlinarith [mul_nonneg hη0 hε0, mul_nonneg (sq_nonneg η) (mul_nonneg hε0 hk)]
      have hpos_f : 0 < mwFactor η (ℓ s k) := hpos s (by omega) k
      have h1ηε : 0 ≤ 1 - η * ε :=
        nonneg_of_mul_nonneg_left (le_trans (hpos s (by omega) j).le hfactor) hpos_f
      have hmul := mul_le_mul hsub hfactor (hpos s (by omega) j).le
        (mul_nonneg (pow_nonneg h1ηε s)
          (weight_pos (fun u hu i => hpos u (by omega) i) k).le)
      linarith [show (1 - η * ε) ^ s * weight (mwFactor η) ℓ s k *
          ((1 - η * ε) * mwFactor η (ℓ s k)) =
          (1 - η * ε) ^ s * (1 - η * ε) * (weight (mwFactor η) ℓ s k * mwFactor η (ℓ s k)) by
        ring]
  calc prob (mwFactor η) ℓ t j
      = weight (mwFactor η) ℓ t j / potential (mwFactor η) ℓ t := rfl
    _ ≤ weight (mwFactor η) ℓ t j / weight (mwFactor η) ℓ t k :=
        div_le_div_of_nonneg_left (weight_pos hpos j).le hwk_pos hwk_le
    _ ≤ (1 - η * ε) ^ t := by
        rw [div_le_iff₀ hwk_pos]
        exact hprod

/-- **Total cumulative Polynomial Weights weight on an `ε`-dominated action**
[BlumMansour2007AGT, Exercise 4.8, p. 101]: summing `mw_prob_le_of_dominated` gives total mass at
most `1 / (η * ε)` over *any* horizon `T`. -/
theorem mw_sum_prob_le_of_dominated {η ε : ℝ} (hη0 : 0 < η) (hε0 : 0 < ε) (hηε : η * ε ≤ 1)
    {ℓ : ℕ → ι → ℝ} {T : ℕ} {j k : ι}
    (hpos : ∀ s < T, ∀ i, 0 < mwFactor η (ℓ s i))
    (hk0 : ∀ s < T, 0 ≤ ℓ s k) (hdom : ∀ s < T, ℓ s k + ε ≤ ℓ s j) :
    ∑ t ∈ range T, prob (mwFactor η) ℓ t j ≤ 1 / (η * ε) := by
  have hstep : ∀ t ∈ range T, prob (mwFactor η) ℓ t j ≤ (1 - η * ε) ^ t := fun t ht => by
    have hlt := mem_range.mp ht
    exact mw_prob_le_of_dominated hη0.le hε0.le
      (fun s hs i => hpos s (by omega) i) (fun s hs => hk0 s (by omega))
      (fun s hs => hdom s (by omega))
  have hsum := sum_geom_le_inv (r := 1 - η * ε) (by linarith) (by linarith [mul_pos hη0 hε0]) T
  have hrew : 1 - (1 - η * ε) = η * ε := by ring
  rw [hrew] at hsum
  exact (sum_le_sum hstep).trans hsum

/-- **Low external regret does not prevent high weight on an `ε`-dominated action**
[BlumMansour2007AGT, Exercise 4.8, p. 101]: for every `ε ∈ [0, 1 / 2]` and `m : ℕ`, over
`T = 2 * m` rounds on `Fin 3`, there exist `[0, 1]`-valued losses `ℓ` in which action `2` is
`ε`-strictly dominated by action `0` in *every* round (`ℓ t 2 = ℓ t 0 + ε`), and deterministic
plays `p` with **nonpositive** external regret (`∑ t < 2 * m, ⟨p t, ℓ t⟩ ≤ minCumLoss ℓ (2 * m)`)
that place time-average weight `1 / 2` (`∑ t < 2 * m, p t 2 = m`) on action `2`. -/
theorem exists_low_external_regret_dominated_weight {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (m : ℕ) :
    ∃ (p ℓ : ℕ → Fin 3 → ℝ),
      (∀ t, (∀ i, p t i = 0 ∨ p t i = 1) ∧ ∑ i, p t i = 1) ∧
      (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, ℓ t 0 + ε ≤ ℓ t 2) ∧
      ∑ t ∈ range (2 * m), ∑ i, p t i * ℓ t i ≤ minCumLoss ℓ (2 * m) ∧
      ∑ t ∈ range (2 * m), p t 2 = m := by
  let ℓ : ℕ → Fin 3 → ℝ := fun t i =>
    if t % 2 = 0 then
      if i = 0 then 0 else if i = 1 then 1 else ε
    else
      if i = 0 then 1 - ε else if i = 1 then 0 else 1
  let p : ℕ → Fin 3 → ℝ := fun t i =>
    if t % 2 = 0 then (if i = 2 then 1 else 0) else (if i = 1 then 1 else 0)
  have hpair : ∀ (f : ℕ → ℝ) (a b : ℝ),
      (∀ k, f (2 * k) = a) → (∀ k, f (2 * k + 1) = b) →
      ∑ t ∈ range (2 * m), f t = (m : ℝ) * (a + b) := fun f a b ha hb => by
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
        ha k, hb k]
      push_cast
      ring
  refine ⟨p, ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    refine ⟨fun i => by dsimp only [p]; split_ifs <;> simp, ?_⟩
    by_cases he : t % 2 = 0 <;> simp [p, he]
  · intro t i
    dsimp only [ℓ]
    split_ifs <;> exact ⟨by linarith, by linarith⟩
  · intro t
    by_cases he : t % 2 = 0
    · simp only [ℓ, he, ↓reduceIte, show (0 : Fin 3) = 0 from rfl,
        show ¬ (2 : Fin 3) = 0 by decide, show ¬ (2 : Fin 3) = 1 by decide]
      linarith
    · simp only [ℓ, he, ↓reduceIte, show (0 : Fin 3) = 0 from rfl,
        show ¬ (2 : Fin 3) = 0 by decide, show ¬ (2 : Fin 3) = 1 by decide]
      linarith
  · have hloss : ∑ t ∈ range (2 * m), ∑ i : Fin 3, p t i * ℓ t i = (m : ℝ) * (ε + 0) :=
      hpair _ ε 0
        (fun k => by simp [p, ℓ, Fin.sum_univ_three])
        (fun k => by simp [p, ℓ, Fin.sum_univ_three])
    have h0_odd : ∀ k : ℕ, (2 * k + 1) % 2 = 1 := fun k => by omega
    have hc0 : cumLoss ℓ (2 * m) 0 = (m : ℝ) * (0 + (1 - ε)) :=
      hpair (fun t => ℓ t 0) 0 (1 - ε)
        (fun k => by simp [ℓ])
        (fun k => by simp [ℓ, h0_odd k])
    have hc1 : cumLoss ℓ (2 * m) 1 = (m : ℝ) * (1 + 0) :=
      hpair (fun t => ℓ t 1) 1 0
        (fun k => by simp [ℓ])
        (fun k => by simp [ℓ, h0_odd k])
    have hc2 : cumLoss ℓ (2 * m) 2 = (m : ℝ) * (ε + 1) :=
      hpair (fun t => ℓ t 2) ε 1
        (fun k => by simp [ℓ])
        (fun k => by simp [ℓ, h0_odd k])
    rw [hloss]
    refine le_minCumLoss_iff.mpr fun i => ?_
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases show i = 0 ∨ i = 1 ∨ i = 2 by omega with rfl | rfl | rfl
    · rw [hc0]; nlinarith
    · rw [hc1]; nlinarith
    · rw [hc2]; nlinarith
  · have hw := hpair (fun t => p t 2) 1 0
      (fun k => by simp [p])
      (fun k => by
        have hodd : (2 * k + 1) % 2 = 1 := by omega
        simp [p, hodd])
    linarith

end Cslib.MachineLearning.OnlineLearning.Experts
