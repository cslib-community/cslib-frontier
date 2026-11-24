/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Partial-information (multi-armed bandit) reduction from full-information learning

This module formalizes the generic block-exploration reduction from the adversarial
partial-information (multi-armed bandit, MAB) model to the full-information (experts) model of
[BlumMansour2007AGT, §4.6, Theorem 4.17, pp. 94–96].

Given `N` actions (`ι`), a horizon `T`, `K` blocks of length `m` (`K * m ≤ T`, `N ≤ m`), and a
causal full-information algorithm `H` (`IsOnlineAlg H`) with external regret bound `R_K` over `K`
rounds on `[0, 1]` loss vectors, the bandit reduction partitions `[0, K * m)` into `K` blocks
`B_τ = {τ * m, …, τ * m + m - 1}`. In each block `τ`:

* Every action `i : ι` is assigned a collision-free exploration offset `time (ω τ) i : Fin m`
  whose marginal distribution under the uniform average over `ω τ : Ω` is uniform on `Fin m`
  (`ExplorationSchedule`).
* At exploration step `t = τ * m + time (ω τ) i`, the algorithm plays action `i` deterministically,
  observes *only* the loss `ℓ t i` of the played arm, and records `ĉ_i^τ := ℓ t i`
  (`exploredLoss`).
* At the remaining `m - N` exploitation steps of block `τ`, the algorithm plays the distribution
  `H (exploredLoss sched ω ℓ) τ`, which depends only on the single-arm losses observed during the
  earlier blocks `σ < τ` (`mabPlay_bandit_congr`).
* On any leftover tail rounds `t ∈ [K * m, T)` (`T - K * m < K` when `m = T / K`), the algorithm
  plays the uniform distribution on `ι`, avoiding any divisibility requirement `K ∣ T`.

## Overview and source mapping

* **Block-averaged full-information reduction** (`blockAvgLoss`, `blockFullInfo`,
  `blockFullInfo_loss_eq`, `blockFullInfo_loss_le` — [BlumMansour2007AGT, §4.6, p. 94]):
  Over `K` blocks of length `m`, playing `p^τ = H (blockAvgLoss m ℓ) τ` throughout each block has
  total loss `m * ∑ τ, ⟨p^τ, c^τ⟩ ≤ minCumLoss ℓ (K * m) + m * R_K`.
* **Collision-free exploration schedules** (`ExplorationSchedule`, `cyclicExplorationSchedule`,
  `uniformInjExplorationSchedule` — [BlumMansour2007AGT, §4.6, p. 95]):
  Two canonical schedules for any `N ≤ m`:
  - `uniformInjExplorationSchedule` averages uniformly over all embeddings `ι ↪ Fin m` (the literal
    random collision-free subset without replacement described on p. 95).
  - `cyclicExplorationSchedule` fixes one embedding `e : ι ↪ Fin m` and applies a single uniform
    cyclic shift `s : Fin m`, using only `m` outcomes per block.
* **Unbiased exploration feedback and decoupling** (`exploredLoss`, `expect_exploredLoss_eq`,
  `expect_online_mul_exploredLoss_eq`, `expect_minCumLoss_exploredLoss_le` —
  [BlumMansour2007AGT, §4.6, eq. (4.2), p. 95]):
  Because `H` is causal, `p^τ` is independent of the round-`τ` randomness `ω τ`, so
  `𝔼_ω[⟨p^τ, ĉ^τ⟩] = 𝔼_ω[⟨p^τ, c^τ⟩]` (`expect_online_mul_exploredLoss_eq`), and Jensen's
  inequality for `min` gives `𝔼_ω[min_i Ĉ_i^K] ≤ min_i C_i^K`
  (`expect_minCumLoss_exploredLoss_le`).
* **Generic block reduction** (`mabPlay`, `mabPlay_bandit_congr`, `mabPlay_expected_loss_le_mul`,
  `mabPlay_expected_loss_le` — [BlumMansour2007AGT, §4.6, p. 95]):
  For exact horizon `T = K * m`, `𝔼_ω[L_MAB^{K m}] ≤ L_min^{K m} + N * K + m * R_K`. For arbitrary
  `T` with `K * m ≤ T`, `𝔼_ω[L_MAB^T] ≤ L_min^T + N * K + (T - K * m) + m * R_K`.
* **Theorem 4.17 tunings and instantiations** (`optBlockCount`, `optBlockLen`,
  `mabPlay_expected_loss_le_optimal`, `bookBlockCount`, `bookBlockLen`,
  `mabPlay_expected_loss_le_book`, `mabRWM_expected_loss_le`, `mabAnytimeHedge_expected_loss_le` —
  [BlumMansour2007AGT, §4.6, Theorem 4.17, p. 96]):
  - Balanced choice `K = ⌊(T / N)^{2/3} (ln N)^{1/3}⌋` (`optBlockCount`, matching the two error
    terms `N K` and `T √(ln N / K)`) gives the sharp `O(T^{2/3} (N ln N)^{1/3})` bound with
    explicit constant `3 / 2 + C √2` for *every* `N ≥ 2` and *every* `T : ℕ` (including small
    `T < 2 N ln N`, where uniform play already satisfies `T ≤ (3 / 2) T^{2/3} (N ln N)^{1/3}`).
  - Instantiating with horizon-tuned Randomized Weighted Majority (`rwm_loss_le_tunedStep`,
    `C = 2`) yields explicit regret bound `(9 / 2) T^{2/3} (N ln N)^{1/3}`
    (`mabRWM_expected_loss_le`); instantiating with horizon-free `anytimeHedgeProb` (`C = 3`)
    yields `6 T^{2/3} (N ln N)^{1/3}` (`mabAnytimeHedge_expected_loss_le`).
  - The textbook tuning `K = ⌊(T / N)^{2/3}⌋` (`bookBlockCount`, [BlumMansour2007AGT, p. 96]) gives
    `(3 / 2 + C √2 √(ln N)) T^{2/3} N^{1/3}` for all `T ≥ N ≥ 2`
    (`mabPlay_expected_loss_le_book`), strictly improving the `ln N` factor printed in the source's
    Theorem 4.17 display to `√(ln N)` (and matching `O(T^{2/3} N^{1/3} ln N)` via
    `mabPlay_expected_loss_le_book_log`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.blockAvgLoss`: block-average loss vector `c^τ`.
* `Cslib.MachineLearning.OnlineLearning.Experts.blockFullInfo`: full-information algorithm running
  constant strategies across blocks (`FIB`).
* `Cslib.MachineLearning.OnlineLearning.Experts.ExplorationSchedule`: collision-free block
  exploration schedule with uniform marginal exploration times.
* `Cslib.MachineLearning.OnlineLearning.Experts.cyclicExplorationSchedule`: cyclic-shift schedule
  on `Fin m`.
* `Cslib.MachineLearning.OnlineLearning.Experts.uniformInjExplorationSchedule`: uniform schedule
  over all injections `ι ↪ Fin m`.
* `Cslib.MachineLearning.OnlineLearning.Experts.exploredLoss`: single-arm bandit estimate `ĉ^τ`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay`: the partial-information block-exploration
  reduction learner (`MAB`).
* `Cslib.MachineLearning.OnlineLearning.Experts.optBlockCount`,
  `Cslib.MachineLearning.OnlineLearning.Experts.optBlockLen`: balanced block count `K` and block
  length `m` for `O(T^{2/3} (N ln N)^{1/3})`.
* `Cslib.MachineLearning.OnlineLearning.Experts.bookBlockCount`,
  `Cslib.MachineLearning.OnlineLearning.Experts.bookBlockLen`: textbook block count
  `⌊(T / N)^{2/3}⌋` and length `⌊T / K⌋`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.isOnlineAlg_rwm`: causality of
  `prob (rwmFactor η)` for `η < 1`.
* `Cslib.MachineLearning.OnlineLearning.Experts.blockFullInfo_loss_le`: full-information block
  regret bound `L_FIB^{K m} ≤ L_min^{K m} + m R_K` ([BlumMansour2007AGT, §4.6, p. 94]).
* `Cslib.MachineLearning.OnlineLearning.Experts.expect_exploredLoss_eq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.expect_online_mul_exploredLoss_eq`: unbiasedness
  and decoupling identity ([BlumMansour2007AGT, §4.6, eq. (4.2), p. 95]).
* `Cslib.MachineLearning.OnlineLearning.Experts.expect_minCumLoss_exploredLoss_le`:
  `𝔼[min_i Ĉ_i^K] ≤ min_i C_i^K`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_bandit_congr`: partial-information feedback
  invariance of `mabPlay`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_mul`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le`: general block-reduction
  expected-loss bounds ([BlumMansour2007AGT, §4.6, p. 95]).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_optimal`:
  `O(T^{2/3} (N ln N)^{1/3})` black-box bandit reduction ([BlumMansour2007AGT, Theorem 4.17]).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_book`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_book_log`:
  [BlumMansour2007AGT, Theorem 4.17] with textbook block count `K = ⌊(T / N)^{2/3}⌋`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabRWM_expected_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mabAnytimeHedge_expected_loss_le`: explicit
  instantiations using horizon-tuned RWM (`9 / 2`) and anytime Hedge (`6`).

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ### Causality of Randomized Weighted Majority -/

/-- Randomized Weighted Majority `prob (rwmFactor η)` is a causal online algorithm for any
learning rate `η < 1`. -/
theorem isOnlineAlg_rwm [Nonempty ι] {η : ℝ} (hη : η < 1) :
    IsOnlineAlg (prob (rwmFactor η) : (ℕ → ι → ℝ) → ℕ → ι → ℝ) where
  nonneg _ _ i := prob_nonneg (fun _ _ _ => by
    rw [rwmFactor_apply]; exact rpow_pos_of_pos (by linarith) _) i
  sum_eq_one _ _ := sum_prob (fun _ _ _ => by
    rw [rwmFactor_apply]; exact rpow_pos_of_pos (by linarith) _)
  congr h := prob_congr h

/-! ### Block averages and the full-information block learner (`FIB`) -/

private theorem sum_range_mul_eq_sum_block (K m : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ range (K * m), f t = ∑ τ ∈ range K, ∑ r : Fin m, f (τ * m + r.val) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun r => f (K * m + r)) m).symm

/-- Block-average loss vector `c^τ` of block `τ` of length `m` [BlumMansour2007AGT, §4.6, p. 94]:
`c^τ_i = (1 / m) ∑_{r < m} ℓ(τ * m + r, i)`. -/
noncomputable def blockAvgLoss (m : ℕ) (ℓ : ℕ → ι → ℝ) (τ : ℕ) (i : ι) : ℝ :=
  (∑ r : Fin m, ℓ (τ * m + r.val) i) / m

omit [Fintype ι] in
theorem blockAvgLoss_apply (m : ℕ) (ℓ : ℕ → ι → ℝ) (τ : ℕ) (i : ι) :
    blockAvgLoss m ℓ τ i = (∑ r : Fin m, ℓ (τ * m + r.val) i) / m := by rw [blockAvgLoss]

omit [Fintype ι] in
/-- Block-average losses remain in `[0, 1]` when the underlying per-round losses are in `[0, 1]`. -/
theorem blockAvgLoss_mem_Icc {m : ℕ} (hm : 0 < m) {ℓ : ℕ → ι → ℝ} {τ : ℕ} {i : ι}
    (hℓ : ∀ r : Fin m, ℓ (τ * m + r.val) i ∈ Set.Icc (0 : ℝ) 1) :
    blockAvgLoss m ℓ τ i ∈ Set.Icc (0 : ℝ) 1 := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  unfold blockAvgLoss
  constructor
  · exact div_nonneg (sum_nonneg fun r _ => (hℓ r).1) hm_pos.le
  · rw [div_le_one hm_pos]
    calc ∑ r : Fin m, ℓ (τ * m + r.val) i
        ≤ ∑ _r : Fin m, (1 : ℝ) := sum_le_sum fun r _ => (hℓ r).2
      _ = m := by simp

omit [Fintype ι] in
/-- Multiplying the cumulative block-average loss by block length `m` recovers the exact cumulative
loss over `K * m` rounds. -/
theorem mul_cumLoss_blockAvgLoss {m : ℕ} (hm : 0 < m) (ℓ : ℕ → ι → ℝ) (K : ℕ) (i : ι) :
    (m : ℝ) * cumLoss (blockAvgLoss m ℓ) K i = cumLoss ℓ (K * m) i := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [cumLoss, blockAvgLoss, mul_sum]
  rw [sum_range_mul_eq_sum_block K m (fun t => ℓ t i)]
  exact sum_congr rfl fun τ _ => mul_div_cancel₀ _ hm_ne

omit [Fintype ι] in
/-- `blockAvgLoss m ℓ τ` depends only on the losses inside block `τ`. -/
theorem blockAvgLoss_congr {m : ℕ} {ℓ ℓ' : ℕ → ι → ℝ} {τ : ℕ}
    (h : ∀ r : Fin m, ℓ (τ * m + r.val) = ℓ' (τ * m + r.val)) :
    blockAvgLoss m ℓ τ = blockAvgLoss m ℓ' τ := by
  funext i
  simp only [blockAvgLoss]
  congr 1
  exact sum_congr rfl fun r _ => congrFun (h r) i

/-- Multiplying the minimum cumulative block-average loss by `m` recovers `minCumLoss ℓ (K * m)`. -/
theorem mul_minCumLoss_blockAvgLoss [Nonempty ι] {m : ℕ} (hm : 0 < m) (ℓ : ℕ → ι → ℝ) (K : ℕ) :
    (m : ℝ) * minCumLoss (blockAvgLoss m ℓ) K = minCumLoss ℓ (K * m) := by
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  apply le_antisymm
  · obtain ⟨i₀, hi₀⟩ := exists_cumLoss_eq_minCumLoss ℓ (K * m)
    rw [← hi₀, ← mul_cumLoss_blockAvgLoss hm ℓ K i₀]
    exact mul_le_mul_of_nonneg_left (minCumLoss_le (blockAvgLoss m ℓ) K i₀) hm_nn
  · obtain ⟨i₀, hi₀⟩ := exists_cumLoss_eq_minCumLoss (blockAvgLoss m ℓ) K
    rw [← hi₀, mul_cumLoss_blockAvgLoss hm ℓ K i₀]
    exact minCumLoss_le ℓ (K * m) i₀

/-- The full-information block learner `FIB` [BlumMansour2007AGT, §4.6, p. 94]: throughout block
`τ = t / m`, it plays the constant distribution `H (blockAvgLoss m ℓ) τ`. -/
noncomputable def blockFullInfo (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (m : ℕ) (ℓ : ℕ → ι → ℝ)
    (t : ℕ) : ι → ℝ :=
  H (blockAvgLoss m ℓ) (t / m)

/-- `blockFullInfo H m` depends only on earlier completed blocks `s < (t / m) * m`. -/
theorem blockFullInfo_congr {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) {m : ℕ}
    {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t / m * m, ℓ s = ℓ' s) :
    blockFullInfo H m ℓ t = blockFullInfo H m ℓ' t := by
  apply hH.congr
  intro σ hσ
  apply blockAvgLoss_congr
  intro r
  apply h
  have h1 : (σ + 1) * m ≤ t / m * m := Nat.mul_le_mul_right m hσ
  have h2 : σ * m + r.val < (σ + 1) * m := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left r.isLt (σ * m)
  exact lt_of_lt_of_le h2 h1

/-- If `H` is causal then `blockFullInfo H m` is causal. -/
theorem isOnlineAlg_blockFullInfo {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (m : ℕ) :
    IsOnlineAlg (blockFullInfo H m) where
  nonneg ℓ t i := hH.nonneg (blockAvgLoss m ℓ) (t / m) i
  sum_eq_one ℓ t := hH.sum_eq_one (blockAvgLoss m ℓ) (t / m)
  congr h := blockFullInfo_congr hH fun s hs =>
    h s (lt_of_lt_of_le hs (Nat.div_mul_le_self _ m))

/-- Exact total loss of `blockFullInfo H m` over `K` blocks of length `m`
[BlumMansour2007AGT, §4.6, p. 94]: `L_FIB^{K m} = m * ∑ τ < K, ⟨p^τ, c^τ⟩`. -/
theorem blockFullInfo_loss_eq (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) {K m : ℕ} (hm : 0 < m)
    (ℓ : ℕ → ι → ℝ) :
    ∑ t ∈ range (K * m), ∑ i, blockFullInfo H m ℓ t i * ℓ t i =
      (m : ℝ) * ∑ τ ∈ range K, ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [sum_range_mul_eq_sum_block K m, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  have hdiv : ∀ r : Fin m, (τ * m + r.val) / m = τ := fun r => by
    rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_left m τ),
      Nat.mul_div_cancel _ hm, Nat.div_eq_of_lt r.isLt, add_zero]
  calc ∑ r : Fin m, ∑ i, blockFullInfo H m ℓ (τ * m + r.val) i * ℓ (τ * m + r.val) i
      = ∑ r : Fin m, ∑ i, H (blockAvgLoss m ℓ) τ i * ℓ (τ * m + r.val) i := by
        refine sum_congr rfl fun r _ => sum_congr rfl fun i _ => ?_
        simp only [blockFullInfo, hdiv r]
    _ = ∑ i, ∑ r : Fin m, H (blockAvgLoss m ℓ) τ i * ℓ (τ * m + r.val) i := sum_comm
    _ = ∑ i, H (blockAvgLoss m ℓ) τ i * ∑ r : Fin m, ℓ (τ * m + r.val) i :=
        sum_congr rfl fun i _ => (mul_sum _ _ _).symm
    _ = (m : ℝ) * ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        simp only [blockAvgLoss]
        field_simp

/-- Full-information block regret bound [BlumMansour2007AGT, §4.6, p. 94]:
if `H` achieves external regret at most `R` on `blockAvgLoss m ℓ` over `K` blocks, then
`L_FIB^{K m} ≤ minCumLoss ℓ (K * m) + m * R`. -/
theorem blockFullInfo_loss_le [Nonempty ι] {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} {K m : ℕ}
    (hm : 0 < m) {ℓ : ℕ → ι → ℝ} {R : ℝ}
    (hreg : ∀ k : ι,
      ∑ τ ∈ range K, ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i ≤
        cumLoss (blockAvgLoss m ℓ) K k + R) :
    ∑ t ∈ range (K * m), ∑ i, blockFullInfo H m ℓ t i * ℓ t i ≤
      minCumLoss ℓ (K * m) + (m : ℝ) * R := by
  obtain ⟨k₀, hk₀⟩ := exists_cumLoss_eq_minCumLoss (blockAvgLoss m ℓ) K
  have h1 := hreg k₀
  rw [hk₀] at h1
  rw [blockFullInfo_loss_eq H hm ℓ, ← mul_minCumLoss_blockAvgLoss hm ℓ K]
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (m : ℝ) * ∑ τ ∈ range K, ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i
      ≤ (m : ℝ) * (minCumLoss (blockAvgLoss m ℓ) K + R) := mul_le_mul_of_nonneg_left h1 hm_nn
    _ = (m : ℝ) * minCumLoss (blockAvgLoss m ℓ) K + (m : ℝ) * R := mul_add _ _ _

/-! ### Collision-free exploration schedules -/

/-- A collision-free exploration schedule for a finite action space `ι` inside a block of length
`m` [BlumMansour2007AGT, §4.6, p. 95]. Each outcome `ω : Ω` maps the actions injectively to
distinct offsets `time ω : ι ↪ Fin m`, and the marginal distribution of `time ω i` under a uniform
draw `ω : Ω` is uniform on `Fin m`. -/
structure ExplorationSchedule (ι : Type*) (m : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- Pairwise distinct in-block exploration offsets assigned by outcome `ω`. -/
  time : Ω → ι ↪ Fin m
  /-- Uniform marginal: for each action `i`, `time ω i` is uniformly distributed on `Fin m`. -/
  expect_apply : ∀ (i : ι) (f : Fin m → ℝ),
    (𝔼 ω : Ω, f (time ω i)) = (∑ r : Fin m, f r) / m

/-- Given a base embedding `e : ι ↪ Fin m` (`m > 0`), the cyclic-shift exploration schedule draws
a single shift `s : Fin m` uniformly and explores action `i` at offset `e i + s (mod m)`. -/
def cyclicExplorationSchedule {m : ℕ} (hm : 0 < m) (e : ι ↪ Fin m) :
    ExplorationSchedule ι m (Fin m) where
  time s :=
    { toFun := fun i => e i + s
      inj' := fun _ _ h => e.injective (add_right_cancel h) }
  expect_apply i f := by
    have : NeZero m := ⟨hm.ne'⟩
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (e i)) _ _ fun _ => rfl

omit [Fintype ι] in
@[simp] theorem cyclicExplorationSchedule_time {m : ℕ} (hm : 0 < m) (e : ι ↪ Fin m)
    (s : Fin m) (i : ι) :
    (cyclicExplorationSchedule hm e).time s i = e i + s := by
  simp only [cyclicExplorationSchedule]
  rfl

/-- Right-shift permutation of the space `ι ↪ Fin m` adding `s : Fin m` to every offset. -/
private def shiftEmbEquiv {m : ℕ} [NeZero m] (s : Fin m) : (ι ↪ Fin m) ≃ (ι ↪ Fin m) where
  toFun ω :=
    { toFun := fun i => ω i + s
      inj' := fun _ _ h => ω.injective (add_right_cancel h) }
  invFun ω :=
    { toFun := fun i => ω i - s
      inj' := fun _ _ h => ω.injective (sub_left_inj.mp h) }
  left_inv ω := by
    ext i
    exact congrArg Fin.val (add_sub_cancel_right (ω i) s)
  right_inv ω := by
    ext i
    exact congrArg Fin.val (sub_add_cancel (ω i) s)

/-- The literal uniform exploration schedule over *all* collision-free injections `ι ↪ Fin m`
(`|ι| ≤ m`, `0 < m`), matching [BlumMansour2007AGT, §4.6, p. 95]. -/
noncomputable def uniformInjExplorationSchedule [DecidableEq ι] {m : ℕ}
    (hm : 0 < m) (hcard : Fintype.card ι ≤ m) :
    ExplorationSchedule ι m (ι ↪ Fin m) where
  time := id
  expect_apply i f := by
    have : NeZero m := ⟨hm.ne'⟩
    have : Nonempty (ι ↪ Fin m) :=
      ⟨(Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)⟩
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hcard_pos : (0 : ℝ) < Fintype.card (ι ↪ Fin m) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have hshift : ∀ s : Fin m,
        ∑ ω : ι ↪ Fin m, f (ω i) = ∑ ω : ι ↪ Fin m, f (ω i + s) := fun s =>
      (Fintype.sum_equiv (shiftEmbEquiv s) (fun ω => f (ω i + s)) (fun ω => f (ω i))
        fun _ => rfl).symm
    have hmul : (m : ℝ) * ∑ ω : ι ↪ Fin m, f (ω i) =
        (Fintype.card (ι ↪ Fin m) : ℝ) * ∑ r : Fin m, f r := by
      calc (m : ℝ) * ∑ ω : ι ↪ Fin m, f (ω i)
          = ∑ _s : Fin m, ∑ ω : ι ↪ Fin m, f (ω i) := by
            simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ s : Fin m, ∑ ω : ι ↪ Fin m, f (ω i + s) :=
            sum_congr rfl fun s _ => hshift s
        _ = ∑ ω : ι ↪ Fin m, ∑ s : Fin m, f (ω i + s) := sum_comm
        _ = ∑ _ω : ι ↪ Fin m, ∑ r : Fin m, f r :=
            sum_congr rfl fun ω _ =>
              Fintype.sum_equiv (Equiv.addLeft (ω i)) _ _ fun _ => rfl
        _ = (Fintype.card (ι ↪ Fin m) : ℝ) * ∑ r : Fin m, f r := by
            simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [Fintype.expect_eq_sum_div_card]
    dsimp only [id_eq]
    rw [div_eq_div_iff hcard_pos.ne' hm_pos.ne']
    linarith

/-! ### Unbiased exploration feedback `ĉ` and decoupling identity -/

/-- The single-arm exploration loss estimate `ĉ^τ` fed to the full-information base algorithm
[BlumMansour2007AGT, §4.6, p. 95]: for each block `τ < K` and action `i`,
`exploredLoss sched ω ℓ τ i = ℓ (τ * m + time (ω τ) i) i`, which only reads the loss of action `i`
at the single round where action `i` is played. -/
def exploredLoss {m K : ℕ} {Ω : Type*} [Fintype Ω] (sched : ExplorationSchedule ι m Ω)
    (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ) (τ : ℕ) (i : ι) : ℝ :=
  if hτ : τ < K then ℓ (τ * m + (sched.time (ω ⟨τ, hτ⟩) i).val) i else 0

omit [Fintype ι] in
theorem exploredLoss_of_lt {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (sched : ExplorationSchedule ι m Ω) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ)
    {τ : ℕ} (hτ : τ < K) (i : ι) :
    exploredLoss sched ω ℓ τ i = ℓ (τ * m + (sched.time (ω ⟨τ, hτ⟩) i).val) i := by
  simp only [exploredLoss, hτ, ↓reduceDIte]

omit [Fintype ι] in
/-- For `[0, 1]`-valued losses on `[0, K * m)`, every explored loss estimate lies in `[0, 1]`. -/
theorem exploredLoss_mem_Icc {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (sched : ExplorationSchedule ι m Ω) (ω : Fin K → Ω) {ℓ : ℕ → ι → ℝ}
    (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {τ : ℕ} (hτ : τ < K) (i : ι) :
    exploredLoss sched ω ℓ τ i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [exploredLoss_of_lt sched ω ℓ hτ i]
  refine hℓ _ ?_ i
  have h1 : (τ + 1) * m ≤ K * m := Nat.mul_le_mul_right m hτ
  have h2 : τ * m + (sched.time (ω ⟨τ, hτ⟩) i).val < (τ + 1) * m := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left (sched.time (ω ⟨τ, hτ⟩) i).isLt (τ * m)
  exact lt_of_lt_of_le h2 h1

/-- Involution swapping coordinate `τ` of `ω : Fin K → Ω` with an independent draw `x : Ω`. -/
private def swapCoordEquiv {K : ℕ} {Ω : Type*} (τ : Fin K) :
    Equiv.Perm ((Fin K → Ω) × Ω) where
  toFun p := (Function.update p.1 τ p.2, p.1 τ)
  invFun p := (Function.update p.1 τ p.2, p.1 τ)
  left_inv p := by
    rcases p with ⟨ω, x⟩
    ext j
    · simp only [Function.update_idem, Function.update_eq_self]
    · exact Function.update_self τ x ω
  right_inv p := by
    rcases p with ⟨ω, x⟩
    ext j
    · simp only [Function.update_idem, Function.update_eq_self]
    · exact Function.update_self τ x ω

/-- Resampling one coordinate of a uniform product `Fin K → Ω` preserves expectation. -/
private theorem expect_eq_expect_update {K : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (τ : Fin K) (g : (Fin K → Ω) → ℝ) :
    (𝔼 ω : Fin K → Ω, g ω) = 𝔼 ω : Fin K → Ω, 𝔼 x : Ω, g (Function.update ω τ x) := by
  have hsum : ∑ ω : Fin K → Ω, ∑ x : Ω, g (Function.update ω τ x) =
      (Fintype.card Ω : ℝ) * ∑ ω : Fin K → Ω, g ω := by
    calc ∑ ω : Fin K → Ω, ∑ x : Ω, g (Function.update ω τ x)
        = ∑ p : (Fin K → Ω) × Ω, g (swapCoordEquiv τ p).1 := by
          rw [Fintype.sum_prod_type]
          rfl
      _ = ∑ p : (Fin K → Ω) × Ω, g p.1 :=
          Fintype.sum_equiv (swapCoordEquiv τ) _ _ fun _ => rfl
      _ = ∑ ω : Fin K → Ω, ∑ _x : Ω, g ω := Fintype.sum_prod_type _
      _ = (Fintype.card Ω : ℝ) * ∑ ω : Fin K → Ω, g ω := by
          simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  have hcardK : (Fintype.card (Fin K → Ω) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardΩ : (Fintype.card Ω : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← sum_div, hsum]
  field_simp

private theorem expect_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    (𝔼 x : α, c * f x) = c * 𝔼 x : α, f x := by
  simp only [Fintype.expect_eq_sum_div_card, ← mul_sum, mul_div_assoc]

omit [Fintype ι] in
/-- Unbiasedness of `exploredLoss` [BlumMansour2007AGT, §4.6, p. 95]:
for every block `τ < K` and action `i`, `𝔼_ω[ĉ^τ_i] = c^τ_i`. -/
theorem expect_exploredLoss_eq {m K : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι m Ω) (ℓ : ℕ → ι → ℝ) {τ : ℕ} (hτ : τ < K) (i : ι) :
    (𝔼 ω : Fin K → Ω, exploredLoss sched ω ℓ τ i) = blockAvgLoss m ℓ τ i := by
  rw [expect_eq_expect_update ⟨τ, hτ⟩]
  have hinner : ∀ ω : Fin K → Ω,
      (𝔼 x : Ω, exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i) =
        blockAvgLoss m ℓ τ i := fun ω => by
    have heq : (𝔼 x : Ω, exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i) =
        𝔼 x : Ω, ℓ (τ * m + (sched.time x i).val) i := by
      refine expect_congr rfl fun x _ => ?_
      simp only [exploredLoss_of_lt sched _ ℓ hτ i, Function.update_self]
    rw [heq]
    exact sched.expect_apply i (fun r => ℓ (τ * m + r.val) i)
  calc (𝔼 ω : Fin K → Ω, 𝔼 x : Ω, exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i)
      = 𝔼 _ω : Fin K → Ω, blockAvgLoss m ℓ τ i := expect_congr rfl fun ω _ => hinner ω
    _ = blockAvgLoss m ℓ τ i := expect_const univ_nonempty _

/-- **Decoupling identity** [BlumMansour2007AGT, §4.6, eq. (4.2), p. 95]: because `H` is causal,
its round-`τ` distribution depends only on blocks `< τ`, hence is independent of `ω τ`. Therefore
`𝔼_ω[⟨p^τ(ω), ĉ^τ(ω)⟩] = 𝔼_ω[⟨p^τ(ω), c^τ⟩]`. -/
theorem expect_online_mul_exploredLoss_eq {m K : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι m Ω) {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H)
    (ℓ : ℕ → ι → ℝ) {τ : ℕ} (hτ : τ < K) :
    (𝔼 ω : Fin K → Ω,
        ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i) =
      𝔼 ω : Fin K → Ω,
        ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i := by
  rw [expect_eq_expect_update ⟨τ, hτ⟩]
  refine expect_congr rfl fun ω _ => ?_
  have hindep : ∀ x : Ω,
      H (exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ) τ =
        H (exploredLoss sched ω ℓ) τ := fun x => hH.congr fun σ hσ => by
    funext i
    have hσK : σ < K := lt_trans hσ hτ
    have hne : (⟨σ, hσK⟩ : Fin K) ≠ ⟨τ, hτ⟩ := by
      intro h
      exact hσ.ne (congrArg Fin.val h)
    simp only [exploredLoss_of_lt sched _ ℓ hσK i, Function.update_of_ne hne]
  calc (𝔼 x : Ω, ∑ i, H (exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ) τ i *
          exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i)
      = 𝔼 x : Ω, ∑ i, H (exploredLoss sched ω ℓ) τ i *
          ℓ (τ * m + (sched.time x i).val) i := by
        refine expect_congr rfl fun x _ => sum_congr rfl fun i _ => ?_
        rw [hindep x, exploredLoss_of_lt sched _ ℓ hτ i, Function.update_self]
    _ = ∑ i, 𝔼 x : Ω, H (exploredLoss sched ω ℓ) τ i *
          ℓ (τ * m + (sched.time x i).val) i := expect_sum_comm _ _ _
    _ = ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i := by
        refine sum_congr rfl fun i _ => ?_
        rw [expect_const_mul]
        congr 1
        exact sched.expect_apply i (fun r => ℓ (τ * m + r.val) i)

/-- Expected minimum of cumulative explored losses is at most the minimum cumulative true block
average (`𝔼[min_i Ĉ_i^K] ≤ min_i C_i^K`) [BlumMansour2007AGT, §4.6, p. 95]. -/
theorem expect_minCumLoss_exploredLoss_le [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (sched : ExplorationSchedule ι m Ω) (ℓ : ℕ → ι → ℝ) :
    (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K) ≤
      minCumLoss (blockAvgLoss m ℓ) K := by
  refine le_minCumLoss_iff.mpr fun i => ?_
  calc (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K)
      ≤ 𝔼 ω : Fin K → Ω, cumLoss (exploredLoss sched ω ℓ) K i :=
        expect_le_expect fun ω _ => minCumLoss_le (exploredLoss sched ω ℓ) K i
    _ = ∑ τ ∈ range K, 𝔼 ω : Fin K → Ω, exploredLoss sched ω ℓ τ i := by
        simp only [cumLoss]
        exact expect_sum_comm _ _ _
    _ = cumLoss (blockAvgLoss m ℓ) K i := by
        simp only [cumLoss]
        exact sum_congr rfl fun τ hτ => expect_exploredLoss_eq sched ℓ (mem_range.mp hτ) i

/-- Combining the causal decoupling identity with a worst-case external-regret guarantee `R` for
`H` bounds the expected block-average loss `𝔼_ω[C_MAB^K] ≤ C_min^K + R`
[BlumMansour2007AGT, §4.6, p. 95]. -/
theorem expect_sum_online_mul_blockAvgLoss_le [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ cumLoss c K k + R) :
    (𝔼 ω : Fin K → Ω,
        ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i) ≤
      minCumLoss (blockAvgLoss m ℓ) K + R := by
  have hdec : (𝔼 ω : Fin K → Ω,
      ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i) =
      𝔼 ω : Fin K → Ω,
        ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i := by
    rw [expect_sum_comm, expect_sum_comm]
    exact sum_congr rfl fun τ hτ =>
      (expect_online_mul_exploredLoss_eq sched hH ℓ (mem_range.mp hτ)).symm
  rw [hdec]
  have hpt : ∀ ω : Fin K → Ω,
      ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i ≤
        minCumLoss (exploredLoss sched ω ℓ) K + R := fun ω => by
    obtain ⟨k₀, hk₀⟩ := exists_cumLoss_eq_minCumLoss (exploredLoss sched ω ℓ) K
    rw [← hk₀]
    exact hreg (exploredLoss sched ω ℓ)
      (fun τ hτ i => exploredLoss_mem_Icc sched ω hℓ hτ i) k₀
  calc (𝔼 ω : Fin K → Ω, ∑ τ ∈ range K,
          ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i)
      ≤ 𝔼 ω : Fin K → Ω, (minCumLoss (exploredLoss sched ω ℓ) K + R) :=
        expect_le_expect fun ω _ => hpt ω
    _ = (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K) + R := by
        rw [expect_add_distrib, expect_const univ_nonempty]
    _ ≤ minCumLoss (blockAvgLoss m ℓ) K + R := by
        linarith [expect_minCumLoss_exploredLoss_le (K := K) sched ℓ]

/-! ### The explicit partial-information block-exploration learner (`mabPlay`) -/

/-- The partial-information (multi-armed bandit) block-exploration algorithm of
[BlumMansour2007AGT, §4.6, pp. 94–96].

Inside each full block `τ = t / m < K` of length `m > 0`:
* if the in-block offset `r = t % m` equals `sched.time (ω τ) i` for some (unique) action `i : ι`,
  `mabPlay` explores by placing probability `1` on `i`;
* otherwise (`r` is not an exploration time in block `τ`), `mabPlay` exploits by playing
  `H (exploredLoss sched ω ℓ) τ`.

On any leftover tail round `t ≥ K * m`, `mabPlay` plays the uniform distribution on `ι`. -/
noncomputable def mabPlay [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) : ℝ :=
  if hτ : t / m < K then
    if h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩ then
      if j = h.choose then 1 else 0
    else
      H (exploredLoss sched ω ℓ) (t / m) j
  else
    1 / Fintype.card ι

theorem mabPlay_nonneg [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (ω : Fin K → Ω)
    (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    0 ≤ mabPlay hm sched H ω ℓ t j := by
  unfold mabPlay
  by_cases hτ : t / m < K
  · simp only [hτ, ↓reduceDIte]
    by_cases h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩
    · simp only [h, ↓reduceDIte]
      split_ifs <;> norm_num
    · simp only [h, ↓reduceDIte]
      exact hH.nonneg _ _ _
  · simp only [hτ, ↓reduceDIte]
    positivity

theorem sum_mabPlay_eq_one [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (ω : Fin K → Ω)
    (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ j : ι, mabPlay hm sched H ω ℓ t j = 1 := by
  unfold mabPlay
  by_cases hτ : t / m < K
  · simp only [hτ, ↓reduceDIte]
    by_cases h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩
    · simp only [h, ↓reduceDIte, sum_ite_eq', mem_univ, ↓reduceIte]
    · simp only [h, ↓reduceDIte]
      exact hH.sum_eq_one _ _
  · simp only [hτ, ↓reduceDIte]
    have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self hN]

/-- **Partial-information (bandit) feedback invariance**: in round `t`, `mabPlay` depends *only* on
the single-arm losses observed during the earlier blocks' exploration rounds
`(σ * m + time (ω σ) i, i)` for `σ < min (t / m) K`. Changing losses of any unplayed action, any
exploitation round, or any current/future round leaves `mabPlay`'s output unchanged. -/
theorem mabPlay_bandit_congr [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (ω : Fin K → Ω)
    {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ σ : Fin K, σ.val < t / m → ∀ i : ι,
      ℓ (σ.val * m + (sched.time (ω σ) i).val) i =
        ℓ' (σ.val * m + (sched.time (ω σ) i).val) i) :
    mabPlay hm sched H ω ℓ t = mabPlay hm sched H ω ℓ' t := by
  funext j
  unfold mabPlay
  by_cases hτ : t / m < K
  · simp only [hτ, ↓reduceDIte]
    by_cases hex : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩
    · simp only [hex, ↓reduceDIte]
    · simp only [hex, ↓reduceDIte]
      have hcongr : H (exploredLoss sched ω ℓ) (t / m) = H (exploredLoss sched ω ℓ') (t / m) :=
        hH.congr fun σ hσ => by
          funext i
          have hσK : σ < K := lt_trans hσ hτ
          simp only [exploredLoss_of_lt sched ω _ hσK i]
          exact h ⟨σ, hσK⟩ hσ i
      exact congrFun hcongr j
  · simp only [hτ, ↓reduceDIte]

/-- For every fixed exploration seed sequence `ω : Fin K → Ω`, `mabPlay` is a causal online
algorithm. -/
theorem isOnlineAlg_mabPlay [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (ω : Fin K → Ω) :
    IsOnlineAlg (mabPlay hm sched H ω) where
  nonneg := mabPlay_nonneg hm sched hH ω
  sum_eq_one := sum_mabPlay_eq_one hm sched hH ω
  congr {ℓ ℓ' t} h := mabPlay_bandit_congr hm sched hH ω fun σ hσ i => by
    have hlt : σ.val * m + (sched.time (ω σ) i).val < t := by
      have h1 : (σ.val + 1) * m ≤ t / m * m := Nat.mul_le_mul_right m hσ
      have h2 : σ.val * m + (sched.time (ω σ) i).val < (σ.val + 1) * m := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left (sched.time (ω σ) i).isLt (σ.val * m)
      exact lt_of_lt_of_le (lt_of_lt_of_le h2 h1) (Nat.div_mul_le_self t m)
    exact congrFun (h _ hlt) i

/-- At the unique exploration offset assigned to action `i` in block `τ`, `mabPlay` puts mass `1`
on `i` and `0` on every other action. -/
theorem mabPlay_apply_explore [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ)
    (τ : Fin K) (i j : ι) :
    mabPlay hm sched H ω ℓ (τ.val * m + (sched.time (ω τ) i).val) j =
      if j = i then 1 else 0 := by
  have hrlt : (sched.time (ω τ) i).val < m := (sched.time (ω τ) i).isLt
  have hdiv : (τ.val * m + (sched.time (ω τ) i).val) / m = τ.val := by
    rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_left m τ.val),
      Nat.mul_div_cancel _ hm, Nat.div_eq_of_lt hrlt, add_zero]
  have hmod : (τ.val * m + (sched.time (ω τ) i).val) % m = (sched.time (ω τ) i).val := by
    rw [Nat.mul_add_mod_of_lt hrlt]
  unfold mabPlay
  have hτ : (τ.val * m + (sched.time (ω τ) i).val) / m < K := by rw [hdiv]; exact τ.isLt
  have hex : ∃ i' : ι, sched.time (ω ⟨(τ.val * m + (sched.time (ω τ) i).val) / m, hτ⟩) i' =
      ⟨(τ.val * m + (sched.time (ω τ) i).val) % m, Nat.mod_lt _ hm⟩ := by
    refine ⟨i, ?_⟩
    ext
    simp only [hdiv, Fin.eta, hmod]
  simp only [hτ, ↓reduceDIte, hex]
  have huniq : hex.choose = i := by
    have hfin : (⟨(τ.val * m + (sched.time (ω τ) i).val) / m, hτ⟩ : Fin K) = τ :=
      Fin.ext hdiv
    have hr : (⟨(τ.val * m + (sched.time (ω τ) i).val) % m, Nat.mod_lt _ hm⟩ : Fin m) =
        sched.time (ω τ) i := Fin.ext hmod
    have hspec := congrArg Fin.val hex.choose_spec
    have hτeq : (sched.time (ω τ) hex.choose).val = (sched.time (ω τ) i).val := by
      have h1 : ω ⟨(τ.val * m + (sched.time (ω τ) i).val) / m, hτ⟩ = ω τ := congrArg ω hfin
      simpa only [h1, hmod] using hspec
    exact (sched.time (ω τ)).injective (Fin.ext hτeq)
  rw [huniq]

/-- On any non-exploration offset `r` in block `τ`, `mabPlay` plays the base algorithm's
distribution `H (exploredLoss sched ω ℓ) τ`. -/
theorem mabPlay_apply_exploit [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ)
    (τ : Fin K) {r : Fin m} (hr : ∀ i : ι, sched.time (ω τ) i ≠ r) (j : ι) :
    mabPlay hm sched H ω ℓ (τ.val * m + r.val) j = H (exploredLoss sched ω ℓ) τ.val j := by
  have hdiv : (τ.val * m + r.val) / m = τ.val := by
    rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_left m τ.val),
      Nat.mul_div_cancel _ hm, Nat.div_eq_of_lt r.isLt, add_zero]
  have hmod : (τ.val * m + r.val) % m = r.val := Nat.mul_add_mod_of_lt r.isLt
  unfold mabPlay
  have hτ : (τ.val * m + r.val) / m < K := by rw [hdiv]; exact τ.isLt
  have hnot : ¬ ∃ i : ι, sched.time (ω ⟨(τ.val * m + r.val) / m, hτ⟩) i =
      ⟨(τ.val * m + r.val) % m, Nat.mod_lt _ hm⟩ := by
    rintro ⟨i, hi⟩
    have hfin : (⟨(τ.val * m + r.val) / m, hτ⟩ : Fin K) = τ := Fin.ext hdiv
    have hr' : (⟨(τ.val * m + r.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = r := Fin.ext hmod
    rw [hfin, hr'] at hi
    exact hr i hi
  rw [dite_eq_left_of_eq_true (eq_true hτ), dite_eq_right_of_eq_false (eq_false hnot), hdiv]

/-- Per-block expected loss bound: for every fixed `ω` and block `τ`, `mabPlay` pays at most `N`
on its `N` exploration rounds plus the total block loss `m * ⟨p^τ, c^τ⟩` of `p^τ`. -/
private theorem mabPlay_block_loss_le [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) (ω : Fin K → Ω)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (τ : Fin K) :
    ∑ r : Fin m, ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (Fintype.card ι : ℝ) +
        (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
  classical
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  set E : Finset (Fin m) := univ.image (sched.time (ω τ))
  have hlt_Km : ∀ r : Fin m, τ.val * m + r.val < K * m := fun r => by
    have h1 : (τ.val + 1) * m ≤ K * m := Nat.mul_le_mul_right m τ.isLt
    have h2 : τ.val * m + r.val < (τ.val + 1) * m := by
      rw [Nat.add_mul, one_mul]
      exact Nat.add_lt_add_left r.isLt (τ.val * m)
    exact lt_of_lt_of_le h2 h1
  have hexplore_step : ∀ r ∈ E,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤ 1 := by
    intro r _
    calc ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j
        ≤ ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * 1 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (hℓ _ (hlt_Km r) j).2 (mabPlay_nonneg hm sched hH ω ℓ _ j)
      _ = 1 := by simp only [mul_one, sum_mabPlay_eq_one hm sched hH ω]
  have hcardE : E.card = Fintype.card ι := by
    rw [card_image_of_injective _ (sched.time (ω τ)).injective, card_univ]
  have hsplit : ∑ r : Fin m,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j =
      (∑ r ∈ E,
        ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j) +
      (∑ r ∈ univ \ E,
        ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j) := by
    rw [← sum_sdiff (subset_univ E), add_comm]
  have hE_le : ∑ r ∈ E,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (Fintype.card ι : ℝ) := by
    calc ∑ r ∈ E, ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j
        ≤ ∑ _r ∈ E, (1 : ℝ) := sum_le_sum hexplore_step
      _ = (Fintype.card ι : ℝ) := by simp only [sum_const, nsmul_eq_mul, mul_one, hcardE]
  have hEc_le : ∑ r ∈ univ \ E,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
    have hrew : ∑ r ∈ univ \ E,
        ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j =
        ∑ r ∈ univ \ E,
          ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ℓ (τ.val * m + r.val) j := by
      refine sum_congr rfl fun r hr => sum_congr rfl fun j _ => ?_
      have hnotE : r ∉ E := (mem_sdiff.mp hr).2
      have hne : ∀ i : ι, sched.time (ω τ) i ≠ r := fun i hi =>
        hnotE (mem_image.mpr ⟨i, mem_univ i, hi⟩)
      rw [mabPlay_apply_exploit hm sched H ω ℓ τ hne j]
    rw [hrew]
    calc ∑ r ∈ univ \ E,
          ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ℓ (τ.val * m + r.val) j
        ≤ ∑ r : Fin m,
          ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ℓ (τ.val * m + r.val) j :=
          sum_le_sum_of_subset_of_nonneg (sdiff_subset) fun r _ _ =>
            sum_nonneg fun j _ => mul_nonneg (hH.nonneg _ _ _) (hℓ _ (hlt_Km r) j).1
      _ = ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ∑ r : Fin m, ℓ (τ.val * m + r.val) j := by
          rw [sum_comm]
          exact sum_congr rfl fun j _ => (mul_sum _ _ _).symm
      _ = (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          simp only [blockAvgLoss]
          field_simp
  linarith

/-- **Generic block-reduction regret bound (exact multiple `T = K * m`)**
[BlumMansour2007AGT, §4.6, p. 95]:
if `H` is causal and achieves external regret at most `R` over `K` rounds on `[0, 1]` losses, then
`𝔼_ω[L_MAB^{K m}] ≤ L_min^{K m} + N * K + m * R`. -/
theorem mabPlay_expected_loss_le_mul [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ cumLoss c K k + R) :
    (𝔼 ω : Fin K → Ω,
        ∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ (K * m) + (Fintype.card ι : ℝ) * K + (m : ℝ) * R := by
  have hpt : ∀ ω : Fin K → Ω,
      ∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j ≤
        (Fintype.card ι : ℝ) * K +
          (m : ℝ) * ∑ τ ∈ range K,
            ∑ j, H (exploredLoss sched ω ℓ) τ j * blockAvgLoss m ℓ τ j := fun ω => by
    rw [sum_range_mul_eq_sum_block K m, ← Fin.sum_univ_eq_sum_range]
    have hsum : ∑ τ : Fin K,
        ∑ r : Fin m,
          ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
        ∑ τ : Fin K, ((Fintype.card ι : ℝ) +
          (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j) :=
      sum_le_sum fun τ _ => mabPlay_block_loss_le hm sched hH ω hℓ τ
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_sum] at hsum
    have hfin := Fin.sum_univ_eq_sum_range (fun τ =>
      ∑ j, H (exploredLoss sched ω ℓ) τ j * blockAvgLoss m ℓ τ j) K
    rw [hfin, mul_comm (K : ℝ)] at hsum
    exact hsum
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hexp := expect_sum_online_mul_blockAvgLoss_le sched hH hℓ hreg
  calc (𝔼 ω : Fin K → Ω,
          ∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j)
      ≤ 𝔼 ω : Fin K → Ω, ((Fintype.card ι : ℝ) * K +
          (m : ℝ) * ∑ τ ∈ range K,
            ∑ j, H (exploredLoss sched ω ℓ) τ j * blockAvgLoss m ℓ τ j) :=
        expect_le_expect fun ω _ => hpt ω
    _ = (Fintype.card ι : ℝ) * K + (m : ℝ) * 𝔼 ω : Fin K → Ω,
          ∑ τ ∈ range K, ∑ j, H (exploredLoss sched ω ℓ) τ j * blockAvgLoss m ℓ τ j := by
        rw [expect_add_distrib, expect_const univ_nonempty, expect_const_mul]
    _ ≤ (Fintype.card ι : ℝ) * K + (m : ℝ) * (minCumLoss (blockAvgLoss m ℓ) K + R) := by
        gcongr
    _ = minCumLoss ℓ (K * m) + (Fintype.card ι : ℝ) * K + (m : ℝ) * R := by
        rw [mul_add, mul_minCumLoss_blockAvgLoss hm ℓ K]
        ring

/-- **Generic block-reduction regret bound (arbitrary horizon `T ≥ K * m`)**:
adds at most `T - K * m` for the leftover tail rounds after the `K` full blocks of length `m`,
removing the divisibility hypothesis `K ∣ T` from [BlumMansour2007AGT, §4.6, p. 95]. -/
theorem mabPlay_expected_loss_le [DecidableEq ι] [Nonempty ι] {m K T : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (hm : 0 < m) (hKm : K * m ≤ T)
    (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ cumLoss c K k + R) :
    (𝔼 ω : Fin K → Ω,
        ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T + (Fintype.card ι : ℝ) * K + ((T - K * m : ℕ) : ℝ) + (m : ℝ) * R := by
  have hhead_ℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1 := fun t ht i =>
    hℓ t (lt_of_lt_of_le ht hKm) i
  have hsplit : ∀ ω : Fin K → Ω,
      ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j =
        (∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) +
        (∑ r ∈ range (T - K * m),
          ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j) := fun ω => by
    conv_lhs => rw [show T = K * m + (T - K * m) by omega]
    exact sum_range_add _ _ _
  have htail : ∀ ω : Fin K → Ω,
      ∑ r ∈ range (T - K * m),
        ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j ≤
        ((T - K * m : ℕ) : ℝ) := fun ω => by
    calc ∑ r ∈ range (T - K * m),
          ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j
        ≤ ∑ _r ∈ range (T - K * m), (1 : ℝ) := sum_le_sum fun r hr => by
          have hlt : K * m + r < T := by
            have := mem_range.mp hr
            omega
          calc ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j
              ≤ ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * 1 :=
                sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
                  (hℓ _ hlt j).2 (mabPlay_nonneg hm sched hH ω ℓ _ j)
            _ = 1 := by simp only [mul_one, sum_mabPlay_eq_one hm sched hH ω]
      _ = ((T - K * m : ℕ) : ℝ) := by simp
  have hmin_mono : minCumLoss ℓ (K * m) ≤ minCumLoss ℓ T := by
    obtain ⟨k₀, hk₀⟩ := exists_cumLoss_eq_minCumLoss ℓ T
    rw [← hk₀]
    refine (minCumLoss_le ℓ (K * m) k₀).trans ?_
    simp only [cumLoss]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hKm) fun t ht _ =>
      (hℓ t (mem_range.mp ht) k₀).1
  have hmain := mabPlay_expected_loss_le_mul hm sched hH hhead_ℓ hreg
  calc (𝔼 ω : Fin K → Ω, ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j)
      = (𝔼 ω : Fin K → Ω,
          ∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) +
        (𝔼 ω : Fin K → Ω, ∑ r ∈ range (T - K * m),
          ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j) := by
        rw [← expect_add_distrib]
        exact expect_congr rfl fun ω _ => hsplit ω
    _ ≤ (minCumLoss ℓ (K * m) + (Fintype.card ι : ℝ) * K + (m : ℝ) * R) +
        ((T - K * m : ℕ) : ℝ) := by
        refine add_le_add hmain ?_
        calc (𝔼 ω : Fin K → Ω, ∑ r ∈ range (T - K * m),
                ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j)
            ≤ 𝔼 _ω : Fin K → Ω, ((T - K * m : ℕ) : ℝ) :=
              expect_le_expect fun ω _ => htail ω
          _ = ((T - K * m : ℕ) : ℝ) := expect_const univ_nonempty _
    _ ≤ minCumLoss ℓ T + (Fintype.card ι : ℝ) * K + ((T - K * m : ℕ) : ℝ) + (m : ℝ) * R := by
        linarith

/-! ### Block-count tunings and Theorem 4.17 -/

private theorem half_le_natFloor_of_one_le {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases hx2 : x < 2
  · have h1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx)
    linarith
  · have h2 : 2 ≤ x := not_lt.mp hx2
    have hlt := Nat.lt_floor_add_one x
    linarith

private theorem rem_le_half_mul_of_le {N K m T : ℕ} {x B : ℝ} (hN : 2 ≤ N) (hK : 0 < K)
    (hm : m = T / K) (hKx : (K : ℝ) ≤ x) (hNx : (N : ℝ) * x = B) (hB : 0 ≤ B) :
    ((T - K * m : ℕ) : ℝ) ≤ (1 / 2) * B := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hrem_nat : T - K * m < K := by
    rw [hm, show T - K * (T / K) = T % K by have := Nat.div_add_mod T K; omega]
    exact Nat.mod_lt T hK
  calc ((T - K * m : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hrem_nat.le
    _ ≤ x := hKx
    _ = (1 / N) * ((N : ℝ) * x) := by field_simp
    _ ≤ (1 / 2) * B := by
        rw [hNx]
        exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hNr) hB

private theorem mul_sqrt_block_le {K m T : ℕ} {L x : ℝ} (hK : 0 < K) (hKm : K * m ≤ T)
    (hx : 0 < x) (hxK : x / 2 ≤ (K : ℝ)) :
    (m : ℝ) * √((K : ℝ) * L) ≤ √2 * ((T : ℝ) * √L / √x) := by
  have hKr_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hm_le : (m : ℝ) ≤ (T : ℝ) / K := by
    rw [le_div_iff₀ hKr_pos]
    exact_mod_cast (show m * K ≤ T by rw [mul_comm]; exact hKm)
  have hsqrtK : 0 < √(K : ℝ) := sqrt_pos.mpr hKr_pos
  have hinv : 1 / √(K : ℝ) ≤ √2 / √x := by
    rw [div_le_div_iff₀ hsqrtK (sqrt_pos.mpr hx), one_mul]
    calc √x = √(2 * (x / 2)) := by ring_nf
      _ = √2 * √(x / 2) := sqrt_mul (by norm_num) _
      _ ≤ √2 * √(K : ℝ) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hxK) (sqrt_nonneg _)
  calc (m : ℝ) * √((K : ℝ) * L)
      ≤ ((T : ℝ) / K) * (√(K : ℝ) * √L) := by
        rw [← sqrt_mul hKr_pos.le]
        exact mul_le_mul_of_nonneg_right hm_le (sqrt_nonneg _)
    _ = (T : ℝ) * √L * (1 / √(K : ℝ)) := by
        field_simp [hsqrtK.ne']
        rw [sq_sqrt hKr_pos.le]
    _ ≤ (T : ℝ) * √L * (√2 / √x) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = √2 * ((T : ℝ) * √L / √x) := by ring

private theorem rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((2 : ℝ) / 3)) ^ 3 = x ^ 2 := by
  rw [← rpow_natCast, ← rpow_mul hx]
  norm_num

private theorem rpow_one_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← rpow_natCast, ← rpow_mul hx]
  norm_num

/-- Balanced number of blocks `K` for the `O(T^{2/3} (N ln N)^{1/3})` partial-information
reduction: `⌊(T / N)^{2/3} (ln N)^{1/3}⌋` when `2 N ln N ≤ T`, and `0` otherwise (in which case
uniform play over `T` rounds already satisfies `T ≤ (3 / 2) T^{2/3} (N ln N)^{1/3}`). -/
noncomputable def optBlockCount (N T : ℕ) : ℕ :=
  if (2 : ℝ) * N * log N ≤ T then
    ⌊((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3)⌋₊
  else
    0

theorem optBlockCount_eq_zero_of_lt {N T : ℕ} (hT : (T : ℝ) < 2 * N * log N) :
    optBlockCount N T = 0 := by
  have hnot : ¬ (2 : ℝ) * N * log N ≤ T := not_le.mpr hT
  simp only [optBlockCount, hnot, ↓reduceIte]

theorem optBlockCount_eq_floor {N T : ℕ} (hT : (2 : ℝ) * N * log N ≤ T) :
    optBlockCount N T = ⌊((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3)⌋₊ := by
  simp only [optBlockCount, hT, ↓reduceIte]

/-- Block length paired with `optBlockCount N T`: `T / K` when `K > 0`, and `N` when `K = 0` so
that `N ≤ optBlockLen N T` and `optBlockCount N T * optBlockLen N T ≤ T` hold unconditionally. -/
noncomputable def optBlockLen (N T : ℕ) : ℕ :=
  if optBlockCount N T = 0 then N else T / optBlockCount N T

/-- For `N ≥ 2` and `T ≥ 2 N ln N`, the unrounded target `x = (T / N)^{2/3} (ln N)^{1/3}` exceeds
`1`. -/
private theorem one_le_optBlockReal {N T : ℕ} (hN : 2 ≤ N)
    (hT : (2 : ℝ) * N * log N ≤ T) :
    1 ≤ ((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hlog_ge : log 2 ≤ log N :=
    log_le_log (by norm_num) (by exact_mod_cast hN)
  have hL : 0 ≤ log N := le_trans (by norm_num : (0 : ℝ) ≤ 0.6931471803) (hlog2.le.trans hlog_ge)
  have hTN_ge : 2 * log N ≤ (T : ℝ) / N := by
    rw [le_div_iff₀ hNr]
    linarith
  have hnn : 0 ≤ ((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3) := by positivity
  rw [← pow_le_pow_iff_left₀ (by norm_num) hnn (by decide : 3 ≠ 0)]
  rw [one_pow, mul_pow, rpow_two_thirds_cube (div_nonneg (Nat.cast_nonneg T) hNr.le),
    rpow_one_third_cube hL]
  have hsq : (2 * log N) ^ 2 ≤ ((T : ℝ) / N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hTN_ge 2
  have hcube : (1 : ℝ) ≤ 4 * (log N) ^ 3 := by
    have hl : (0.6931471803 : ℝ) < log N := lt_of_lt_of_le hlog2 hlog_ge
    have h3 : (0.6931471803 : ℝ) ^ 3 ≤ (log N) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hl.le 3
    linarith [show (1 : ℝ) ≤ 4 * (0.6931471803 : ℝ) ^ 3 by norm_num]
  have hmul : (2 * log N) ^ 2 * log N ≤ ((T : ℝ) / N) ^ 2 * log N :=
    mul_le_mul_of_nonneg_right hsq hL
  linarith

theorem optBlockCount_pos {N T : ℕ} (hN : 2 ≤ N) (hT : (2 : ℝ) * N * log N ≤ T) :
    0 < optBlockCount N T := by
  simp only [optBlockCount, hT, ↓reduceIte]
  exact Nat.floor_pos.mpr (one_le_optBlockReal hN hT)

theorem optBlockCount_mul_optBlockLen_le (N T : ℕ) :
    optBlockCount N T * optBlockLen N T ≤ T := by
  unfold optBlockLen
  split_ifs with h
  · rw [h, zero_mul]; exact Nat.zero_le T
  · exact Nat.mul_div_le T (optBlockCount N T)

theorem le_optBlockLen {N T : ℕ} (hN : 2 ≤ N) : N ≤ optBlockLen N T := by
  unfold optBlockLen
  split_ifs with h
  · exact le_rfl
  · have hT : (2 : ℝ) * N * log N ≤ T := by
      by_contra hn
      exact h (by simp [optBlockCount, hn])
    have hK_pos : 0 < optBlockCount N T := Nat.pos_of_ne_zero h
    rw [Nat.le_div_iff_mul_le hK_pos]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have hL : 0 < log N := log_pos (by exact_mod_cast hN)
    set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3)
    have hK_le : (optBlockCount N T : ℝ) ≤ x := by
      simp only [optBlockCount, hT, ↓reduceIte]
      exact Nat.floor_le (by positivity)
    have hNx_le : (N : ℝ) * x ≤ T := by
      rw [← pow_le_pow_iff_left₀ (by positivity) hTr (by decide : 3 ≠ 0)]
      rw [mul_pow, show x ^ 3 = ((T : ℝ) / N) ^ 2 * log N by
        dsimp only [x]
        rw [mul_pow, rpow_two_thirds_cube (by positivity), rpow_one_third_cube hL.le]]
      have hcalc : (N : ℝ) ^ 3 * (((T : ℝ) / N) ^ 2 * log N) = (T : ℝ) ^ 2 * ((N : ℝ) * log N) := by
        field_simp
      rw [hcalc]
      nlinarith [sq_nonneg (T : ℝ), hL, hNr]
    have hmul : ((N * optBlockCount N T : ℕ) : ℝ) ≤ T := by
      push_cast
      exact (mul_le_mul_of_nonneg_left hK_le hNr.le).trans hNx_le
    exact_mod_cast hmul

theorem optBlockLen_pos {N T : ℕ} (hN : 2 ≤ N) : 0 < optBlockLen N T :=
  lt_of_lt_of_le (by omega) (le_optBlockLen hN)

/-- **Balanced partial-information regret reduction** (`O(T^{2/3} (N ln N)^{1/3})`, sharp tuning
of [BlumMansour2007AGT, Theorem 4.17, p. 96]): given *any* family `H K` of causal
full-information algorithms on `ι` with external regret at most `C * √(K * ln N)` over `K` rounds
on `[0, 1]` losses, running `mabPlay` with `K = optBlockCount N T`, `m = optBlockLen N T`, and any
`ExplorationSchedule ι m Ω` gives expected loss at most
`minCumLoss ℓ T + (3 / 2 + C * √2) * T^{2/3} * (N * ln N)^{1/3}` for *every* `N ≥ 2` and `T : ℕ`. -/
theorem mabPlay_expected_loss_le_optimal [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (T : ℕ)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι (optBlockLen (Fintype.card ι) T) Ω)
    {H : ℕ → (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : ∀ K, IsOnlineAlg (H K))
    {C : ℝ} (hC : 0 ≤ C)
    (hreg : ∀ K (c : ℕ → ι → ℝ), (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H K c τ i * c τ i ≤
        cumLoss c K k + C * √((K : ℝ) * log (Fintype.card ι)))
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    (𝔼 ω : Fin (optBlockCount (Fintype.card ι) T) → Ω,
        ∑ t ∈ range T,
          ∑ j, mabPlay (optBlockLen_pos hn) sched (H (optBlockCount (Fintype.card ι) T))
            ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (3 / 2 + C * √2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
          ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let N := Fintype.card ι
  let K := optBlockCount N T
  let m := optBlockLen N T
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set B : ℝ := (T : ℝ) ^ ((2 : ℝ) / 3) * ((N : ℝ) * log N) ^ ((1 : ℝ) / 3)
  have hB_nn : 0 ≤ B := by positivity
  by_cases hT : (2 : ℝ) * N * log N ≤ T
  · have hK_pos : 0 < K := optBlockCount_pos hn hT
    have hKr_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK_pos
    have hK_ne : K ≠ 0 := hK_pos.ne'
    have hm_eq : m = T / K := by simp only [m, optBlockLen, K, hK_ne, ↓reduceIte]
    have hKm : K * m ≤ T := optBlockCount_mul_optBlockLen_le N T
    have hbase := mabPlay_expected_loss_le (optBlockLen_pos hn) hKm sched (hH K) hℓ (hreg K)
    set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3) * (log N) ^ ((1 : ℝ) / 3)
    have hx_ge : 1 ≤ x := one_le_optBlockReal hn hT
    have hx_pos : 0 < x := by linarith
    have hK_le_x : (K : ℝ) ≤ x := by
      simp only [K, optBlockCount, hT, ↓reduceIte]
      exact Nat.floor_le hx_pos.le
    have hx_half_le_K : x / 2 ≤ (K : ℝ) := by
      simp only [K, optBlockCount, hT, ↓reduceIte]
      exact half_le_natFloor_of_one_le hx_ge
    have hNx_eq_B : (N : ℝ) * x = B := by
      refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 3 ≠ 0)).mp ?_
      have hx3 : x ^ 3 = ((T : ℝ) / N) ^ 2 * log N := by
        dsimp only [x]
        rw [mul_pow, rpow_two_thirds_cube (by positivity), rpow_one_third_cube hL.le]
      have hB3 : B ^ 3 = (T : ℝ) ^ 2 * ((N : ℝ) * log N) := by
        dsimp only [B]
        rw [mul_pow, rpow_two_thirds_cube hTr, rpow_one_third_cube (by positivity)]
      rw [mul_pow, hx3, hB3]
      field_simp
    have hterm1 : (N : ℝ) * K ≤ B := by
      calc (N : ℝ) * K ≤ (N : ℝ) * x := mul_le_mul_of_nonneg_left hK_le_x hNpos.le
        _ = B := hNx_eq_B
    have hterm2 : ((T - K * m : ℕ) : ℝ) ≤ (1 / 2) * B :=
      rem_le_half_mul_of_le hn hK_pos hm_eq hK_le_x hNx_eq_B hB_nn
    have hT_sqrt_eq : (T : ℝ) * √(log N) / √x = B := by
      have hden : 0 < √x := sqrt_pos.mpr hx_pos
      refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 6 ≠ 0)).mp ?_
      rw [div_pow, mul_pow, show (√(log N)) ^ 6 = (log N) ^ 3 by
        calc (√(log N)) ^ 6 = ((√(log N)) ^ 2) ^ 3 := by ring
          _ = (log N) ^ 3 := by rw [sq_sqrt hL.le]]
      rw [show (√x) ^ 6 = x ^ 3 by
        calc (√x) ^ 6 = ((√x) ^ 2) ^ 3 := by ring
          _ = x ^ 3 := by rw [sq_sqrt hx_pos.le]]
      have hx3 : x ^ 3 = ((T : ℝ) / N) ^ 2 * log N := by
        dsimp only [x]
        rw [mul_pow, rpow_two_thirds_cube (by positivity), rpow_one_third_cube hL.le]
      have hB6 : B ^ 6 = (B ^ 3) ^ 2 := by ring
      have hB3 : B ^ 3 = (T : ℝ) ^ 2 * ((N : ℝ) * log N) := by
        dsimp only [B]
        rw [mul_pow, rpow_two_thirds_cube hTr, rpow_one_third_cube (by positivity)]
      rw [hx3, hB6, hB3]
      have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
      field_simp
    have hsqrt_le : (m : ℝ) * √((K : ℝ) * log N) ≤ √2 * B := by
      have h1 := mul_sqrt_block_le (L := log N) hK_pos hKm hx_pos hx_half_le_K
      rwa [hT_sqrt_eq] at h1
    have hterm3 : (m : ℝ) * (C * √((K : ℝ) * log N)) ≤ C * √2 * B := by
      calc (m : ℝ) * (C * √((K : ℝ) * log N))
          = C * ((m : ℝ) * √((K : ℝ) * log N)) := by ring
        _ ≤ C * (√2 * B) := mul_le_mul_of_nonneg_left hsqrt_le hC
        _ = C * √2 * B := by ring
    refine hbase.trans ?_
    have hrew : (3 / 2 + C * √2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
        ((N : ℝ) * log N) ^ ((1 : ℝ) / 3) = B + (1 / 2) * B + C * √2 * B := by
      dsimp only [B]; ring
    change minCumLoss ℓ T + (N : ℝ) * K + ((T - K * m : ℕ) : ℝ) +
        (m : ℝ) * (C * √((K : ℝ) * log N)) ≤
      minCumLoss ℓ T + (3 / 2 + C * √2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
        ((N : ℝ) * log N) ^ ((1 : ℝ) / 3)
    linarith
  · have hK0 : K = 0 := by simp [K, optBlockCount, hT]
    have hT_lt : (T : ℝ) < 2 * N * log N := not_le.mp hT
    have hT_le_B : (T : ℝ) ≤ (3 / 2) * B := by
      rw [← pow_le_pow_iff_left₀ hTr (by positivity) (by decide : 3 ≠ 0)]
      have hB3 : B ^ 3 = (T : ℝ) ^ 2 * ((N : ℝ) * log N) := by
        dsimp only [B]
        rw [mul_pow, rpow_two_thirds_cube hTr, rpow_one_third_cube (by positivity)]
      rw [mul_pow, hB3]
      calc (T : ℝ) ^ 3 = (T : ℝ) ^ 2 * T := by ring
        _ ≤ (T : ℝ) ^ 2 * (2 * ((N : ℝ) * log N)) := by
            nlinarith [sq_nonneg (T : ℝ), hT_lt]
        _ ≤ (3 / 2 : ℝ) ^ 3 * ((T : ℝ) ^ 2 * ((N : ℝ) * log N)) := by
            nlinarith [sq_nonneg (T : ℝ), mul_nonneg hNpos.le hL.le]
    have hbase := mabPlay_expected_loss_le (optBlockLen_pos hn)
      (optBlockCount_mul_optBlockLen_le N T) sched (hH K) hℓ (R := 0)
      (fun c _ k => by
        change ∑ τ ∈ range K, ∑ i, H K c τ i * c τ i ≤ cumLoss c K k + 0
        simp [hK0, cumLoss])
    have hKm0 : K * m = 0 := by rw [hK0, zero_mul]
    have hK0_cast : (K : ℝ) = 0 := by exact_mod_cast hK0
    have htail_eq : ((T - K * m : ℕ) : ℝ) = T := by rw [hKm0, Nat.sub_zero]
    have hCterm : (3 / 2) * B ≤ (3 / 2 + C * √2) * B := by
      nlinarith [hB_nn, mul_nonneg hC (sqrt_nonneg 2)]
    refine hbase.trans ?_
    have hrew : (3 / 2 + C * √2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
        ((N : ℝ) * log N) ^ ((1 : ℝ) / 3) = (3 / 2 + C * √2) * B := by
      dsimp only [B]; ring
    change minCumLoss ℓ T + (N : ℝ) * K + ((T - K * m : ℕ) : ℝ) + (m : ℝ) * 0 ≤
      minCumLoss ℓ T + (3 / 2 + C * √2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
        ((N : ℝ) * log N) ^ ((1 : ℝ) / 3)
    rw [hK0_cast, htail_eq, mul_zero, mul_zero, add_zero, add_zero, hrew]
    linarith

/-- The textbook block count `K = ⌊(T / N)^{2/3}⌋` of [BlumMansour2007AGT, §4.6, p. 96]
for `T ≥ N`, defaulting to `0` when `T < N`. -/
noncomputable def bookBlockCount (N T : ℕ) : ℕ :=
  if N ≤ T then ⌊((T : ℝ) / N) ^ ((2 : ℝ) / 3)⌋₊ else 0

theorem bookBlockCount_eq_zero_of_lt {N T : ℕ} (hT : T < N) :
    bookBlockCount N T = 0 := by
  have hnot : ¬ N ≤ T := by omega
  simp only [bookBlockCount, hnot, ↓reduceIte]

theorem bookBlockCount_eq_floor {N T : ℕ} (hT : N ≤ T) :
    bookBlockCount N T = ⌊((T : ℝ) / N) ^ ((2 : ℝ) / 3)⌋₊ := by
  simp only [bookBlockCount, hT, ↓reduceIte]

/-- Block length paired with `bookBlockCount N T`: `T / K` when `K > 0`, and `N` when `K = 0`. -/
noncomputable def bookBlockLen (N T : ℕ) : ℕ :=
  if bookBlockCount N T = 0 then N else T / bookBlockCount N T

theorem bookBlockCount_pos {N T : ℕ} (hN : 1 ≤ N) (hT : N ≤ T) :
    0 < bookBlockCount N T := by
  simp only [bookBlockCount, hT, ↓reduceIte]
  refine Nat.floor_pos.mpr ?_
  have h1 : (1 : ℝ) ≤ (T : ℝ) / N := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega)), one_mul]
    exact_mod_cast hT
  exact one_le_rpow h1 (by norm_num)

theorem bookBlockCount_mul_bookBlockLen_le (N T : ℕ) :
    bookBlockCount N T * bookBlockLen N T ≤ T := by
  unfold bookBlockLen
  split_ifs with h
  · rw [h, zero_mul]; exact Nat.zero_le T
  · exact Nat.mul_div_le T (bookBlockCount N T)

theorem le_bookBlockLen {N T : ℕ} (hN : 1 ≤ N) : N ≤ bookBlockLen N T := by
  unfold bookBlockLen
  split_ifs with h
  · exact le_rfl
  · have hNT : N ≤ T := by
      by_contra hn
      exact h (by simp [bookBlockCount, hn])
    have hK_pos : 0 < bookBlockCount N T := Nat.pos_of_ne_zero h
    rw [Nat.le_div_iff_mul_le hK_pos]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3)
    have hK_le : (bookBlockCount N T : ℝ) ≤ x := by
      simp only [bookBlockCount, hNT, ↓reduceIte]
      exact Nat.floor_le (by positivity)
    have hNx_le : (N : ℝ) * x ≤ T := by
      rw [← pow_le_pow_iff_left₀ (by positivity) hTr (by decide : 3 ≠ 0)]
      rw [mul_pow, rpow_two_thirds_cube (by positivity)]
      have hcalc : (N : ℝ) ^ 3 * ((T : ℝ) / N) ^ 2 = (T : ℝ) ^ 2 * N := by field_simp
      rw [hcalc]
      have hNT_r : (N : ℝ) ≤ T := by exact_mod_cast hNT
      nlinarith [sq_nonneg (T : ℝ)]
    have hmul : ((N * bookBlockCount N T : ℕ) : ℝ) ≤ T := by
      push_cast
      exact (mul_le_mul_of_nonneg_left hK_le hNr.le).trans hNx_le
    exact_mod_cast hmul

theorem bookBlockLen_pos {N T : ℕ} (hN : 1 ≤ N) : 0 < bookBlockLen N T :=
  lt_of_lt_of_le (by omega) (le_bookBlockLen hN)

/-- **Theorem 4.17 with the textbook block count `K = ⌊(T / N)^{2/3}⌋`**
[BlumMansour2007AGT, §4.6, Theorem 4.17, p. 96]: for `N ≥ 2` and `T ≥ N`, given *any* family `H K`
of causal full-information learners with regret at most `C * √(K * ln N)` over `K` rounds,
`mabPlay` has expected loss at most
`minCumLoss ℓ T + (3 / 2 + C * √2 * √(ln N)) * T^{2/3} * N^{1/3}`. -/
theorem mabPlay_expected_loss_le_book [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Fintype.card ι ≤ T)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι (bookBlockLen (Fintype.card ι) T) Ω)
    {H : ℕ → (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : ∀ K, IsOnlineAlg (H K))
    {C : ℝ} (hC : 0 ≤ C)
    (hreg : ∀ K (c : ℕ → ι → ℝ), (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H K c τ i * c τ i ≤
        cumLoss c K k + C * √((K : ℝ) * log (Fintype.card ι)))
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    (𝔼 ω : Fin (bookBlockCount (Fintype.card ι) T) → Ω,
        ∑ t ∈ range T,
          ∑ j, mabPlay (bookBlockLen_pos (by omega : 1 ≤ Fintype.card ι)) sched
            (H (bookBlockCount (Fintype.card ι) T)) ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (3 / 2 + C * √2 * √(log (Fintype.card ι))) *
          (T : ℝ) ^ ((2 : ℝ) / 3) * (Fintype.card ι : ℝ) ^ ((1 : ℝ) / 3) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let N := Fintype.card ι
  let K := bookBlockCount N T
  let m := bookBlockLen N T
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hK_pos : 0 < K := bookBlockCount_pos hN1 hT
  have hKr_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK_pos
  have hK_ne : K ≠ 0 := hK_pos.ne'
  have hm_eq : m = T / K := by simp only [m, bookBlockLen, K, hK_ne, ↓reduceIte]
  have hKm : K * m ≤ T := bookBlockCount_mul_bookBlockLen_le N T
  have hbase := mabPlay_expected_loss_le (bookBlockLen_pos hN1) hKm sched (hH K) hℓ (hreg K)
  set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3)
  set B : ℝ := (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)
  have hB_nn : 0 ≤ B := by positivity
  have hx_ge : 1 ≤ x := one_le_rpow (by
    rw [le_div_iff₀ hNpos, one_mul]
    exact_mod_cast hT) (by norm_num)
  have hx_pos : 0 < x := by linarith
  have hK_le_x : (K : ℝ) ≤ x := by
    change (bookBlockCount (Fintype.card ι) T : ℝ) ≤ x
    simp only [bookBlockCount, hT, ↓reduceIte]
    exact Nat.floor_le hx_pos.le
  have hx_half_le_K : x / 2 ≤ (K : ℝ) := by
    change x / 2 ≤ (bookBlockCount (Fintype.card ι) T : ℝ)
    simp only [bookBlockCount, hT, ↓reduceIte]
    exact half_le_natFloor_of_one_le hx_ge
  have hNx_eq_B : (N : ℝ) * x = B := by
    refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 3 ≠ 0)).mp ?_
    rw [mul_pow, show x ^ 3 = ((T : ℝ) / N) ^ 2 by
      exact rpow_two_thirds_cube (by positivity)]
    rw [show B ^ 3 = (T : ℝ) ^ 2 * N by
      dsimp only [B]
      rw [mul_pow, rpow_two_thirds_cube hTpos.le, rpow_one_third_cube hNpos.le]]
    field_simp
  have hterm1 : (N : ℝ) * K ≤ B :=
    (mul_le_mul_of_nonneg_left hK_le_x hNpos.le).trans_eq hNx_eq_B
  have hterm2 : ((T - K * m : ℕ) : ℝ) ≤ (1 / 2) * B :=
    rem_le_half_mul_of_le hn hK_pos hm_eq hK_le_x hNx_eq_B hB_nn
  have hT_div_eq : (T : ℝ) / √x = B := by
    refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 6 ≠ 0)).mp ?_
    rw [div_pow, show (√x) ^ 6 = x ^ 3 by
      calc (√x) ^ 6 = ((√x) ^ 2) ^ 3 := by ring
        _ = x ^ 3 := by rw [sq_sqrt hx_pos.le]]
    rw [show x ^ 3 = ((T : ℝ) / N) ^ 2 by exact rpow_two_thirds_cube (by positivity)]
    rw [show B ^ 6 = (B ^ 3) ^ 2 by ring, show B ^ 3 = (T : ℝ) ^ 2 * N by
      dsimp only [B]
      rw [mul_pow, rpow_two_thirds_cube hTpos.le, rpow_one_third_cube hNpos.le]]
    field_simp
  have hterm3 : (m : ℝ) * (C * √((K : ℝ) * log N)) ≤ C * √2 * √(log N) * B := by
    have hcore : (m : ℝ) * √((K : ℝ) * log N) ≤ √2 * √(log N) * B := by
      have h1 := mul_sqrt_block_le (L := log N) hK_pos hKm hx_pos hx_half_le_K
      have hrew : √2 * ((T : ℝ) * √(log N) / √x) = √2 * √(log N) * ((T : ℝ) / √x) := by ring
      rw [hrew, hT_div_eq] at h1
      exact h1
    calc (m : ℝ) * (C * √((K : ℝ) * log N))
        = C * ((m : ℝ) * √((K : ℝ) * log N)) := by ring
      _ ≤ C * (√2 * √(log N) * B) := mul_le_mul_of_nonneg_left hcore hC
      _ = C * √2 * √(log N) * B := by ring
  refine hbase.trans ?_
  have hrew : (3 / 2 + C * √2 * √(log N)) * (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) =
      B + (1 / 2) * B + C * √2 * √(log N) * B := by
    dsimp only [B]; ring
  change minCumLoss ℓ T + (N : ℝ) * K + ((T - K * m : ℕ) : ℝ) +
      (m : ℝ) * (C * √((K : ℝ) * log N)) ≤
    minCumLoss ℓ T + (3 / 2 + C * √2 * √(log N)) *
      (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)
  linarith

/-- Multiplicative `O(T^{2/3} N^{1/3} ln N)` corollary matching the displayed bound of
[BlumMansour2007AGT, Theorem 4.17, p. 96]. -/
theorem mabPlay_expected_loss_le_book_log [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Fintype.card ι ≤ T)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι (bookBlockLen (Fintype.card ι) T) Ω)
    {H : ℕ → (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : ∀ K, IsOnlineAlg (H K))
    {C : ℝ} (hC : 0 ≤ C)
    (hreg : ∀ K (c : ℕ → ι → ℝ), (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H K c τ i * c τ i ≤
        cumLoss c K k + C * √((K : ℝ) * log (Fintype.card ι)))
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    (𝔼 ω : Fin (bookBlockCount (Fintype.card ι) T) → Ω,
        ∑ t ∈ range T,
          ∑ j, mabPlay (bookBlockLen_pos (by omega : 1 ≤ Fintype.card ι)) sched
            (H (bookBlockCount (Fintype.card ι) T)) ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (3 + 2 * C) * (T : ℝ) ^ ((2 : ℝ) / 3) * (Fintype.card ι : ℝ) ^ ((1 : ℝ) / 3) *
          log (Fintype.card ι) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hL_gt : (1 / 2 : ℝ) ≤ log (Fintype.card ι : ℝ) := by
    have hmono : log 2 ≤ log (Fintype.card ι : ℝ) :=
      log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hcoef1 : (3 / 2 : ℝ) ≤ 3 * log (Fintype.card ι : ℝ) := by linarith
  have hcoef2 : √2 * √(log (Fintype.card ι : ℝ)) ≤ 2 * log (Fintype.card ι : ℝ) := by
    have hLnn : 0 ≤ log (Fintype.card ι : ℝ) := by linarith
    have hsq : (√2 * √(log (Fintype.card ι : ℝ))) ^ 2 ≤
        (2 * log (Fintype.card ι : ℝ)) ^ 2 := by
      rw [mul_pow, sq_sqrt (by norm_num), sq_sqrt hLnn]
      nlinarith
    exact le_of_sq_le_sq hsq (by positivity)
  have hbase := mabPlay_expected_loss_le_book hn hT sched hH hC hreg hℓ
  have hfactor : (3 / 2 + C * √2 * √(log (Fintype.card ι : ℝ))) ≤
      (3 + 2 * C) * log (Fintype.card ι : ℝ) := by
    calc 3 / 2 + C * √2 * √(log (Fintype.card ι : ℝ))
        = 3 / 2 + C * (√2 * √(log (Fintype.card ι : ℝ))) := by ring
      _ ≤ 3 * log (Fintype.card ι : ℝ) + C * (2 * log (Fintype.card ι : ℝ)) :=
          add_le_add hcoef1 (mul_le_mul_of_nonneg_left hcoef2 hC)
      _ = (3 + 2 * C) * log (Fintype.card ι : ℝ) := by ring
  have hTN_nn : 0 ≤ (T : ℝ) ^ ((2 : ℝ) / 3) * (Fintype.card ι : ℝ) ^ ((1 : ℝ) / 3) := by
    positivity
  exact hbase.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hTN_nn])

/-! ### Explicit instantiations with RWM and anytime Hedge -/

/-- Horizon-tuned RWM instantiation of the partial-information reduction
[BlumMansour2007AGT, Theorem 4.17]: using `prob (rwmFactor (tunedStep (ln N) K))` (`C = 2`) with
any collision-free `ExplorationSchedule`, expected total loss is at most
`minCumLoss ℓ T + (9 / 2) * T^{2/3} * (N * ln N)^{1/3}` for *every* `N ≥ 2` and `T : ℕ`. -/
theorem mabRWM_expected_loss_le [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (T : ℕ)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι (optBlockLen (Fintype.card ι) T) Ω)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let K := optBlockCount (Fintype.card ι) T
    let H := fun K' => prob (rwmFactor (tunedStep (log (Fintype.card ι)) K'))
    (𝔼 ω : Fin K → Ω,
        ∑ t ∈ range T, ∑ j, mabPlay (optBlockLen_pos hn) sched (H K) ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (9 / 2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
          ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hL : 0 < log (Fintype.card ι : ℝ) := log_pos (by exact_mod_cast hn)
  have halg : ∀ K : ℕ, IsOnlineAlg
      (prob (rwmFactor (tunedStep (log (Fintype.card ι)) (K : ℝ))) :
        (ℕ → ι → ℝ) → ℕ → ι → ℝ) :=
    fun K => isOnlineAlg_rwm (lt_of_le_of_lt (tunedStep_le_half hL.le K) (by norm_num))
  have hreg : ∀ K : ℕ, ∀ (c : ℕ → ι → ℝ), (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K,
          ∑ i, prob (rwmFactor (tunedStep (log (Fintype.card ι)) (K : ℝ))) c τ i * c τ i ≤
        cumLoss c K k + 2 * √((K : ℝ) * log (Fintype.card ι)) := fun K c hc k => by
    linarith [rwm_loss_le_tunedStep hn hc, minCumLoss_le c K k]
  have hbound := mabPlay_expected_loss_le_optimal hn T sched halg
    (by norm_num : (0 : ℝ) ≤ 2) hreg hℓ
  have h2sqrt2 : 2 * √2 ≤ (3 : ℝ) :=
    le_of_sq_le_sq (by rw [mul_pow, sq_sqrt (by norm_num)]; norm_num) (by norm_num)
  have hBnn : 0 ≤ (T : ℝ) ^ ((2 : ℝ) / 3) *
      ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by positivity
  refine hbound.trans ?_
  have hcoef : 3 / 2 + 2 * √2 ≤ (9 / 2 : ℝ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hBnn]

/-- Horizon-free `anytimeHedgeProb` instantiation of the partial-information reduction (`C = 3`):
expected total loss is at most `minCumLoss ℓ T + 6 * T^{2/3} * (N * ln N)^{1/3}` for *every*
`N ≥ 2` and `T : ℕ`. -/
theorem mabAnytimeHedge_expected_loss_le [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (T : ℕ)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι (optBlockLen (Fintype.card ι) T) Ω)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    (𝔼 ω : Fin (optBlockCount (Fintype.card ι) T) → Ω,
        ∑ t ∈ range T, ∑ j, mabPlay (optBlockLen_pos hn) sched anytimeHedgeProb ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        6 * (T : ℝ) ^ ((2 : ℝ) / 3) *
          ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hbound := mabPlay_expected_loss_le_optimal hn T sched
    (H := fun _ => anytimeHedgeProb) (fun _ => isOnlineAlg_anytimeHedge)
    (by norm_num : (0 : ℝ) ≤ 3)
    (fun _ _ hc k => anytimeHedge_regret_le hn hc k) hℓ
  have h3sqrt2 : 3 * √2 ≤ (9 / 2 : ℝ) :=
    le_of_sq_le_sq (by rw [mul_pow, sq_sqrt (by norm_num)]; norm_num) (by norm_num)
  have hBnn : 0 ≤ (T : ℝ) ^ ((2 : ℝ) / 3) *
      ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by positivity
  refine hbound.trans ?_
  have hcoef : 3 / 2 + 3 * √2 ≤ (6 : ℝ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hBnn]

/-- Complete specialization to the uniform collision-free injection schedule `ι ↪ Fin m`
with horizon-tuned RWM (`prob (rwmFactor (tunedStep (ln N) K))`), witnessing nonemptiness of `Ω`
automatically. -/
theorem mabRWM_uniformInj_expected_loss_le [DecidableEq ι] (hn : 2 ≤ Fintype.card ι) (T : ℕ)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let sched := uniformInjExplorationSchedule (ι := ι) (optBlockLen_pos hn) (le_optBlockLen hn)
    let K := optBlockCount (Fintype.card ι) T
    let H := prob (rwmFactor (tunedStep (log (Fintype.card ι)) K))
    (𝔼 ω : Fin K → (ι ↪ Fin (optBlockLen (Fintype.card ι) T)),
        ∑ t ∈ range T, ∑ j, mabPlay (optBlockLen_pos hn) sched H ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (9 / 2) * (T : ℝ) ^ ((2 : ℝ) / 3) *
          ((Fintype.card ι : ℝ) * log (Fintype.card ι)) ^ ((1 : ℝ) / 3) := by
  have : Nonempty (ι ↪ Fin (optBlockLen (Fintype.card ι) T)) :=
    ⟨(Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb (le_optBlockLen hn))⟩
  exact mabRWM_expected_loss_le hn T
    (uniformInjExplorationSchedule (ι := ι) (optBlockLen_pos hn) (le_optBlockLen hn)) hℓ

end Cslib.MachineLearning.OnlineLearning.Experts
