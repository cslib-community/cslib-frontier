/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.LowerBounds
public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.CardEmbedding
import CslibFrontier.Foundations.Data.Finset.Expect
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
# Partial-information (multi-armed bandit) block-exploration reduction

This module formalizes the generic block-exploration reduction from the adversarial
partial-information (multi-armed bandit, MAB) model to the full-information (experts) model of
[BlumMansour2007AGT, §4.6, Theorem 4.17, pp. 94–96].

Given `N = Fintype.card ι` actions, a horizon `T`, `K` blocks of length `m` (`K * m ≤ T`, `N ≤ m`),
and a causal full-information algorithm `H` (`IsOnlineAlgorithm H`) with external regret bound
`R` over `K` rounds on `[0, 1]` loss vectors, the bandit reduction partitions `[0, K * m)` into `K`
blocks `B_τ = {τ * m, …, τ * m + m - 1}`. In each block `τ`:

* Every action `i : ι` is assigned a collision-free exploration offset `time (ω τ) i : Fin m` whose
  marginal distribution under the uniform average over `ω τ : Ω` is uniform on `Fin m`
  (`ExplorationSchedule`, canonically witnessed by `uniformInjExplorationSchedule` over all
  injections `ι ↪ Fin m`).
* At exploration step `t = τ * m + time (ω τ) i`, `mabPlay` plays action `i` deterministically
  (`mabPlay_apply_explore`), observes *only* the loss `ℓ t i` of the played arm, and records
  `ĉ_i^τ := ℓ t i` (`exploredLoss`).
* At the remaining `m - N` exploitation steps of block `τ`, `mabPlay` plays the distribution
  `H (exploredLoss sched ω ℓ) τ` (`mabPlay_apply_exploit`), which depends *only* on the single-arm
  losses observed during the earlier blocks' exploration rounds (`mabPlay_bandit_congr`).
* On any leftover tail rounds `t ∈ [K * m, T)` (`T - K * m < K` when `m = T / K`), `mabPlay` plays
  the uniform distribution on `ι`, avoiding any divisibility assumption `K ∣ T`.

Consistent with the rest of `CslibFrontier/MachineLearning/OnlineLearning/`, all bounds state
mathematical expected regret over oblivious `[0, 1]` loss sequences under the uniform average `𝔼 ω`
over exploration schedules (`Fin K → Ω`), with partial-information feedback causality proved
explicitly in `mabPlay_bandit_congr`, without claiming machine running time.

## Overview and source mapping

* **Full-information block learner** (`blockAvgLoss`, `blockFullInfo`, `blockFullInfo_loss_le` —
  [BlumMansour2007AGT, §4.6, p. 94]): over `K` blocks of length `m`, playing
  `p^τ = H (blockAvgLoss m ℓ) τ` throughout block `τ` incurs cumulative loss at most
  `minCumLoss ℓ (K * m) + m * R`.
* **Collision-free exploration and causal decoupling** (`ExplorationSchedule`,
  `uniformInjExplorationSchedule`, `exploredLoss`, `expect_exploredLoss_eq`,
  `expect_online_mul_exploredLoss_eq`, `expect_minCumLoss_exploredLoss_le` —
  [BlumMansour2007AGT, §4.6, eq. (4.2), p. 95]): because `H` is causal, `p^τ` is independent of the
  round-`τ` randomness `ω τ`, so `𝔼_ω[⟨p^τ, ĉ^τ⟩] = 𝔼_ω[⟨p^τ, c^τ⟩]`, and concavity of `min` gives
  `𝔼_ω[min_i Ĉ_i^K] ≤ min_i C_i^K`.
* **Generic `(K, m)` block reduction** (`mabPlay`, `mabPlay_bandit_congr`,
  `mabPlay_expected_loss_le` — [BlumMansour2007AGT, §4.6, p. 95]): for any `0 < m` and `K * m ≤ T`,
  `𝔼_ω[L_MAB^T] ≤ minCumLoss ℓ T + N * K + (T - K * m) + m * R`. (Callers choosing custom block
  counts, such as balancing `N * K` against `(T / K) * √(K * ln N)` at
  `K ≈ (T / N)^{2/3} * (ln N)^{1/3}`, apply `mabPlay_expected_loss_le` directly.)
* **Theorem 4.17 and Polynomial Weights instantiation** (`mabBlockCount`, `mabBlockLen`,
  `mabPlay_expected_loss_le_two_thirds`, `mabMW_expected_loss_le` —
  [BlumMansour2007AGT, §4.6, Theorem 4.17, p. 96]): setting `K = ⌊(T / N)^{2/3}⌋` and
  `m = ⌊T / K⌋` for `T ≥ N` converts any `C * √(K * ln N)` full-information learner into a bandit
  learner with expected regret at most `(3 + 2 * C) * T^{2/3} * N^{1/3} * ln N`, and instantiating
  with capped Polynomial Weights (`prob (mwFactor (min √(ln N / K) (1 / 2)))`, `C = 2` via
  `mw_regret_le_sqrt_of_mem_Icc`) yields `7 * T^{2/3} * N^{1/3} * ln N`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.blockAvgLoss`: block-average loss vector `c^τ`.
* `Cslib.MachineLearning.OnlineLearning.Experts.blockFullInfo`: full-information learner playing
  constant distributions across blocks (`FIB`).
* `Cslib.MachineLearning.OnlineLearning.Experts.ExplorationSchedule`: collision-free block
  exploration schedule with uniform marginal exploration times.
* `Cslib.MachineLearning.OnlineLearning.Experts.uniformInjExplorationSchedule`: canonical uniform
  schedule over all injections `ι ↪ Fin m`.
* `Cslib.MachineLearning.OnlineLearning.Experts.exploredLoss`: single-arm bandit estimate `ĉ^τ`.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay`: partial-information block-exploration
  learner (`MAB`).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabBlockCount`,
  `Cslib.MachineLearning.OnlineLearning.Experts.mabBlockLen`: block count `⌊(T / N)^{2/3}⌋` and
  block length `⌊T / K⌋` of [BlumMansour2007AGT, p. 96].

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.blockFullInfo_loss_le`: full-information block
  regret bound `L_FIB^{K m} ≤ minCumLoss ℓ (K * m) + m * R` ([BlumMansour2007AGT, §4.6, p. 94]).
* `Cslib.MachineLearning.OnlineLearning.Experts.expect_exploredLoss_eq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.expect_online_mul_exploredLoss_eq`,
  `Cslib.MachineLearning.OnlineLearning.Experts.expect_minCumLoss_exploredLoss_le`: unbiasedness,
  causal decoupling ([BlumMansour2007AGT, eq. (4.2), p. 95]), and expected-minimum inequality.
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_bandit_congr`: bandit-feedback causality of
  `mabPlay` (round-`t` play depends solely on the single-arm losses observed at earlier exploration
  rounds).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le`: generic `(K, m)`
  block-reduction expected-loss bound ([BlumMansour2007AGT, §4.6, p. 95]).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_two_thirds`: black-box
  `O(T^{2/3} N^{1/3} log N)` bandit reduction ([BlumMansour2007AGT, Theorem 4.17, pp. 94–96]).
* `Cslib.MachineLearning.OnlineLearning.Experts.mabMW_expected_loss_le`: explicit Polynomial Weights
  (`mwFactor`) instantiation achieving `7 * T^{2/3} * N^{1/3} * ln N` expected regret for `T ≥ N`
  ([BlumMansour2007AGT, Theorem 4.17, pp. 94–96]).

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ### Block averages and the full-information block learner (`FIB`) -/

private theorem sum_range_mul_eq_sum_block (K m : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ range (K * m), f t = ∑ τ ∈ range K, ∑ r : Fin m, f (τ * m + r.val) := by
  induction K with
  | zero => simp only [zero_mul, range_zero, sum_empty]
  | succ K ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun r => f (K * m + r)) m).symm

/-- Block-average loss vector `c^τ` of block `τ` of length `m` [BlumMansour2007AGT, §4.6, p. 94]:
`c^τ_i = (∑_{r < m} ℓ(τ * m + r, i)) / m`. -/
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
      _ = m := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

omit [Fintype ι] in
/-- Multiplying the cumulative block-average loss by block length `m` recovers the cumulative loss
over `K * m` rounds. -/
theorem mul_sum_blockAvgLoss {m : ℕ} (hm : 0 < m) (ℓ : ℕ → ι → ℝ) (K : ℕ) (i : ι) :
    (m : ℝ) * ∑ τ ∈ range K, blockAvgLoss m ℓ τ i = ∑ t ∈ range (K * m), ℓ t i := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [blockAvgLoss, mul_sum]
  rw [sum_range_mul_eq_sum_block K m (fun t => ℓ t i)]
  exact sum_congr rfl fun τ _ => mul_div_cancel₀ _ hm_ne

omit [Fintype ι] in
private theorem blockAvgLoss_congr {m : ℕ} {ℓ ℓ' : ℕ → ι → ℝ} {τ : ℕ}
    (h : ∀ r : Fin m, ℓ (τ * m + r.val) = ℓ' (τ * m + r.val)) :
    blockAvgLoss m ℓ τ = blockAvgLoss m ℓ' τ := by
  funext i
  simp only [blockAvgLoss]
  congr 1
  exact sum_congr rfl fun r _ => congrFun (h r) i

omit [Fintype ι] in
/-- Multiplying the minimum cumulative block-average loss by `m` recovers `minCumLoss ℓ (K * m)`. -/
theorem mul_minCumLoss_blockAvgLoss [Finite ι] [Nonempty ι] {m : ℕ} (hm : 0 < m)
    (ℓ : ℕ → ι → ℝ) (K : ℕ) :
    (m : ℝ) * minCumLoss (blockAvgLoss m ℓ) K = minCumLoss ℓ (K * m) := by
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  apply le_antisymm
  · obtain ⟨i₀, hi₀⟩ := exists_sum_eq_minCumLoss ℓ (K * m)
    rw [← hi₀, ← mul_sum_blockAvgLoss hm ℓ K i₀]
    exact mul_le_mul_of_nonneg_left (minCumLoss_le (blockAvgLoss m ℓ) K i₀) hm_nn
  · obtain ⟨i₀, hi₀⟩ := exists_sum_eq_minCumLoss (blockAvgLoss m ℓ) K
    rw [← hi₀, mul_sum_blockAvgLoss hm ℓ K i₀]
    exact minCumLoss_le ℓ (K * m) i₀

/-- The full-information block learner `FIB` [BlumMansour2007AGT, §4.6, p. 94]: throughout block
`τ = t / m`, it plays the constant distribution `H (blockAvgLoss m ℓ) τ`. -/
noncomputable def blockFullInfo (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (m : ℕ) (ℓ : ℕ → ι → ℝ)
    (t : ℕ) : ι → ℝ :=
  H (blockAvgLoss m ℓ) (t / m)

private theorem blockIdx_lt {σ B m : ℕ} (hσ : σ < B) (r : Fin m) : σ * m + r.val < B * m :=
  calc σ * m + r.val < (σ + 1) * m := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left r.isLt _
    _ ≤ B * m := Nat.mul_le_mul_right m hσ

private theorem blockIdx_lt_of_lt_div {σ t m : ℕ} (hσ : σ < t / m) (r : Fin m) :
    σ * m + r.val < t :=
  (blockIdx_lt hσ r).trans_le (Nat.div_mul_le_self t m)

private theorem blockIdx_div {m : ℕ} (hm : 0 < m) (τ : ℕ) (r : Fin m) :
    (τ * m + r.val) / m = τ := by
  rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_left m τ),
    Nat.mul_div_cancel _ hm, Nat.div_eq_of_lt r.isLt, add_zero]

omit [Fintype ι] in
private theorem blockAvgLoss_history_mem_Icc {m t : ℕ} {ℓ : ℕ → ι → ℝ}
    (hℓ : ∀ s < t / m * m, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ σ < t / m, ∀ i, blockAvgLoss m ℓ σ i ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro σ hσ
    simp at hσ
  · exact fun σ hσ i => blockAvgLoss_mem_Icc hm fun r => hℓ _ (blockIdx_lt hσ r) i

/-- If `H` is an online algorithm then `blockFullInfo H m` is an online algorithm. -/
theorem isOnlineAlgorithm_blockFullInfo {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H)
    (m : ℕ) : IsOnlineAlgorithm (blockFullInfo H m) where
  nonneg hℓ i := hH.nonneg
    (blockAvgLoss_history_mem_Icc fun s hs => hℓ s (hs.trans_le (Nat.div_mul_le_self _ m))) i
  sum_eq_one hℓ := hH.sum_eq_one
    (blockAvgLoss_history_mem_Icc fun s hs => hℓ s (hs.trans_le (Nat.div_mul_le_self _ m)))
  congr hℓ h := hH.congr
    (blockAvgLoss_history_mem_Icc fun s hs => hℓ s (hs.trans_le (Nat.div_mul_le_self _ m)))
    fun _ hσ => blockAvgLoss_congr fun r => h _ (blockIdx_lt_of_lt_div hσ r)

/-- Exact total loss of `blockFullInfo H m` over `K` blocks of length `m`
[BlumMansour2007AGT, §4.6, p. 94]: `L_FIB^{K m} = m * ∑ τ < K, ⟨p^τ, c^τ⟩`. -/
theorem blockFullInfo_loss_eq (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) {K m : ℕ} (hm : 0 < m)
    (ℓ : ℕ → ι → ℝ) :
    ∑ t ∈ range (K * m), ∑ i, blockFullInfo H m ℓ t i * ℓ t i =
      (m : ℝ) * ∑ τ ∈ range K, ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i := by
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [sum_range_mul_eq_sum_block K m, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  calc ∑ r : Fin m, ∑ i, blockFullInfo H m ℓ (τ * m + r.val) i * ℓ (τ * m + r.val) i
      = ∑ i, H (blockAvgLoss m ℓ) τ i * ∑ r : Fin m, ℓ (τ * m + r.val) i := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => by simp [blockFullInfo, blockIdx_div hm, mul_sum]
    _ = (m : ℝ) * ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by
          simp only [blockAvgLoss]
          field_simp

/-- Full-information block regret bound [BlumMansour2007AGT, §4.6, p. 94]:
if `H` achieves external regret at most `R` on `blockAvgLoss m ℓ` over `K` blocks, then
`L_FIB^{K m} ≤ minCumLoss ℓ (K * m) + m * R`. -/
theorem blockFullInfo_loss_le [Nonempty ι] {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} {K m : ℕ}
    (hm : 0 < m) {ℓ : ℕ → ι → ℝ} {R : ℝ}
    (hreg : ∀ k : ι,
      ∑ τ ∈ range K, ∑ i, H (blockAvgLoss m ℓ) τ i * blockAvgLoss m ℓ τ i ≤
        ∑ τ ∈ range K, blockAvgLoss m ℓ τ k + R) :
    ∑ t ∈ range (K * m), ∑ i, blockFullInfo H m ℓ t i * ℓ t i ≤
      minCumLoss ℓ (K * m) + (m : ℝ) * R := by
  obtain ⟨k₀, hk₀⟩ := exists_sum_eq_minCumLoss (blockAvgLoss m ℓ) K
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

/-- Right-shift permutation of `ι ↪ Fin m` adding `s : Fin m` to every offset. -/
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

/-- Canonical uniform exploration schedule over all collision-free injections `ι ↪ Fin m`
(`|ι| ≤ m`, `0 < m`), matching [BlumMansour2007AGT, §4.6, p. 95]. -/
noncomputable def uniformInjExplorationSchedule {m : ℕ}
    (hm : 0 < m) (_hcard : Fintype.card ι ≤ m) :
    ExplorationSchedule ι m (ι ↪ Fin m) where
  time := id
  expect_apply i f := by
    have : NeZero m := ⟨hm.ne'⟩
    have : Nonempty (ι ↪ Fin m) :=
      ⟨(Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb _hcard)⟩
    have hshift : ∀ s : Fin m,
        (𝔼 ω : ι ↪ Fin m, f (ω i)) = 𝔼 ω : ι ↪ Fin m, f (ω i + s) := fun s =>
      (Fintype.expect_equiv (shiftEmbEquiv s) (fun ω => f (ω i + s)) (fun ω => f (ω i))
        fun _ => rfl).symm
    calc (𝔼 ω : ι ↪ Fin m, f (ω i))
        = 𝔼 _s : Fin m, 𝔼 ω : ι ↪ Fin m, f (ω i) := (Fintype.expect_const _).symm
      _ = 𝔼 s : Fin m, 𝔼 ω : ι ↪ Fin m, f (ω i + s) := expect_congr rfl fun s _ => hshift s
      _ = 𝔼 ω : ι ↪ Fin m, 𝔼 s : Fin m, f (ω i + s) := expect_comm _ _ _
      _ = 𝔼 _ω : ι ↪ Fin m, (∑ r : Fin m, f r) / m := expect_congr rfl fun ω _ => by
            rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
            congr 1
            exact Fintype.sum_equiv (Equiv.addLeft (ω i)) _ _ fun _ => rfl
      _ = (∑ r : Fin m, f r) / m := Fintype.expect_const _

@[simp] theorem uniformInjExplorationSchedule_time {m : ℕ}
    (hm : 0 < m) (hcard : Fintype.card ι ≤ m) (ω : ι ↪ Fin m) (i : ι) :
    (uniformInjExplorationSchedule hm hcard).time ω i = ω i := by
  simp only [uniformInjExplorationSchedule, id_eq]

/-! ### Unbiased exploration feedback `ĉ` and causal decoupling -/

/-- The single-arm exploration loss estimate `ĉ^τ` fed to the full-information base algorithm
[BlumMansour2007AGT, §4.6, p. 95]: for each block `τ < K` and action `i`,
`exploredLoss sched ω ℓ τ i = ℓ (τ * m + time (ω τ) i) i`, reading only the loss of action `i` at
the single round where action `i` is deterministically played. -/
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
private theorem exploredLoss_mem_Icc_of_obs {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (sched : ExplorationSchedule ι m Ω) (ω : Fin K → Ω) {ℓ : ℕ → ι → ℝ} {τ : ℕ}
    (hobs : ∀ σ : Fin K, σ.val < τ → ∀ i : ι,
      ℓ (σ.val * m + (sched.time (ω σ) i).val) i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ σ < τ, ∀ i : ι, exploredLoss sched ω ℓ σ i ∈ Set.Icc (0 : ℝ) 1 := by
  intro σ hσ i
  by_cases hσK : σ < K
  · rw [exploredLoss_of_lt sched ω ℓ hσK i]
    exact hobs ⟨σ, hσK⟩ hσ i
  · simp only [exploredLoss, hσK, ↓reduceDIte, Set.mem_Icc, le_refl, zero_le_one, and_self]

omit [Fintype ι] in
private theorem exploredLoss_mem_Icc {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (sched : ExplorationSchedule ι m Ω) (ω : Fin K → Ω) {ℓ : ℕ → ι → ℝ}
    (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {τ : ℕ} (hτ : τ < K) (i : ι) :
    exploredLoss sched ω ℓ τ i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [exploredLoss_of_lt sched ω ℓ hτ i]
  exact hℓ _ (blockIdx_lt hτ _) i

omit [Fintype ι] in
/-- Unbiasedness of `exploredLoss` [BlumMansour2007AGT, §4.6, p. 95]:
for every block `τ < K` and action `i`, `𝔼_ω[ĉ^τ_i] = c^τ_i`. -/
theorem expect_exploredLoss_eq {m K : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι m Ω) (ℓ : ℕ → ι → ℝ) {τ : ℕ} (hτ : τ < K) (i : ι) :
    (𝔼 ω : Fin K → Ω, exploredLoss sched ω ℓ τ i) = blockAvgLoss m ℓ τ i := by
  rw [← Fintype.expect_expect_update (fun ω : Fin K → Ω => exploredLoss sched ω ℓ τ i) ⟨τ, hτ⟩]
  have hinner : ∀ ω : Fin K → Ω,
      (𝔼 x : Ω, exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i) =
        blockAvgLoss m ℓ τ i := fun ω =>
    (expect_congr rfl (g := fun x : Ω => ℓ (τ * m + (sched.time x i).val) i) fun x _ => by
      simp only [exploredLoss_of_lt sched _ ℓ hτ i, Function.update_self]).trans
      (sched.expect_apply i fun r => ℓ (τ * m + r.val) i)
  simp only [hinner, Fintype.expect_const]

/-- **Causal decoupling identity** [BlumMansour2007AGT, §4.6, eq. (4.2), p. 95]: because `H` is
causal on `[0, 1]` histories, its round-`τ` distribution depends only on blocks `< τ` and is
independent of `ω τ`, so `𝔼_ω[⟨p^τ(ω), ĉ^τ(ω)⟩] = 𝔼_ω[⟨p^τ(ω), c^τ⟩]`. -/
theorem expect_online_mul_exploredLoss_eq {m K : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sched : ExplorationSchedule ι m Ω) {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {τ : ℕ} (hτ : τ < K) :
    (𝔼 ω : Fin K → Ω,
        ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i) =
      𝔼 ω : Fin K → Ω,
        ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i := by
  rw [← Fintype.expect_expect_update
    (fun ω : Fin K → Ω => ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i)
    ⟨τ, hτ⟩]
  have hinner : ∀ ω : Fin K → Ω,
      (𝔼 x : Ω, ∑ i, H (exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ) τ i *
          exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i) =
        ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i := fun ω => by
    have hindep : ∀ x : Ω,
        H (exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ) τ =
          H (exploredLoss sched ω ℓ) τ := fun x =>
      hH.congr
        (fun σ hσ j => exploredLoss_mem_Icc sched _ hℓ (lt_trans hσ hτ) j)
        fun σ hσ => by
          funext j
          have hσK : σ < K := lt_trans hσ hτ
          have hne : (⟨σ, hσK⟩ : Fin K) ≠ ⟨τ, hτ⟩ := fun h => hσ.ne (congrArg Fin.val h)
          simp only [exploredLoss_of_lt sched _ ℓ hσK j, Function.update_of_ne hne]
    calc (𝔼 x : Ω, ∑ i, H (exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ) τ i *
            exploredLoss sched (Function.update ω ⟨τ, hτ⟩ x) ℓ τ i)
        = 𝔼 x : Ω, ∑ i, H (exploredLoss sched ω ℓ) τ i *
            ℓ (τ * m + (sched.time x i).val) i := by
          refine expect_congr rfl fun x _ => sum_congr rfl fun i _ => ?_
          rw [hindep x, exploredLoss_of_lt sched _ ℓ hτ i, Function.update_self]
      _ = ∑ i, 𝔼 x : Ω, H (exploredLoss sched ω ℓ) τ i *
            ℓ (τ * m + (sched.time x i).val) i := expect_sum_comm _ _ _
      _ = ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i :=
          sum_congr rfl fun i _ => by
            rw [← mul_expect]
            congr 1
            exact sched.expect_apply i (fun r => ℓ (τ * m + r.val) i)
  exact expect_congr rfl fun ω _ => hinner ω

omit [Fintype ι] in
/-- Expected minimum of cumulative explored losses is at most the minimum cumulative true block
average (`𝔼[min_i Ĉ_i^K] ≤ min_i C_i^K`) [BlumMansour2007AGT, §4.6, p. 95]. -/
theorem expect_minCumLoss_exploredLoss_le [Finite ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (sched : ExplorationSchedule ι m Ω) (ℓ : ℕ → ι → ℝ) :
    (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K) ≤
      minCumLoss (blockAvgLoss m ℓ) K := by
  refine le_minCumLoss_iff.mpr fun i => ?_
  calc (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K)
      ≤ 𝔼 ω : Fin K → Ω, ∑ τ ∈ range K, exploredLoss sched ω ℓ τ i :=
        expect_le_expect fun ω _ => minCumLoss_le (exploredLoss sched ω ℓ) K i
    _ = ∑ τ ∈ range K, 𝔼 ω : Fin K → Ω, exploredLoss sched ω ℓ τ i := expect_sum_comm _ _ _
    _ = ∑ τ ∈ range K, blockAvgLoss m ℓ τ i :=
        sum_congr rfl fun τ hτ => expect_exploredLoss_eq sched ℓ (mem_range.mp hτ) i

private theorem expect_sum_online_mul_blockAvgLoss_le [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ ∑ τ ∈ range K, c τ k + R) :
    (𝔼 ω : Fin K → Ω,
        ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i) ≤
      minCumLoss (blockAvgLoss m ℓ) K + R := by
  have hdec : (𝔼 ω : Fin K → Ω,
      ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * blockAvgLoss m ℓ τ i) =
      𝔼 ω : Fin K → Ω,
        ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i := by
    rw [expect_sum_comm, expect_sum_comm]
    exact sum_congr rfl fun τ hτ =>
      (expect_online_mul_exploredLoss_eq sched hH hℓ (mem_range.mp hτ)).symm
  rw [hdec]
  have hpt : ∀ ω : Fin K → Ω,
      ∑ τ ∈ range K, ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i ≤
        minCumLoss (exploredLoss sched ω ℓ) K + R := fun ω => by
    obtain ⟨k₀, hk₀⟩ := exists_sum_eq_minCumLoss (exploredLoss sched ω ℓ) K
    rw [← hk₀]
    exact hreg (exploredLoss sched ω ℓ)
      (fun τ hτ i => exploredLoss_mem_Icc sched ω hℓ hτ i) k₀
  calc (𝔼 ω : Fin K → Ω, ∑ τ ∈ range K,
          ∑ i, H (exploredLoss sched ω ℓ) τ i * exploredLoss sched ω ℓ τ i)
      ≤ 𝔼 ω : Fin K → Ω, (minCumLoss (exploredLoss sched ω ℓ) K + R) :=
        expect_le_expect fun ω _ => hpt ω
    _ = (𝔼 ω : Fin K → Ω, minCumLoss (exploredLoss sched ω ℓ) K) + R := by
        rw [expect_add_distrib, Fintype.expect_const]
    _ ≤ minCumLoss (blockAvgLoss m ℓ) K + R := by
        linarith [expect_minCumLoss_exploredLoss_le (K := K) sched ℓ]

/-! ### The partial-information block-exploration learner (`mabPlay`) -/

/-- The partial-information (multi-armed bandit) block-exploration algorithm of
[BlumMansour2007AGT, §4.6, pp. 94–96].

Inside each full block `τ = t / m < K` of length `m > 0`:
* if the in-block offset `r = t % m` equals `sched.time (ω τ) i` for some (unique) action `i : ι`,
  `mabPlay` explores by placing probability `1` on `i`;
* otherwise (`r` is not an exploration time in block `τ`), `mabPlay` exploits by playing
  `H (exploredLoss sched ω ℓ) τ`.

On any leftover tail round `t ≥ K * m`, `mabPlay` plays the uniform distribution on `ι`. -/
noncomputable def mabPlay [DecidableEq ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) : ℝ :=
  if hτ : t / m < K then
    if h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩ then
      if j = h.choose then 1 else 0
    else
      H (exploredLoss sched ω ℓ) (t / m) j
  else
    1 / Fintype.card ι

theorem mabPlay_nonneg [DecidableEq ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} (hℓ : ∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) (j : ι) :
    0 ≤ mabPlay hm sched H ω ℓ t j := by
  unfold mabPlay
  by_cases hτ : t / m < K
  · simp only [hτ, ↓reduceDIte]
    by_cases h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩
    · simp only [h, ↓reduceDIte]
      split_ifs <;> norm_num
    · simp only [h, ↓reduceDIte]
      exact hH.nonneg
        (exploredLoss_mem_Icc_of_obs sched ω fun _ hσ i => hℓ _ (blockIdx_lt_of_lt_div hσ _) i) j
  · simp only [hτ, ↓reduceDIte]; positivity

theorem sum_mabPlay_eq_one [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} (hℓ : ∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ j : ι, mabPlay hm sched H ω ℓ t j = 1 := by
  unfold mabPlay
  by_cases hτ : t / m < K
  · simp only [hτ, ↓reduceDIte]
    by_cases h : ∃ i : ι, sched.time (ω ⟨t / m, hτ⟩) i = ⟨t % m, Nat.mod_lt t hm⟩
    · simp only [h, ↓reduceDIte, sum_ite_eq', mem_univ, ↓reduceIte]
    · simp only [h, ↓reduceDIte]
      exact hH.sum_eq_one
        (exploredLoss_mem_Icc_of_obs sched ω fun _ hσ i => hℓ _ (blockIdx_lt_of_lt_div hσ _) i)
  · have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [hτ, ↓reduceDIte, sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self hN]

/-- **Partial-information (bandit) feedback causality**: in round `t`, `mabPlay` depends *only* on
the single-arm losses observed during the earlier blocks' exploration rounds
`(σ * m + time (ω σ) i, i)` for `σ < min (t / m) K` (at each of which `mabPlay` deterministically
played action `i`, by `mabPlay_apply_explore`). Changing losses of any unplayed action, any
exploitation round, or any current/future round leaves `mabPlay`'s output unchanged. -/
theorem mabPlay_bandit_congr [DecidableEq ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω)
    {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (hobs : ∀ σ : Fin K, σ.val < t / m → ∀ i : ι,
      ℓ (σ.val * m + (sched.time (ω σ) i).val) i ∈ Set.Icc (0 : ℝ) 1)
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
      exact congrFun (hH.congr (exploredLoss_mem_Icc_of_obs sched ω hobs) fun σ hσ =>
        funext fun i => by
          have hσK := lt_trans hσ hτ
          simp only [exploredLoss_of_lt sched ω _ hσK i, h ⟨σ, hσK⟩ hσ i]) j
  · simp only [hτ, ↓reduceDIte]

/-- For every fixed exploration seed sequence `ω : Fin K → Ω`, `mabPlay` is a causal online
algorithm (`IsOnlineAlgorithm`). -/
theorem isOnlineAlgorithm_mabPlay [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω) :
    IsOnlineAlgorithm (mabPlay hm sched H ω) where
  nonneg hℓ := mabPlay_nonneg hm sched hH ω hℓ
  sum_eq_one hℓ := sum_mabPlay_eq_one hm sched hH ω hℓ
  congr {_ _ _} hℓ h := mabPlay_bandit_congr hm sched hH ω
    (fun _ hσ i => hℓ _ (blockIdx_lt_of_lt_div hσ _) i)
    (fun _ hσ i => congrFun (h _ (blockIdx_lt_of_lt_div hσ _)) i)

/-- At the unique exploration offset assigned to action `i` in block `τ`, `mabPlay` puts mass `1`
on `i` and `0` on every other action. -/
theorem mabPlay_apply_explore [DecidableEq ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ)
    (τ : Fin K) (i j : ι) :
    mabPlay hm sched H ω ℓ (τ.val * m + (sched.time (ω τ) i).val) j =
      if j = i then 1 else 0 := by
  have hdiv := blockIdx_div hm τ.val (sched.time (ω τ) i)
  have hmod : (τ.val * m + (sched.time (ω τ) i).val) % m = (sched.time (ω τ) i).val :=
    Nat.mul_add_mod_of_lt (sched.time (ω τ) i).isLt
  unfold mabPlay
  have hτ : (τ.val * m + (sched.time (ω τ) i).val) / m < K := by rw [hdiv]; exact τ.isLt
  have hex : ∃ i' : ι, sched.time (ω ⟨(τ.val * m + (sched.time (ω τ) i).val) / m, hτ⟩) i' =
      ⟨(τ.val * m + (sched.time (ω τ) i).val) % m, Nat.mod_lt _ hm⟩ :=
    ⟨i, by
      ext
      simp only [hdiv, Fin.eta, hmod]⟩
  have huniq : hex.choose = i := (sched.time (ω τ)).injective <| Fin.ext <| by
    have hfin : (⟨(τ.val * m + (sched.time (ω τ) i).val) / m, hτ⟩ : Fin K) = τ := Fin.ext hdiv
    simpa only [congrArg ω hfin, hmod] using congrArg Fin.val hex.choose_spec
  simp only [hτ, ↓reduceDIte, hex, huniq]

/-- On any non-exploration offset `r` in block `τ`, `mabPlay` plays the base algorithm's
distribution `H (exploredLoss sched ω ℓ) τ`. -/
theorem mabPlay_apply_exploit [DecidableEq ι] {m K : ℕ} {Ω : Type*} [Fintype Ω]
    (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) (ω : Fin K → Ω) (ℓ : ℕ → ι → ℝ)
    (τ : Fin K) {r : Fin m} (hr : ∀ i : ι, sched.time (ω τ) i ≠ r) (j : ι) :
    mabPlay hm sched H ω ℓ (τ.val * m + r.val) j = H (exploredLoss sched ω ℓ) τ.val j := by
  have hdiv := blockIdx_div hm τ.val r
  have hmod : (τ.val * m + r.val) % m = r.val := Nat.mul_add_mod_of_lt r.isLt
  unfold mabPlay
  have hτ : (τ.val * m + r.val) / m < K := by rw [hdiv]; exact τ.isLt
  have hnot : ¬ ∃ i : ι, sched.time (ω ⟨(τ.val * m + r.val) / m, hτ⟩) i =
      ⟨(τ.val * m + r.val) % m, Nat.mod_lt _ hm⟩ := fun ⟨i, hi⟩ => by
    have hfin : (⟨(τ.val * m + r.val) / m, hτ⟩ : Fin K) = τ := Fin.ext hdiv
    have hr' : (⟨(τ.val * m + r.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = r := Fin.ext hmod
    exact hr i (by rwa [hfin, hr'] at hi)
  rw [dite_eq_left_of_eq_true (eq_true hτ), dite_eq_right_of_eq_false (eq_false hnot), hdiv]

private theorem mabPlay_round_loss_le_one [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω)
    {ℓ : ℕ → ι → ℝ} {t : ℕ} (hℓ : ∀ s ≤ t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j ≤ 1 := by
  have hprev : ∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1 := fun s hs => hℓ s hs.le
  calc
    ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j
      ≤ ∑ j, mabPlay hm sched H ω ℓ t j * 1 :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hℓ t le_rfl j).2
          (mabPlay_nonneg hm sched hH ω hprev j)
    _ = 1 := by simp [sum_mabPlay_eq_one hm sched hH ω hprev]

/-- Per-block loss bound: for every fixed `ω` and block `τ`, `mabPlay` pays at most `N` on its `N`
exploration rounds plus the total block loss `m * ⟨p^τ, c^τ⟩` of `p^τ`. -/
private theorem mabPlay_block_loss_le [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) (ω : Fin K → Ω)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (τ : Fin K) :
    ∑ r : Fin m, ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (Fintype.card ι : ℝ) +
        (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
  classical
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  set E : Finset (Fin m) := univ.image (sched.time (ω τ))
  have hE_le : ∑ r ∈ E,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (Fintype.card ι : ℝ) := by
    calc
      ∑ r ∈ E, ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j
        ≤ ∑ _r ∈ E, (1 : ℝ) := sum_le_sum fun r _ => mabPlay_round_loss_le_one hm sched hH ω
            fun s hs => hℓ s (hs.trans_lt (blockIdx_lt τ.isLt r))
      _ = (Fintype.card ι : ℝ) := by
          simp [E, card_image_of_injective _ (sched.time (ω τ)).injective]
  have hEc_le : ∑ r ∈ univ \ E,
      ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j ≤
      (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
    have hrew : ∀ r ∈ univ \ E, ∀ j,
        mabPlay hm sched H ω ℓ (τ.val * m + r.val) j = H (exploredLoss sched ω ℓ) τ.val j :=
      fun r hr => mabPlay_apply_exploit hm sched H ω ℓ τ fun i hi =>
        (mem_sdiff.mp hr).2 (mem_image.mpr ⟨i, mem_univ i, hi⟩)
    have hH_nn : ∀ j, 0 ≤ H (exploredLoss sched ω ℓ) τ.val j :=
      hH.nonneg fun _ hσ i => exploredLoss_mem_Icc sched ω hℓ (lt_trans hσ τ.isLt) i
    calc ∑ r ∈ univ \ E,
          ∑ j, mabPlay hm sched H ω ℓ (τ.val * m + r.val) j * ℓ (τ.val * m + r.val) j
        = ∑ r ∈ univ \ E, ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ℓ (τ.val * m + r.val) j :=
          sum_congr rfl fun r hr => sum_congr rfl fun j _ => by rw [hrew r hr j]
      _ ≤ ∑ r : Fin m, ∑ j, H (exploredLoss sched ω ℓ) τ.val j * ℓ (τ.val * m + r.val) j :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset fun r _ _ =>
            sum_nonneg fun j _ => mul_nonneg (hH_nn j) (hℓ _ (blockIdx_lt τ.isLt r) j).1
      _ = (m : ℝ) * ∑ j, H (exploredLoss sched ω ℓ) τ.val j * blockAvgLoss m ℓ τ.val j := by
          rw [sum_comm, mul_sum]
          exact sum_congr rfl fun j _ => by
            rw [← mul_sum]
            simp only [blockAvgLoss]
            field_simp
  rw [← sum_sdiff (subset_univ E)]
  linarith

private theorem mabPlay_expected_loss_le_mul [DecidableEq ι] [Nonempty ι] {m K : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (hm : 0 < m) (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ ∑ τ ∈ range K, c τ k + R) :
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
        rw [expect_add_distrib, Fintype.expect_const, ← mul_expect]
    _ ≤ (Fintype.card ι : ℝ) * K + (m : ℝ) * (minCumLoss (blockAvgLoss m ℓ) K + R) := by
        gcongr
    _ = minCumLoss ℓ (K * m) + (Fintype.card ι : ℝ) * K + (m : ℝ) * R := by
        rw [mul_add, mul_minCumLoss_blockAvgLoss hm ℓ K]
        ring

/-- **Generic block-reduction regret bound** [BlumMansour2007AGT, §4.6, p. 95]:
for any block length `m > 0`, block count `K` with `K * m ≤ T`, collision-free schedule
`sched : ExplorationSchedule ι m Ω`, and causal full-information algorithm `H` achieving external
regret at most `R` over `K` rounds on `[0, 1]` losses, `mabPlay` has expected total loss at most
`minCumLoss ℓ T + N * K + (T - K * m) + m * R` (removing the divisibility hypothesis `K ∣ T`). -/
theorem mabPlay_expected_loss_le [DecidableEq ι] [Nonempty ι] {m K T : ℕ} {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (hm : 0 < m) (hKm : K * m ≤ T)
    (sched : ExplorationSchedule ι m Ω)
    {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) {R : ℝ}
    (hreg : ∀ c : ℕ → ι → ℝ, (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H c τ i * c τ i ≤ ∑ τ ∈ range K, c τ k + R) :
    (𝔼 ω : Fin K → Ω,
        ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T + (Fintype.card ι : ℝ) * K + ((T - K * m : ℕ) : ℝ) + (m : ℝ) * R := by
  have hhead_ℓ : ∀ t < K * m, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1 := fun t ht i =>
    hℓ t (lt_of_lt_of_le ht hKm) i
  have htail : ∀ ω : Fin K → Ω,
      ∑ r ∈ range (T - K * m),
        ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j ≤
        ((T - K * m : ℕ) : ℝ) := fun ω => by
    calc
      ∑ r ∈ range (T - K * m), ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j
        ≤ ∑ _r ∈ range (T - K * m), (1 : ℝ) := sum_le_sum fun r hr =>
            mabPlay_round_loss_le_one hm sched hH ω
              fun s hs => hℓ s (by have := mem_range.mp hr; omega)
      _ = ((T - K * m : ℕ) : ℝ) := by simp
  have hmin_mono : minCumLoss ℓ (K * m) ≤ minCumLoss ℓ T := by
    obtain ⟨k₀, hk₀⟩ := exists_sum_eq_minCumLoss ℓ T
    exact hk₀ ▸ (minCumLoss_le ℓ (K * m) k₀).trans
      (sum_le_sum_of_subset_of_nonneg (range_mono hKm) fun t ht _ => (hℓ t (mem_range.mp ht) k₀).1)
  have hmain := mabPlay_expected_loss_le_mul hm sched hH hhead_ℓ hreg
  have hsplit : ∀ ω : Fin K → Ω,
      ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j =
        (∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) +
        (∑ r ∈ range (T - K * m),
          ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j) := fun ω => by
    conv_lhs => rw [show T = K * m + (T - K * m) by omega]
    exact sum_range_add _ _ _
  calc
    (𝔼 ω : Fin K → Ω, ∑ t ∈ range T, ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j)
      = (𝔼 ω : Fin K → Ω,
          ∑ t ∈ range (K * m), ∑ j, mabPlay hm sched H ω ℓ t j * ℓ t j) +
        (𝔼 ω : Fin K → Ω, ∑ r ∈ range (T - K * m),
          ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j) := by
        rw [expect_congr rfl fun ω _ => hsplit ω, expect_add_distrib]
    _ ≤ (minCumLoss ℓ (K * m) + (Fintype.card ι : ℝ) * K + (m : ℝ) * R) +
        ((T - K * m : ℕ) : ℝ) := by
        refine add_le_add hmain ?_
        calc (𝔼 ω : Fin K → Ω, ∑ r ∈ range (T - K * m),
                ∑ j, mabPlay hm sched H ω ℓ (K * m + r) j * ℓ (K * m + r) j)
            ≤ 𝔼 _ω : Fin K → Ω, ((T - K * m : ℕ) : ℝ) :=
              expect_le_expect fun ω _ => htail ω
          _ = ((T - K * m : ℕ) : ℝ) := Fintype.expect_const _
    _ ≤ minCumLoss ℓ T + (Fintype.card ι : ℝ) * K + ((T - K * m : ℕ) : ℝ) + (m : ℝ) * R := by
        linarith

/-! ### Block-count choice and Theorem 4.17 -/

private theorem rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((2 : ℝ) / 3)) ^ 3 = x ^ 2 := by
  rw [← rpow_natCast, ← rpow_mul hx]
  norm_num

private theorem rpow_one_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← rpow_natCast, ← rpow_mul hx]
  norm_num

/-- Block count `K = ⌊(T / N)^{2/3}⌋` of [BlumMansour2007AGT, §4.6, p. 96]. -/
noncomputable def mabBlockCount (N T : ℕ) : ℕ :=
  ⌊((T : ℝ) / N) ^ ((2 : ℝ) / 3)⌋₊

/-- Block length `m = T / mabBlockCount N T` paired with `mabBlockCount N T`. -/
noncomputable def mabBlockLen (N T : ℕ) : ℕ :=
  T / mabBlockCount N T

theorem mabBlockCount_pos {N T : ℕ} (hN : 0 < N) (hT : N ≤ T) : 0 < mabBlockCount N T := by
  unfold mabBlockCount
  refine Nat.floor_pos.mpr ?_
  have h1 : (1 : ℝ) ≤ (T : ℝ) / N := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hN), one_mul]
    exact_mod_cast hT
  exact one_le_rpow h1 (by norm_num)

theorem mabBlockCount_mul_mabBlockLen_le (N T : ℕ) :
    mabBlockCount N T * mabBlockLen N T ≤ T :=
  Nat.mul_div_le T (mabBlockCount N T)

theorem le_mabBlockLen {N T : ℕ} (hN : 0 < N) (hT : N ≤ T) : N ≤ mabBlockLen N T := by
  unfold mabBlockLen
  rw [Nat.le_div_iff_mul_le (mabBlockCount_pos hN hT)]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hTr : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3)
  have hK_le : (mabBlockCount N T : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hNx_le : (N : ℝ) * x ≤ T := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hTr (by decide : 3 ≠ 0)]
    rw [mul_pow, rpow_two_thirds_cube (by positivity)]
    have hcalc : (N : ℝ) ^ 3 * ((T : ℝ) / N) ^ 2 = (T : ℝ) ^ 2 * N := by field_simp
    rw [hcalc]
    have hNT_r : (N : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith [sq_nonneg (T : ℝ)]
  have hmul : ((N * mabBlockCount N T : ℕ) : ℝ) ≤ T := by
    push_cast
    exact (mul_le_mul_of_nonneg_left hK_le hNr.le).trans hNx_le
  exact_mod_cast hmul

theorem mabBlockLen_pos {N T : ℕ} (hN : 0 < N) (hT : N ≤ T) : 0 < mabBlockLen N T :=
  lt_of_lt_of_le hN (le_mabBlockLen hN hT)

/-- **Partial-information block-exploration reduction** [BlumMansour2007AGT, Theorem 4.17,
pp. 94–96]: for `N = Fintype.card ι ≥ 1` actions, any horizon `T ≥ N`, and any family `H K` of
causal full-information algorithms achieving external regret at most `C * √(K * ln N)` over `K`
rounds on `[0, 1]` losses (`C ≥ 0`), running `mabPlay` over `K = mabBlockCount N T =
⌊(T / N)^{2/3}⌋` blocks of length `m = mabBlockLen N T = ⌊T / K⌋` under the uniform collision-free
schedule `uniformInjExplorationSchedule` achieves expected cumulative loss at most
`minCumLoss ℓ T + (3 + 2 * C) * T^{2/3} * N^{1/3} * ln N` on every `[0, 1]`-valued loss sequence.

For `N ≥ 2` the proof first establishes the sharper `(3 / 2 + C * √2 * √(ln N)) * T^{2/3} * N^{1/3}`
bound and uses `ln N ≥ ln 2 > 1 / 2` to absorb the constant into `ln N`; for `N = 1` both sides
equal `minCumLoss ℓ T` since a single-action distribution incurs zero regret. -/
theorem mabPlay_expected_loss_le_two_thirds [DecidableEq ι] [Nonempty ι] {T : ℕ}
    (hT : Fintype.card ι ≤ T)
    {H : ℕ → (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : ∀ K, IsOnlineAlgorithm (H K))
    {C : ℝ} (hC : 0 ≤ C)
    (hreg : ∀ K (c : ℕ → ι → ℝ), (∀ τ < K, ∀ i, c τ i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k : ι, ∑ τ ∈ range K, ∑ i, H K c τ i * c τ i ≤
        ∑ τ ∈ range K, c τ k + C * √((K : ℝ) * log (Fintype.card ι)))
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    let N := Fintype.card ι
    let K := mabBlockCount N T
    let m := mabBlockLen N T
    let sched := uniformInjExplorationSchedule (ι := ι)
      (mabBlockLen_pos Fintype.card_pos hT) (le_mabBlockLen Fintype.card_pos hT)
    (𝔼 ω : Fin K → (ι ↪ Fin m),
        ∑ t ∈ range T, ∑ j, mabPlay (mabBlockLen_pos Fintype.card_pos hT) sched (H K)
          ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        (3 + 2 * C) * (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) * log N := by
  intro N K m sched
  have hN_pos : 0 < N := Fintype.card_pos
  have hm_pos : 0 < m := mabBlockLen_pos hN_pos hT
  have hcard_m : N ≤ m := le_mabBlockLen hN_pos hT
  have : Nonempty (ι ↪ Fin m) :=
    ⟨(Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard_m)⟩
  by_cases hn : 2 ≤ N
  · have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hn
    have hNpos : (0 : ℝ) < N := by linarith
    have hL : 0 < log (N : ℝ) := log_pos (by linarith)
    have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
    have hK_pos : 0 < K := mabBlockCount_pos hN_pos hT
    have hKr_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK_pos
    have hKm : K * m ≤ T := mabBlockCount_mul_mabBlockLen_le N T
    have hbase := mabPlay_expected_loss_le hm_pos hKm sched (hH K) hℓ (hreg K)
    set x : ℝ := ((T : ℝ) / N) ^ ((2 : ℝ) / 3)
    set B : ℝ := (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)
    have hB_nn : 0 ≤ B := by positivity
    have hx_ge : 1 ≤ x := one_le_rpow (by
      rw [le_div_iff₀ hNpos, one_mul]
      exact_mod_cast hT) (by norm_num)
    have hx_pos : 0 < x := by linarith
    have hK_le_x : (K : ℝ) ≤ x := Nat.floor_le hx_pos.le
    have hx_half_le_K : x / 2 ≤ (K : ℝ) := by
      by_cases hx2 : x < 2
      · have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx_ge)
        linarith
      · have hlt := Nat.lt_floor_add_one x
        change x < (K : ℝ) + 1 at hlt
        linarith
    have hB_cube : B ^ 3 = (T : ℝ) ^ 2 * N := by
      dsimp only [B]
      rw [mul_pow, rpow_two_thirds_cube hTpos.le, rpow_one_third_cube hNpos.le]
    have hNx_eq_B : (N : ℝ) * x = B := by
      refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 3 ≠ 0)).mp ?_
      rw [mul_pow, rpow_two_thirds_cube (by positivity), hB_cube]
      field_simp
    have hterm1 : (N : ℝ) * K ≤ B :=
      (mul_le_mul_of_nonneg_left hK_le_x hNpos.le).trans_eq hNx_eq_B
    have hterm2 : ((T - K * m : ℕ) : ℝ) ≤ (1 / 2) * B := by
      have hrem_nat : T - K * m < K := by
        change T - K * (T / K) < K
        rw [show T - K * (T / K) = T % K by have := Nat.div_add_mod T K; omega]
        exact Nat.mod_lt T hK_pos
      calc ((T - K * m : ℕ) : ℝ) ≤ x := (Nat.cast_le.mpr hrem_nat.le).trans hK_le_x
        _ = (1 / N) * B := by rw [← hNx_eq_B]; field_simp
        _ ≤ (1 / 2) * B :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hNr) hB_nn
    have hT_div_eq : (T : ℝ) / √x = B := by
      refine (pow_left_inj₀ (by positivity) hB_nn (by decide : 6 ≠ 0)).mp ?_
      rw [div_pow, show (√x) ^ 6 = x ^ 3 by rw [show 6 = 2 * 3 by rfl, pow_mul, sq_sqrt hx_pos.le],
        rpow_two_thirds_cube (by positivity), show B ^ 6 = (B ^ 3) ^ 2 by ring, hB_cube]
      field_simp
    have hterm3 : (m : ℝ) * (C * √((K : ℝ) * log N)) ≤ C * √2 * √(log N) * B := by
      have hm_le : (m : ℝ) ≤ (T : ℝ) / K :=
        (le_div_iff₀ hKr_pos).mpr (by exact_mod_cast mul_comm K m ▸ hKm)
      have hsqrtK : 0 < √(K : ℝ) := sqrt_pos.mpr hKr_pos
      have hinv : 1 / √(K : ℝ) ≤ √2 / √x := by
        rw [div_le_div_iff₀ hsqrtK (sqrt_pos.mpr hx_pos), one_mul]
        calc
          √x = √(2 * (x / 2)) := congrArg Real.sqrt (by ring)
          _ = √2 * √(x / 2) := sqrt_mul (by norm_num) _
          _ ≤ √2 * √(K : ℝ) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hx_half_le_K) (sqrt_nonneg _)
      have hcore : (m : ℝ) * √((K : ℝ) * log N) ≤ √2 * √(log N) * B := by
        calc (m : ℝ) * √((K : ℝ) * log N)
            ≤ ((T : ℝ) / K) * (√(K : ℝ) * √(log N)) := by
              rw [← sqrt_mul hKr_pos.le]
              gcongr
          _ = (T : ℝ) * √(log N) * (1 / √(K : ℝ)) := by
              field_simp [hsqrtK.ne']
              rw [sq_sqrt hKr_pos.le]
          _ ≤ (T : ℝ) * √(log N) * (√2 / √x) := by gcongr
          _ = √2 * √(log N) * B := by rw [← hT_div_eq]; ring
      have hc_mul := mul_le_mul_of_nonneg_left hcore hC
      linarith
    have hL_gt : (1 / 2 : ℝ) ≤ log (N : ℝ) := by
      have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
      exact hlog2.trans (log_le_log (by norm_num) hNr)
    have hcoef2 : √2 * √(log (N : ℝ)) ≤ 2 * log (N : ℝ) := by
      refine le_of_sq_le_sq ?_ (by positivity)
      rw [mul_pow, sq_sqrt (by norm_num), sq_sqrt hL.le]
      nlinarith
    have hfactor : 3 / 2 + C * √2 * √(log (N : ℝ)) ≤ (3 + 2 * C) * log (N : ℝ) := by
      linarith [mul_le_mul_of_nonneg_left hcoef2 hC]
    calc
      (𝔼 ω : Fin K → (ι ↪ Fin m),
          ∑ t ∈ range T, ∑ j, mabPlay hm_pos sched (H K) ω ℓ t j * ℓ t j)
        ≤ minCumLoss ℓ T + (N : ℝ) * K + ((T - K * m : ℕ) : ℝ) +
            (m : ℝ) * (C * √((K : ℝ) * log N)) := hbase
      _ ≤ minCumLoss ℓ T +
            (3 + 2 * C) * (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) * log N := by
          have hmul := mul_le_mul_of_nonneg_right hfactor hB_nn
          dsimp only [B] at hterm1 hterm2 hterm3 hmul
          have hrew : ((3 + 2 * C) * log (N : ℝ)) *
              ((T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3)) =
              (3 + 2 * C) * (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) * log N := by ring
          linarith
  · -- Degenerate single-action boundary `N = 1`: regret is identically `0` and `log 1 = 0`.
    have hN1 : N = 1 := le_antisymm (by omega) hN_pos
    have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hN1.le
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [show log (N : ℝ) = 0 by simp [hN1], mul_zero, add_zero]
    have hpt : ∀ ω : Fin K → (ι ↪ Fin m),
        ∑ t ∈ range T, ∑ j, mabPlay hm_pos sched (H K) ω ℓ t j * ℓ t j =
          ∑ t ∈ range T, ℓ t i₀ := fun ω =>
      sum_congr rfl fun t ht => by
        have hs := sum_mabPlay_eq_one hm_pos sched (hH K) ω
          fun s hs i => hℓ s (lt_trans hs (mem_range.mp ht)) i
        rw [Fintype.sum_subsingleton _ i₀] at hs ⊢
        rw [hs, one_mul]
    have hmin_eq : minCumLoss ℓ T = ∑ t ∈ range T, ℓ t i₀ :=
      le_antisymm (minCumLoss_le ℓ T i₀)
        (le_minCumLoss_iff.mpr fun j => by rw [Subsingleton.elim j i₀])
    simp [hpt, hmin_eq]

/-- **Explicit Polynomial Weights instantiation of Theorem 4.17** [BlumMansour2007AGT, Theorem 4.17,
pp. 94–96]: instantiating `mabPlay_expected_loss_le_two_thirds` with capped Polynomial Weights
`prob (mwFactor (min √(ln N / K) (1 / 2)))` (`C = 2` via `mw_regret_le_sqrt_of_mem_Icc` and
`isOnlineAlgorithm_prob`) achieves expected cumulative loss at most
`minCumLoss ℓ T + 7 * T^{2/3} * N^{1/3} * ln N` for every `T ≥ N` and every `[0, 1]` loss
sequence. -/
theorem mabMW_expected_loss_le [DecidableEq ι] [Nonempty ι] {T : ℕ}
    (hT : Fintype.card ι ≤ T)
    {ℓ : ℕ → ι → ℝ} (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    let N := Fintype.card ι
    let K := mabBlockCount N T
    let m := mabBlockLen N T
    let sched := uniformInjExplorationSchedule (ι := ι)
      (mabBlockLen_pos Fintype.card_pos hT) (le_mabBlockLen Fintype.card_pos hT)
    let H := prob (mwFactor (min √(log N / K) (1 / 2)))
    (𝔼 ω : Fin K → (ι ↪ Fin m),
        ∑ t ∈ range T, ∑ j, mabPlay (mabBlockLen_pos Fintype.card_pos hT) sched H
          ω ℓ t j * ℓ t j) ≤
      minCumLoss ℓ T +
        7 * (T : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) * log N := by
  let Hfam : ℕ → (ℕ → ι → ℝ) → ℕ → ι → ℝ := fun K' =>
    prob (mwFactor (min √(log (Fintype.card ι) / K') (1 / 2)))
  have halg : ∀ K', IsOnlineAlgorithm (Hfam K') := fun K' =>
    isOnlineAlgorithm_prob fun x hx => by
      rw [mwFactor_apply]
      have hη_nn : 0 ≤ min √(log (Fintype.card ι) / K') (1 / 2) :=
        le_min (sqrt_nonneg _) (by norm_num)
      have hη_le : min √(log (Fintype.card ι) / K') (1 / 2) ≤ 1 / 2 := min_le_right _ _
      nlinarith [hx.2]
  have hbound := mabPlay_expected_loss_le_two_thirds hT halg (by norm_num : (0 : ℝ) ≤ 2)
    (fun K' c hc k => mw_regret_le_sqrt_of_mem_Icc hc k) hℓ
  simpa only [Hfam, show (3 : ℝ) + 2 * 2 = 7 by norm_num] using hbound

end Cslib.MachineLearning.OnlineLearning.Experts
