/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Nat.Log
import CslibFrontier.Probability.BitString.Khintchine
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# External and dynamic regret lower bounds

This module formalizes all four regret lower-bound theorems and Exercise 4.5 of
[BlumMansour2007AGT, §4.3, §4.3.1, §4.3.4, and Exercise 4.5, pp. 82–88, 101].

## Overview and source mapping

* **Causal online algorithms** (`IsOnlineAlg`):
  `IsOnlineAlg H` states that in each round `t`, `H ℓ t` is a probability distribution on `ι`
  depending only on the losses `ℓ 0, …, ℓ (t - 1)` of earlier rounds. All experts learners in this
  library (`prob (hedgeFactor η)`, `randGreedyProb`, `anytimeHedgeProb`, `blumMansourProb η`, and
  deterministic learners via `detToOnline`) satisfy `IsOnlineAlg`.
* **Theorem 4.1 — Dynamic regret against `G_all`** (`exists_dynamic_regret_ge` —
  [BlumMansour2007AGT, §4.3, Theorem 4.1, pp. 82–83]):
  Against the comparison class `G_all` of all action sequences `g : ℕ → ι`, for every causal online
  algorithm `H` and horizon `T`, there exist a `{0, 1}` loss sequence `ℓ` and an action sequence
  `g` with zero cumulative loss such that `H` incurs expected loss at least `T * (1 - 1 / N)`.
* **Theorem 4.3 — Deterministic lower bound** (`exists_deterministic_loss_eq_and_minCumLoss_eq` —
  [BlumMansour2007AGT, §4.3.1, Theorem 4.3, pp. 83–84]):
  For every causal deterministic algorithm `D : (ℕ → ι → ℝ) → ℕ → ι` and horizon `T`, there exists
  a `{0, 1}` loss sequence `ℓ` on which `D` incurs loss `T` while `minCumLoss ℓ T = ⌊T / N⌋` holds
  with *exact equality* (matching the equality stated in Theorem 4.3 as well as the inequality
  `≤ ⌊T / N⌋` proved on p. 84).
* **Theorem 4.7 — Short-horizon randomized lower bound (`2 ^ T ≤ N`)**
  (`exists_stochastic_loss_eq_half_minCumLoss_zero` — [BlumMansour2007AGT, §4.3.4,
  Theorem 4.7, pp. 87–88]):
  Whenever `2 ^ T ≤ N` (covering `T < log₂ N` and the boundary `N = 2 ^ T`), there is a uniform
  distribution over `2 ^ T` binary `{0, 1}` loss sequences under which *every* causal online
  algorithm `H` incurs expected loss `T / 2` while `minCumLoss ℓ T = 0` holds deterministically on
  *every* realization.
* **Theorem 4.8 — Two-expert `Ω(√T)` stochastic lower bound**
  (`exists_two_experts_stochastic_regret_ge` — [BlumMansour2007AGT, §4.3.4, Theorem 4.8, p. 88]):
  For `N ≥ 2` (in particular `N = 2`), under i.i.d. fair-coin `{0, 1}` losses, every causal online
  algorithm `H` incurs expected loss `T / 2` and expected external regret at least
  `(1 / (2 √3)) * √T`.
* **Exercise 4.5 — General `Ω(√(T log N))` stochastic lower bound**
  (`exists_stochastic_regret_ge_sqrt_mul_log`, `exists_stochastic_regret_ge_sqrt_mul_log_of_card_le`
  — [BlumMansour2007AGT, Exercise 4.5, p. 101]):
  Combining the `2 ^ k` cube embedding (`k = ⌊log₂ N⌋`) across `k` blocks of length `B = ⌊T / k⌋`
  with Khintchine's `L¹` bound inside each block shows that for all `N ≥ 2` and `T ≥ ⌊log₂ N⌋`
  (hence in particular for all `T ≥ N`), there is a stochastic `{0, 1}` loss family under which
  *every* causal online algorithm incurs expected external regret at least
  `(1 / (4 √3)) * √(T * ln N)`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.IsOnlineAlg`: causal online algorithm predicate.
* `Cslib.MachineLearning.OnlineLearning.Experts.detToOnline`: embedding a deterministic learner as a
  point-mass online algorithm.
* `Cslib.MachineLearning.OnlineLearning.Experts.blockCoinLoss`: unified hypercube-block `{0, 1}`
  stochastic loss family underlying Theorems 4.7, 4.8, and Exercise 4.5.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.exists_dynamic_regret_ge`: [BlumMansour2007AGT,
  Theorem 4.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_deterministic_loss_eq_and_minCumLoss_eq`:
  [BlumMansour2007AGT, Theorem 4.3].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_loss_eq_half_minCumLoss_zero`
  — [BlumMansour2007AGT, Theorem 4.7].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_two_experts_stochastic_regret_ge`:
  [BlumMansour2007AGT, Theorem 4.8].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log`,
  `Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log_of_card_le`
  — [BlumMansour2007AGT, Exercise 4.5].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real Cslib.BitString
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ### Causal online algorithms -/

/-- A causal online experts algorithm: in each round `t`, `H ℓ t` is a probability distribution on
`ι` determined solely by the loss vectors `ℓ 0, …, ℓ (t - 1)` of earlier rounds. -/
structure IsOnlineAlg (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) : Prop where
  /-- Probabilities are nonnegative in every round. -/
  nonneg : ∀ ℓ t i, 0 ≤ H ℓ t i
  /-- Probabilities sum to `1` in every round. -/
  sum_eq_one : ∀ ℓ t, ∑ i, H ℓ t i = 1
  /-- Round-`t` distribution depends only on rounds `< t`. -/
  congr : ∀ {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}, (∀ s < t, ℓ s = ℓ' s) → H ℓ t = H ℓ' t

/-- Point-mass online distribution corresponding to a deterministic learner `D`. -/
def detToOnline [DecidableEq ι] (D : (ℕ → ι → ℝ) → ℕ → ι) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  if i = D ℓ t then 1 else 0

theorem isOnlineAlg_detToOnline [DecidableEq ι] {D : (ℕ → ι → ℝ) → ℕ → ι}
    (hD : ∀ {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}, (∀ s < t, ℓ s = ℓ' s) → D ℓ t = D ℓ' t) :
    IsOnlineAlg (detToOnline D) where
  nonneg _ _ _ := by unfold detToOnline; split_ifs <;> norm_num
  sum_eq_one ℓ t := by simp [detToOnline]
  congr h := by funext i; simp only [detToOnline, hD h]

theorem isOnlineAlg_hedge [Nonempty ι] (η : ℝ) : IsOnlineAlg (prob (hedgeFactor η) :
    (ℕ → ι → ℝ) → ℕ → ι → ℝ) where
  nonneg _ _ i := prob_nonneg (fun _ _ _ => by rw [hedgeFactor_apply]; exact exp_pos _) i
  sum_eq_one _ _ := sum_prob (fun _ _ _ => by rw [hedgeFactor_apply]; exact exp_pos _)
  congr h := prob_congr h

theorem isOnlineAlg_randGreedy [Nonempty ι] : IsOnlineAlg (randGreedyProb (ι := ι)) where
  nonneg := randGreedyProb_nonneg
  sum_eq_one := sum_randGreedyProb
  congr h := randGreedyProb_congr h

theorem isOnlineAlg_anytimeHedge [Nonempty ι] : IsOnlineAlg (anytimeHedgeProb (ι := ι)) where
  nonneg := anytimeHedgeProb_nonneg
  sum_eq_one := sum_anytimeHedgeProb
  congr h := anytimeHedgeProb_congr h

theorem isOnlineAlg_blumMansour [DecidableEq ι] [Nonempty ι] (η : ℝ) :
    IsOnlineAlg (blumMansourProb (ι := ι) η) where
  nonneg := blumMansourProb_nonneg η
  sum_eq_one := sum_blumMansourProb η
  congr h := blumMansourProb_congr h

/-! ### Theorem 4.1: Dynamic regret against `G_all` -/

private theorem exists_prob_le_inv_card [Nonempty ι] {p : ι → ℝ} (hsum : ∑ i, p i = 1) :
    ∃ i : ι, p i ≤ 1 / Fintype.card ι := by
  by_contra! hgt
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hlt : (1 : ℝ) < ∑ i, p i := by
    calc (1 : ℝ) = ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) := by
          rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
      _ < ∑ i, p i := sum_lt_sum_of_nonempty univ_nonempty fun i _ => hgt i
  linarith

/-- **Dynamic regret lower bound against `G_all`** [BlumMansour2007AGT, Theorem 4.1, pp. 82–83]:
for every causal online algorithm `H` on `N ≥ 1` experts and horizon `T`, there exist a `{0, 1}`
loss sequence `ℓ` and an action sequence `g : ℕ → ι` such that `g` incurs total loss `0` while `H`
incurs expected loss at least `T * (1 - 1 / N)`. -/
theorem exists_dynamic_regret_ge [Nonempty ι] {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ}
    (hH : IsOnlineAlg H) (T : ℕ) :
    ∃ (ℓ : ℕ → ι → ℝ) (g : ℕ → ι),
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∑ t ∈ range T, ℓ t (g t) = 0) ∧
      (T : ℝ) * (1 - 1 / Fintype.card ι) ≤ ∑ t ∈ range T, ∑ i, H ℓ t i * ℓ t i := by
  classical
  -- Construct `(g t, ℓ t)` adaptively by well-founded recursion on `t`:
  let step : ∀ t : ℕ, (∀ s < t, ι × (ι → ℝ)) → ι × (ι → ℝ) := fun t prev =>
    let ℓ_pre : ℕ → ι → ℝ := fun s => if hs : s < t then (prev s hs).2 else 0
    let it := (exists_prob_le_inv_card (hH.sum_eq_one ℓ_pre t)).choose
    (it, fun i => if i = it then 0 else 1)
  let run : ℕ → ι × (ι → ℝ) := WellFounded.fix Nat.lt_wfRel.wf step
  let g : ℕ → ι := fun t => (run t).1
  let ℓ : ℕ → ι → ℝ := fun t => (run t).2
  have hrun : ∀ t, run t = step t (fun s _ => run s) := fun t =>
    WellFounded.fix_eq Nat.lt_wfRel.wf step t
  have hℓ_eq : ∀ t i, ℓ t i = if i = g t then 0 else 1 := fun t i => by
    have h1 := congrArg Prod.fst (hrun t)
    have h2 := congrArg Prod.snd (hrun t)
    simp only [ℓ, g, h1, h2]
    rfl
  have hg_le : ∀ t, H ℓ t (g t) ≤ 1 / Fintype.card ι := fun t => by
    let ℓ_pre : ℕ → ι → ℝ := fun s => if s < t then (run s).2 else 0
    have hcongr : H ℓ t = H ℓ_pre t := hH.congr fun s hs => by simp [ℓ, ℓ_pre, hs]
    rw [hcongr]
    have hg_def : g t = (exists_prob_le_inv_card (hH.sum_eq_one ℓ_pre t)).choose := by
      dsimp only [g]
      rw [hrun t]
    rw [hg_def]
    exact (exists_prob_le_inv_card (hH.sum_eq_one ℓ_pre t)).choose_spec
  refine ⟨ℓ, g, ?_, ?_, ?_⟩
  · intro t _ i
    rw [hℓ_eq t i]
    split_ifs <;> simp
  · refine sum_eq_zero fun t _ => ?_
    rw [hℓ_eq t (g t)]
    simp only [↓reduceIte]
  · calc (T : ℝ) * (1 - 1 / Fintype.card ι)
        = ∑ _t ∈ range T, (1 - 1 / (Fintype.card ι : ℝ)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ range T, ∑ i, H ℓ t i * ℓ t i := sum_le_sum fun t _ => by
          have h1 := hH.sum_eq_one ℓ t
          have hloss : ∑ i, H ℓ t i * ℓ t i = 1 - H ℓ t (g t) := by
            have hpart : ∑ i, H ℓ t i = H ℓ t (g t) + ∑ i, H ℓ t i * ℓ t i := by
              have hgt : H ℓ t (g t) = ∑ i, if i = g t then H ℓ t i else 0 := by simp
              rw [hgt, ← sum_add_distrib]
              refine sum_congr rfl fun i _ => ?_
              rw [hℓ_eq t i]
              split_ifs <;> ring
            linarith
          rw [hloss]
          linarith [hg_le t]

/-! ### Theorem 4.3: Deterministic lower bound (`L_D^T = T` and `L_min^T = ⌊T / N⌋`) -/

/-- **Deterministic regret lower bound** [BlumMansour2007AGT, Theorem 4.3, pp. 83–84]: for every
causal deterministic algorithm `D` on `N ≥ 1` experts and horizon `T`, there exists a `{0, 1}` loss
sequence `ℓ` on which `D` incurs loss `T` while `minCumLoss ℓ T = ⌊T / N⌋` holds with exact
equality. -/
theorem exists_deterministic_loss_eq_and_minCumLoss_eq [Nonempty ι] {D : (ℕ → ι → ℝ) → ℕ → ι}
    (hD : ∀ {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}, (∀ s < t, ℓ s = ℓ' s) → D ℓ t = D ℓ' t) (T : ℕ) :
    ∃ ℓ : ℕ → ι → ℝ,
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∑ t ∈ range T, ℓ t (D ℓ t) = T) ∧
      minCumLoss ℓ T = ((T / Fintype.card ι : ℕ) : ℝ) := by
  classical
  set N := Fintype.card ι
  have hN : 0 < N := Fintype.card_pos
  set k := T / N
  -- Integer loss construction by well-founded recursion on `t`: in round `t < T`, give loss `1` to
  -- `D`'s chosen action AND to any expert whose remaining slack `(∑ s < t, nℓ s i) + (T - t)` has
  -- dropped to `≤ k` so every expert reaches `≥ k` without ever pushing any slack-forced expert
  -- past `k`.
  let step : ∀ t : ℕ, (∀ s < t, ι → ℕ) → ι → ℕ := fun t prev =>
    let ℓ_pre : ℕ → ι → ℝ := fun s i => if hs : s < t then (prev s hs i : ℝ) else 0
    let xt := D ℓ_pre t
    fun i =>
      if i = xt ∨ (∑ s ∈ attach (range t), prev s.1 (mem_range.mp s.2) i) + (T - t) ≤ k then 1
      else 0
  let nℓ : ℕ → ι → ℕ := WellFounded.fix Nat.lt_wfRel.wf step
  let ℓ : ℕ → ι → ℝ := fun t i => (nℓ t i : ℝ)
  have hnℓ_eq : ∀ t i, nℓ t i =
      if i = D ℓ t ∨ (∑ s ∈ range t, nℓ s i) + (T - t) ≤ k then 1 else 0 := by
    intro t i
    have hfix : nℓ t = step t (fun s _ => nℓ s) := WellFounded.fix_eq Nat.lt_wfRel.wf step t
    have hD_eq : D (fun s j => if hs : s < t then (nℓ s j : ℝ) else 0) t = D ℓ t :=
      hD fun s hs => by funext j; simp [ℓ, hs]
    have hsum_att : (∑ s ∈ attach (range t), nℓ s.1 i) = ∑ s ∈ range t, nℓ s i :=
      sum_attach (range t) fun s => nℓ s i
    have h1 := congrFun hfix i
    dsimp only [step] at h1
    rw [hD_eq, hsum_att] at h1
    exact h1
  have hnℓ_le_one : ∀ t i, nℓ t i ≤ 1 := fun t i => by
    rw [hnℓ_eq t i]
    split_ifs <;> omega
  -- Every expert has `k ≤ ∑ s < t, nℓ s i + (T - t)` for all `t ≤ T`:
  have hslack_ge : ∀ t ≤ T, ∀ i, k ≤ (∑ s ∈ range t, nℓ s i) + (T - t) := by
    intro t ht i
    induction t with
    | zero =>
      simp only [range_zero, sum_empty, zero_add, Nat.sub_zero]
      exact Nat.div_le_self T N
    | succ t ih =>
      have ih' := ih (by omega)
      rw [sum_range_succ, hnℓ_eq t i]
      split_ifs with hc
      · omega
      · omega
  -- If an expert triggers `(∑ s < t₀, nℓ s i) + (T - t₀) ≤ k` at some `t₀ < T`, then its total
  -- loss at `T` is at most `k`:
  have hcap_of_trigger : ∀ i, ∀ t₀ < T, (∑ s ∈ range t₀, nℓ s i) + (T - t₀) ≤ k →
      ∑ s ∈ range T, nℓ s i ≤ k := by
    intro i t₀ ht₀ htrig
    have hsplit : range T = range t₀ ∪ Ico t₀ T := by
      ext s
      simp only [mem_range, mem_union, mem_Ico]
      omega
    have hdisj : Disjoint (range t₀) (Ico t₀ T) := by
      rw [disjoint_left]
      intro s hs1 hs2
      simp only [mem_range, mem_Ico] at hs1 hs2
      omega
    have htail : ∑ s ∈ Ico t₀ T, nℓ s i ≤ T - t₀ := by
      calc ∑ s ∈ Ico t₀ T, nℓ s i ≤ ∑ _s ∈ Ico t₀ T, 1 :=
            sum_le_sum fun s _ => hnℓ_le_one s i
        _ = T - t₀ := by simp
    rw [hsplit, sum_union hdisj]
    omega
  -- By pigeonhole, some expert has `∑ s < T, nℓ s i ≤ k`:
  have hex_le_k : ∃ i, ∑ s ∈ range T, nℓ s i ≤ k := by
    by_contra! hgt
    -- Every expert has `≥ k + 1`, so NO expert ever triggered the slack branch before `T`!
    have hno_trig : ∀ i, ∀ t < T, nℓ t i = if i = D ℓ t then 1 else 0 := by
      intro i t ht
      have hnot : ¬ ((∑ s ∈ range t, nℓ s i) + (T - t) ≤ k) :=
        fun htr => not_le_of_gt (hgt i) (hcap_of_trigger i t ht htr)
      rw [hnℓ_eq t i]
      simp [hnot]
    have htot : ∑ i : ι, ∑ t ∈ range T, nℓ t i = T := by
      rw [sum_comm]
      calc ∑ t ∈ range T, ∑ i : ι, nℓ t i
          = ∑ t ∈ range T, ∑ i : ι, (if i = D ℓ t then 1 else 0) :=
            sum_congr rfl fun t ht => sum_congr rfl fun i _ => hno_trig i t (mem_range.mp ht)
        _ = T := by simp
    have hge : N * (k + 1) ≤ ∑ i : ι, ∑ t ∈ range T, nℓ t i := by
      calc N * (k + 1) = ∑ _i : ι, (k + 1) := by simp [N]
        _ ≤ ∑ i : ι, ∑ t ∈ range T, nℓ t i := sum_le_sum fun i _ => hgt i
    have hlt : T < N * (k + 1) := by
      dsimp only [k]
      have hmod := Nat.div_add_mod T N
      have hrem := Nat.mod_lt T hN
      nlinarith
    omega
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro t _ i
    dsimp only [ℓ]
    rw [hnℓ_eq t i]
    split_ifs <;> simp
  · calc ∑ t ∈ range T, ℓ t (D ℓ t) = ∑ _t ∈ range T, (1 : ℝ) :=
          sum_congr rfl fun t _ => by
            dsimp only [ℓ]
            rw [hnℓ_eq t (D ℓ t)]
            simp only [true_or, ↓reduceIte, Nat.cast_one]
      _ = T := by simp
  · apply le_antisymm
    · obtain ⟨i₀, hi₀⟩ := hex_le_k
      refine (minCumLoss_le ℓ T i₀).trans ?_
      dsimp only [cumLoss, ℓ]
      exact_mod_cast hi₀
    · refine le_minCumLoss_iff.mpr fun i => ?_
      have hge := hslack_ge T le_rfl i
      rw [Nat.sub_self, add_zero] at hge
      dsimp only [cumLoss, ℓ]
      exact_mod_cast hge

/-! ### Unified hypercube-block stochastic adversary (Theorems 4.7, 4.8, and Exercise 4.5) -/

/-- `{0, 1}` loss family parameterized by an embedding `emb : (Fin k → Bool) ↪ ι` of `2 ^ k`
bit-vectors and a `k × B` array of fair coins `c : Fin k → Fin B → Bool`. In round `t = r * B + s`
(`r < k`, `s < B`), expert `emb w` pays `0` if `w r = c r s` and `1` otherwise; unembedded experts
pay `0` if `c r s = true` and `1` otherwise; rounds `t ≥ k * B` have loss `0`. -/
noncomputable def blockCoinLoss {k B : ℕ} (hB : 0 < B) (emb : (Fin k → Bool) ↪ ι)
    (c : Fin k → Fin B → Bool) (t : ℕ) (i : ι) : ℝ :=
  open Classical in
  if ht : t < k * B then
    let r : Fin k := ⟨t / B, (Nat.div_lt_iff_lt_mul hB).mpr ht⟩
    let s : Fin B := ⟨t % B, Nat.mod_lt t hB⟩
    if hex : ∃ w : Fin k → Bool, emb w = i then
      if hex.choose r = c r s then 0 else 1
    else
      if c r s then 0 else 1
  else 0

omit [Fintype ι] in
private theorem blockCoinLoss_binary {k B : ℕ} (hB : 0 < B) (emb : (Fin k → Bool) ↪ ι)
    (c : Fin k → Fin B → Bool) (t : ℕ) (i : ι) :
    blockCoinLoss hB emb c t i = 0 ∨ blockCoinLoss hB emb c t i = 1 := by
  classical
  unfold blockCoinLoss
  split_ifs
  · dsimp only
    split_ifs <;> norm_num
  · dsimp only
    split_ifs <;> norm_num
  · norm_num

omit [Fintype ι] in
private theorem blockCoinLoss_emb_apply {k B : ℕ} (hB : 0 < B) (emb : (Fin k → Bool) ↪ ι)
    (c : Fin k → Fin B → Bool) {t : ℕ} (ht : t < k * B) (w : Fin k → Bool) :
    blockCoinLoss hB emb c t (emb w) =
      if w ⟨t / B, (Nat.div_lt_iff_lt_mul hB).mpr ht⟩ =
          c ⟨t / B, (Nat.div_lt_iff_lt_mul hB).mpr ht⟩ ⟨t % B, Nat.mod_lt t hB⟩
        then 0 else 1 := by
  classical
  have hex : ∃ w' : Fin k → Bool, emb w' = emb w := ⟨w, rfl⟩
  have hchoose : hex.choose = w := emb.injective hex.choose_spec
  unfold blockCoinLoss
  simp only [ht, ↓reduceDIte, hex, hchoose]

private theorem expect_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : β → ℝ) : (𝔼 a : α, f (e a)) = 𝔼 b : β, f b := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_congr e, e.sum_comp]

private theorem expect_sum_finset {α β : Type*} [Fintype α] (s : Finset β) (f : α → β → ℝ) :
    (𝔼 a : α, ∑ b ∈ s, f a b) = ∑ b ∈ s, 𝔼 a : α, f a b := by
  simp only [Fintype.expect_eq_sum_div_card, ← sum_div]
  rw [sum_comm]

private theorem expect_const_mul_real {α : Type*} [Fintype α] (r : ℝ) (f : α → ℝ) :
    (𝔼 a : α, r * f a) = r * 𝔼 a : α, f a := by
  simp only [Fintype.expect_eq_sum_div_card, ← mul_sum, mul_div_assoc]

/-- Involution flipping the single coin `(r, s)` in `c : Fin k → Fin B → Bool`. -/
private def flipBlockCoin {k B : ℕ} (r : Fin k) (s : Fin B) :
    Equiv.Perm (Fin k → Fin B → Bool) where
  toFun c r' s' := if r' = r ∧ s' = s then !(c r' s') else c r' s'
  invFun c r' s' := if r' = r ∧ s' = s then !(c r' s') else c r' s'
  left_inv c := by
    funext r' s'
    dsimp only
    split_ifs <;> simp
  right_inv c := by
    funext r' s'
    dsimp only
    split_ifs <;> simp

/-- Under uniform coins `c : Fin k → Fin B → Bool`, every causal online algorithm `H` incurs
expected total loss `(k * B) / 2` over any horizon `T ≥ k * B`. -/
theorem expect_blockCoinLoss_eq [Nonempty ι] {k B T : ℕ} (hB : 0 < B) (hkB : k * B ≤ T)
    (emb : (Fin k → Bool) ↪ ι) {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlg H) :
    (𝔼 c : Fin k → Fin B → Bool,
      ∑ t ∈ range T, ∑ i, H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb c t i) =
      (k * B : ℝ) / 2 := by
  classical
  rw [expect_sum_finset]
  have hround : ∀ t ∈ range T,
      (𝔼 c : Fin k → Fin B → Bool,
        ∑ i, H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb c t i) =
        if t < k * B then 1 / 2 else 0 := by
    intro t _
    by_cases ht : t < k * B
    · simp only [ht, ↓reduceIte]
      let r : Fin k := ⟨t / B, (Nat.div_lt_iff_lt_mul hB).mpr ht⟩
      let s : Fin B := ⟨t % B, Nat.mod_lt t hB⟩
      set f : (Fin k → Fin B → Bool) → ℝ := fun c =>
        ∑ i, H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb c t i
      have hbij : (𝔼 c, f c) = 𝔼 c, f (flipBlockCoin r s c) :=
        (expect_comp_equiv (flipBlockCoin r s) f).symm
      have hpair : ∀ c, f c + f (flipBlockCoin r s c) = 1 := by
        intro c
        have hcongr : H (blockCoinLoss hB emb (flipBlockCoin r s c)) t =
            H (blockCoinLoss hB emb c) t := hH.congr fun t' ht' => by
          funext i
          have ht'kB : t' < k * B := lt_trans ht' ht
          have hne : ¬ (⟨t' / B, (Nat.div_lt_iff_lt_mul hB).mpr ht'kB⟩ = r ∧
              ⟨t' % B, Nat.mod_lt t' hB⟩ = s) := by
            rintro ⟨hr_eq, hs_eq⟩
            have h1 : t' / B = t / B := congrArg Fin.val hr_eq
            have h2 : t' % B = t % B := congrArg Fin.val hs_eq
            have heq : t' = t := by
              rw [← Nat.div_add_mod t' B, ← Nat.div_add_mod t B, h1, h2]
            exact ht'.ne heq
          unfold blockCoinLoss flipBlockCoin
          simp only [ht'kB, ↓reduceDIte, Equiv.coe_fn_mk, hne, ↓reduceIte]
        have hsum_loss : ∀ i, blockCoinLoss hB emb c t i +
            blockCoinLoss hB emb (flipBlockCoin r s c) t i = 1 := by
          intro i
          unfold blockCoinLoss flipBlockCoin
          simp only [ht, ↓reduceDIte, Equiv.coe_fn_mk, r, s, and_self, ↓reduceIte]
          by_cases hex : ∃ w : Fin k → Bool, emb w = i
          · simp only [hex, ↓reduceDIte]
            cases hex.choose r <;> cases c r s <;> norm_num
          · simp only [hex, ↓reduceDIte]
            cases c r s <;> norm_num
        dsimp only [f]
        rw [hcongr, ← sum_add_distrib]
        calc ∑ i, (H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb c t i +
              H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb (flipBlockCoin r s c) t i)
            = ∑ i, H (blockCoinLoss hB emb c) t i *
                (blockCoinLoss hB emb c t i + blockCoinLoss hB emb (flipBlockCoin r s c) t i) :=
              sum_congr rfl fun i _ => (mul_add _ _ _).symm
          _ = ∑ i, H (blockCoinLoss hB emb c) t i * 1 :=
              sum_congr rfl fun i _ => by rw [hsum_loss i]
          _ = 1 := by simp only [mul_one, hH.sum_eq_one]
      have h2 : 2 * (𝔼 c, f c) = 1 := by
        calc 2 * (𝔼 c, f c) = (𝔼 c, f c) + 𝔼 c, f (flipBlockCoin r s c) := by linarith [hbij]
          _ = 𝔼 c, (f c + f (flipBlockCoin r s c)) := (expect_add_distrib _ _ _).symm
          _ = 𝔼 _c : Fin k → Fin B → Bool, (1 : ℝ) := expect_congr rfl fun c _ => hpair c
          _ = 1 := by simp
      linarith
    · simp only [ht, ↓reduceIte]
      have hzero : ∀ c i, blockCoinLoss hB emb c t i = 0 := fun c i => by
        unfold blockCoinLoss
        simp [ht]
      simp [hzero]
  rw [sum_congr rfl hround]
  have hfilt : (range T).filter (· < k * B) = range (k * B) := by
    ext t
    simp only [mem_filter, mem_range]
    omega
  rw [← sum_filter, hfilt, sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Pointwise upper bound on `minCumLoss` under `blockCoinLoss`: the embedded expert matching each
block's majority bit incurs total loss `(k * B) / 2 - (1 / 2) * ∑ r, |∑ s, signVal (c r s)|`. -/
theorem minCumLoss_blockCoinLoss_le [Nonempty ι] {k B T : ℕ} (hB : 0 < B) (hkB : k * B ≤ T)
    (emb : (Fin k → Bool) ↪ ι) (c : Fin k → Fin B → Bool) :
    minCumLoss (blockCoinLoss hB emb c) T ≤
      (k * B : ℝ) / 2 - (1 / 2) * ∑ r : Fin k, |∑ s : Fin B, signVal (c r s)| := by
  -- Majority bit `w* r` minimizing the block-`r` mismatch count:
  let L_bit : Fin k → Bool → ℝ := fun r b =>
    ∑ s : Fin B, if b = c r s then 0 else 1
  let w_star : Fin k → Bool := fun r => if L_bit r false ≤ L_bit r true then false else true
  have hblock_min : ∀ r : Fin k, L_bit r (w_star r) =
      (B : ℝ) / 2 - (1 / 2) * |∑ s : Fin B, signVal (c r s)| := by
    intro r
    have hsum : L_bit r false + L_bit r true = B := by
      dsimp only [L_bit]
      rw [← sum_add_distrib]
      calc ∑ s : Fin B, ((if false = c r s then (0 : ℝ) else 1) +
            if true = c r s then 0 else 1)
          = ∑ _s : Fin B, (1 : ℝ) := sum_congr rfl fun s _ => by cases c r s <;> norm_num
        _ = B := by simp
    have hdiff : |L_bit r false - L_bit r true| = |∑ s : Fin B, signVal (c r s)| := by
      have hsub : L_bit r false - L_bit r true = -∑ s : Fin B, signVal (c r s) := by
        dsimp only [L_bit]
        rw [← sum_sub_distrib, ← sum_neg_distrib]
        refine sum_congr rfl fun s _ => ?_
        cases c r s <;> norm_num [signVal]
      rw [hsub, abs_neg]
    dsimp only [w_star]
    rw [← hdiff]
    by_cases hle : L_bit r false ≤ L_bit r true
    · simp only [hle, ↓reduceIte, abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · simp only [hle, ↓reduceIte, abs_of_pos (sub_pos.mpr (lt_of_not_ge hle))]
      linarith
  -- Compute `cumLoss (blockCoinLoss hB emb c) T (emb w_star)`:
  refine (minCumLoss_le _ T (emb w_star)).trans_eq ?_
  have hpad : cumLoss (blockCoinLoss hB emb c) T (emb w_star) =
      cumLoss (blockCoinLoss hB emb c) (k * B) (emb w_star) := by
    unfold cumLoss
    refine (sum_subset (range_subset_range.mpr hkB) fun t _ ht => ?_).symm
    have hnot : ¬ t < k * B := by rwa [mem_range] at ht
    unfold blockCoinLoss
    simp [hnot]
  rw [hpad, cumLoss]
  -- Biject `range (k * B)` with `Fin k × Fin B` via `(r, s) ↦ r * B + s`:
  let bij : Fin k × Fin B ≃ Fin (k * B) :=
    { toFun := fun ⟨r, s⟩ => ⟨r.1 * B + s.1, by
        calc r.1 * B + s.1 < r.1 * B + B := Nat.add_lt_add_left s.2 _
          _ = (r.1 + 1) * B := by ring
          _ ≤ k * B := Nat.mul_le_mul_right B r.2⟩
      invFun := fun t =>
        (⟨t.1 / B, (Nat.div_lt_iff_lt_mul hB).mpr t.2⟩, ⟨t.1 % B, Nat.mod_lt t.1 hB⟩)
      left_inv := fun ⟨r, s⟩ => by
        ext <;> dsimp only
        · rw [mul_comm r.1 B, Nat.mul_add_div hB, Nat.div_eq_of_lt s.2, add_zero]
        · rw [mul_comm r.1 B, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt s.2]
      right_inv := fun t => by
        ext
        dsimp only
        have := Nat.div_add_mod t.1 B
        linarith }
  rw [sum_range, ← bij.sum_comp, Fintype.sum_prod_type]
  have hinner : ∀ r : Fin k,
      (∑ s : Fin B, blockCoinLoss hB emb c (bij (r, s)).1 (emb w_star)) = L_bit r (w_star r) := by
    intro r
    refine sum_congr rfl fun s _ => ?_
    have ht : (bij (r, s)).1 < k * B := (bij (r, s)).2
    rw [blockCoinLoss_emb_apply hB emb c ht w_star]
    have hdiv : (r.1 * B + s.1) / B = r.1 := by
      rw [mul_comm r.1 B, Nat.mul_add_div hB, Nat.div_eq_of_lt s.2, add_zero]
    have hmod : (r.1 * B + s.1) % B = s.1 := by
      rw [mul_comm r.1 B, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt s.2]
    have hr_fin : (⟨(bij (r, s)).1 / B, (Nat.div_lt_iff_lt_mul hB).mpr ht⟩ : Fin k) = r :=
      Fin.ext hdiv
    have hs_fin : (⟨(bij (r, s)).1 % B, Nat.mod_lt _ hB⟩ : Fin B) = s :=
      Fin.ext hmod
    rw [hr_fin, hs_fin]
  simp only [hinner, hblock_min, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum]
  ring

/-- **Short-horizon stochastic lower bound (`2 ^ T ≤ N`)** [BlumMansour2007AGT, Theorem 4.7,
pp. 87–88]: when `2 ^ T ≤ Fintype.card ι` (including all `T < log₂ N`), under uniform random coins
`w : Fin T → Bool` there is a `{0, 1}` loss family `ℓ w` such that every realization satisfies
`minCumLoss (ℓ w) T = 0` while *every* causal online algorithm `H` incurs expected loss `T / 2`. -/
theorem exists_stochastic_loss_eq_half_minCumLoss_zero [Nonempty ι] {T : ℕ}
    (hTN : 2 ^ T ≤ Fintype.card ι) :
    ∃ ℓ : (Fin T → Bool) → ℕ → ι → ℝ,
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      (∀ w, minCumLoss (ℓ w) T = 0) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlg H →
        (𝔼 w : Fin T → Bool, ∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) = (T : ℝ) / 2 := by
  have hcard : Fintype.card (Fin T → Bool) ≤ Fintype.card ι := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hTN
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  let toBlock : (Fin T → Bool) ≃ (Fin T → Fin 1 → Bool) :=
    { toFun := fun w r _ => w r
      invFun := fun c r => c r 0
      left_inv := fun _ => rfl
      right_inv := fun c => by funext r s; rw [Subsingleton.elim s 0] }
  let ℓ : (Fin T → Bool) → ℕ → ι → ℝ := fun w =>
    blockCoinLoss Nat.one_pos emb (toBlock w)
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro w t i
    exact blockCoinLoss_binary Nat.one_pos emb (toBlock w) t i
  · intro w
    apply le_antisymm
    · have hle := minCumLoss_blockCoinLoss_le Nat.one_pos (Nat.mul_one T).le emb (toBlock w)
      have habs : ∀ r : Fin T, |∑ s : Fin 1, signVal (toBlock w r s)| = 1 := fun r => by
        rw [Fin.sum_univ_one]
        cases toBlock w r 0 <;> norm_num [signVal]
      simp only [Nat.cast_one, mul_one, habs, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hle
      dsimp only [ℓ]
      linarith
    · exact minCumLoss_nonneg fun s _ i => by
        rcases blockCoinLoss_binary Nat.one_pos emb (toBlock w) s i with h0 | h1 <;> linarith
  · intro H hH
    have hexp := expect_blockCoinLoss_eq Nat.one_pos (Nat.mul_one T).le emb hH
    simp only [Nat.cast_one, mul_one] at hexp
    exact (expect_comp_equiv toBlock
      (fun c => ∑ t ∈ range T, ∑ i, H (blockCoinLoss Nat.one_pos emb c) t i *
        blockCoinLoss Nat.one_pos emb c t i)).trans hexp

/-- Marginal expectation of a function depending on row `r` of a uniform `Fin k → Fin B → Bool`
array equals its expectation over `Fin B → Bool`. -/
private theorem expect_eval_row {k B : ℕ} (r : Fin k) (g : (Fin B → Bool) → ℝ) :
    (𝔼 c : Fin k → Fin B → Bool, g (c r)) = 𝔼 u : Fin B → Bool, g u := by
  classical
  let splitEquiv : (Fin k → Fin B → Bool) ≃
      (Fin B → Bool) × ({r' : Fin k // r' ≠ r} → Fin B → Bool) :=
    { toFun := fun c => (c r, fun r' => c r'.1)
      invFun := fun ⟨u, rest⟩ r' => if h : r' = r then u else rest ⟨r', h⟩
      left_inv := fun c => by
        funext r' s
        by_cases h : r' = r
        · subst h; simp
        · simp [h]
      right_inv := fun ⟨u, rest⟩ => by
        refine Prod.ext (by funext s; simp) (by funext r' s; simp [r'.2]) }
  rw [← expect_comp_equiv splitEquiv.symm (fun c => g (c r))]
  simp only [Fintype.expect_eq_sum_div_card, Fintype.sum_prod_type, Fintype.card_prod]
  simp only [splitEquiv, Equiv.coe_fn_symm_mk, ↓reduceDIte, sum_const, card_univ, nsmul_eq_mul,
    Nat.cast_mul]
  rw [← mul_sum, mul_comm (Fintype.card (Fin B → Bool) : ℝ)]
  have hne : (Fintype.card ({r' : Fin k // r' ≠ r} → Fin B → Bool) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  exact mul_div_mul_left _ _ hne

/-- Core block lower bound: for any `k : ℕ`, `B ≥ 1` with `2 ^ k ≤ N` and `k * B ≤ T`, under uniform
`Fin k → Fin B → Bool` coins every causal online algorithm has expected loss `(k * B) / 2` and
expected external regret at least `(k * √(B / 3)) / 2`. -/
theorem exists_block_stochastic_regret_ge {k B T : ℕ} (hB : 0 < B)
    (hkB : k * B ≤ T) (h2k : 2 ^ k ≤ Fintype.card ι) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by positivity) h2k)
    ∃ ℓ : (Fin k → Fin B → Bool) → ℕ → ι → ℝ,
      (∀ c t i, ℓ c t i = 0 ∨ ℓ c t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlg H →
        (𝔼 c, ∑ t ∈ range T, ∑ i, H (ℓ c) t i * ℓ c t i) = (k * B : ℝ) / 2 ∧
        (k : ℝ) * √((B : ℝ) / 3) / 2 ≤
          𝔼 c, ((∑ t ∈ range T, ∑ i, H (ℓ c) t i * ℓ c t i) - minCumLoss (ℓ c) T) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by positivity) h2k)
  have hcard : Fintype.card (Fin k → Bool) ≤ Fintype.card ι := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h2k
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨blockCoinLoss hB emb, blockCoinLoss_binary hB emb, fun H hH => ?_⟩
  have hexp_H := expect_blockCoinLoss_eq hB hkB emb hH
  refine ⟨hexp_H, ?_⟩
  have hpt : ∀ c : Fin k → Fin B → Bool,
      (1 / 2) * (∑ r : Fin k, |∑ s : Fin B, signVal (c r s)|) ≤
        (k * B : ℝ) / 2 - minCumLoss (blockCoinLoss hB emb c) T := fun c => by
    linarith [minCumLoss_blockCoinLoss_le hB hkB emb c]
  have hexp_diff : 𝔼 c, ((∑ t ∈ range T, ∑ i,
      H (blockCoinLoss hB emb c) t i * blockCoinLoss hB emb c t i) -
      minCumLoss (blockCoinLoss hB emb c) T) =
      𝔼 c, ((k * B : ℝ) / 2 - minCumLoss (blockCoinLoss hB emb c) T) := by
    rw [expect_sub_distrib, expect_sub_distrib, hexp_H, Fintype.expect_const]
  rw [hexp_diff]
  have hmono : 𝔼 c : Fin k → Fin B → Bool,
      ((1 / 2) * ∑ r : Fin k, |∑ s : Fin B, signVal (c r s)|) ≤
      𝔼 c, ((k * B : ℝ) / 2 - minCumLoss (blockCoinLoss hB emb c) T) :=
    expect_le_expect fun c _ => hpt c
  refine le_trans ?_ hmono
  rw [expect_const_mul_real, expect_sum_finset]
  have hrow : ∀ r : Fin k, √((B : ℝ) / 3) ≤
      𝔼 c : Fin k → Fin B → Bool, |∑ s : Fin B, signVal (c r s)| := fun r => by
    rw [expect_eval_row r (fun u => |∑ s : Fin B, signVal (u s)|)]
    simpa [Fintype.card_fin] using (sqrt_card_div_three_le_expect_abs_sum_signVal (ι := Fin B))
  have hsum_rows : (k : ℝ) * √((B : ℝ) / 3) ≤
      ∑ r : Fin k, 𝔼 c : Fin k → Fin B → Bool, |∑ s : Fin B, signVal (c r s)| := by
    calc (k : ℝ) * √((B : ℝ) / 3) = ∑ _r : Fin k, √((B : ℝ) / 3) := by simp
      _ ≤ _ := sum_le_sum fun r _ => hrow r
  linarith

/-- **Two-expert `Ω(√T)` stochastic external-regret lower bound**
[BlumMansour2007AGT, Theorem 4.8, p. 88]: for `N ≥ 2` experts (in particular `N = 2`) and any
horizon `T`, under i.i.d. fair-coin `{0, 1}` losses `c : Fin T → Bool`, every causal online
algorithm `H` incurs expected loss `T / 2` and expected external regret at least
`√(T / 12) = (1 / (2 √3)) * √T`. -/
theorem exists_two_experts_stochastic_regret_ge (hn : 2 ≤ Fintype.card ι) (T : ℕ) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    ∃ ℓ : (Fin T → Bool) → ℕ → ι → ℝ,
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlg H →
        (𝔼 w, ∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) = (T : ℝ) / 2 ∧
        (1 / (2 * √3)) * √(T : ℝ) ≤
          𝔼 w, ((∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) T) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  rcases eq_or_lt_of_le (Nat.zero_le T) with rfl | hT
  · refine ⟨fun _ _ _ => 0, fun _ _ _ => Or.inl rfl, fun H _ => ?_⟩
    simp
  · obtain ⟨ℓ₁, h01, hspec⟩ := exists_block_stochastic_regret_ge (ι := ι) (k := 1) (B := T)
      (T := T) hT (by omega) (by simpa using hn)
    let e : (Fin T → Bool) ≃ (Fin 1 → Fin T → Bool) :=
      { toFun := fun w _ s => w s
        invFun := fun c s => c 0 s
        left_inv := fun _ => rfl
        right_inv := fun c => by funext r s; rw [Subsingleton.elim r 0] }
    refine ⟨fun w => ℓ₁ (e w), fun w t i => h01 (e w) t i, fun H hH => ?_⟩
    obtain ⟨hexp, hreg⟩ := hspec H hH
    simp only [Nat.cast_one, one_mul] at hexp hreg
    have htr1 : (𝔼 w : Fin T → Bool, ∑ t ∈ range T, ∑ i, H (ℓ₁ (e w)) t i * ℓ₁ (e w) t i) =
        𝔼 c : Fin 1 → Fin T → Bool, ∑ t ∈ range T, ∑ i, H (ℓ₁ c) t i * ℓ₁ c t i :=
      expect_comp_equiv e (fun c => ∑ t ∈ range T, ∑ i, H (ℓ₁ c) t i * ℓ₁ c t i)
    have htr2 : (𝔼 w : Fin T → Bool,
        ((∑ t ∈ range T, ∑ i, H (ℓ₁ (e w)) t i * ℓ₁ (e w) t i) - minCumLoss (ℓ₁ (e w)) T)) =
        𝔼 c : Fin 1 → Fin T → Bool,
        ((∑ t ∈ range T, ∑ i, H (ℓ₁ c) t i * ℓ₁ c t i) - minCumLoss (ℓ₁ c) T) :=
      expect_comp_equiv e
        (fun c => (∑ t ∈ range T, ∑ i, H (ℓ₁ c) t i * ℓ₁ c t i) - minCumLoss (ℓ₁ c) T)
    refine ⟨htr1.trans hexp, ?_⟩
    rw [htr2]
    refine le_trans ?_ hreg
    rw [sqrt_div (Nat.cast_nonneg T)]
    have hs3 : (0 : ℝ) < √3 := sqrt_pos.mpr (by norm_num)
    field_simp
    exact le_rfl

/-- **General `Ω(√(T log N))` stochastic external-regret lower bound**
[BlumMansour2007AGT, Exercise 4.5, p. 101]: for `N ≥ 2` experts and `T ≥ ⌊log₂ N⌋`, there exists a
finite probability space (uniform over a hypercube `Fin m → Bool`) of `{0, 1}` loss sequences
under which *every* causal online algorithm incurs expected external regret at least
`(1 / (4 √3)) * √(T * ln N)`. -/
theorem exists_stochastic_regret_ge_sqrt_mul_log (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Nat.log 2 (Fintype.card ι) ≤ T) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    ∃ (m : ℕ) (ℓ : (Fin m → Bool) → ℕ → ι → ℝ),
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlg H →
        (1 / (4 * √3)) * √((T : ℝ) * log (Fintype.card ι)) ≤
          𝔼 w : Fin m → Bool,
            ((∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) T) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set N := Fintype.card ι
  set k := Nat.log 2 N
  have hk : 1 ≤ k := Nat.log_pos (by decide) hn
  set B := T / k
  have hB : 1 ≤ B := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have hkB : k * B ≤ T := Nat.mul_div_le T k
  have h2k : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨ℓ₀, h01, hspec⟩ := exists_block_stochastic_regret_ge (ι := ι) (k := k) (B := B)
    (T := T) hB hkB h2k
  -- Flatten `Fin k → Fin B → Bool` into `Fin (k * B) → Bool`:
  let flat : (Fin (k * B) → Bool) ≃ (Fin k → Fin B → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool)).symm.trans (Equiv.curry _ _ _)
  refine ⟨k * B, fun w => ℓ₀ (flat w), fun w t i => h01 (flat w) t i, fun H hH => ?_⟩
  obtain ⟨_, hreg⟩ := hspec H hH
  have htr : (𝔼 w : Fin (k * B) → Bool,
      ((∑ t ∈ range T, ∑ i, H (ℓ₀ (flat w)) t i * ℓ₀ (flat w) t i) -
        minCumLoss (ℓ₀ (flat w)) T)) =
      𝔼 c : Fin k → Fin B → Bool,
      ((∑ t ∈ range T, ∑ i, H (ℓ₀ c) t i * ℓ₀ c t i) - minCumLoss (ℓ₀ c) T) :=
    expect_comp_equiv flat
      (fun c => (∑ t ∈ range T, ∑ i, H (ℓ₀ c) t i * ℓ₀ c t i) - minCumLoss (ℓ₀ c) T)
  rw [htr]
  refine le_trans ?_ hreg
  -- Bound `log N ≤ 2 * k` and `T ≤ 2 * (k * B)`:
  have hlogN : log (N : ℝ) ≤ 2 * (k : ℝ) := by
    have hlt : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) N
    have hpow2 : 2 ^ (k + 1) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    have hN_le : (N : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by exact_mod_cast hlt.le.trans hpow2
    have hlog2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc log (N : ℝ) ≤ log ((2 : ℝ) ^ (2 * k)) :=
          log_le_log (Nat.cast_pos.mpr (by omega)) hN_le
      _ = (2 * k : ℕ) * log 2 := log_pow 2 (2 * k)
      _ ≤ (2 * k : ℕ) * 1 := by gcongr
      _ = 2 * (k : ℝ) := by push_cast; ring
  have hT_le : (T : ℝ) ≤ 2 * ((k : ℝ) * B) := by
    have hdiv : T < k * (B + 1) := Nat.lt_mul_div_succ T hk
    have h2 : k * (B + 1) ≤ 2 * (k * B) := by nlinarith
    have hnat : T ≤ 2 * (k * B) := hdiv.le.trans h2
    exact_mod_cast hnat
  have hprod : (T : ℝ) * log (N : ℝ) ≤ 4 * ((k : ℝ) ^ 2 * B) := by
    have hlog0 : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hkB0 : 0 ≤ (k : ℝ) * B := by positivity
    calc (T : ℝ) * log (N : ℝ) ≤ (2 * ((k : ℝ) * B)) * (2 * (k : ℝ)) :=
          mul_le_mul hT_le hlogN hlog0 (by positivity)
      _ = 4 * ((k : ℝ) ^ 2 * B) := by ring
  have hsq : ((1 / (4 * √3)) * √((T : ℝ) * log (N : ℝ))) ^ 2 ≤
      ((k : ℝ) * √((B : ℝ) / 3) / 2) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, sq_sqrt (mul_nonneg (Nat.cast_nonneg T)
      (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))),
      sq_sqrt (by positivity), div_pow, mul_pow, sq_sqrt (by positivity)]
    linarith
  exact le_of_sq_le_sq hsq (by positivity)

/-- **Exercise 4.5 under the printed `T ≥ N` hypothesis** [BlumMansour2007AGT, Exercise 4.5,
p. 101]: since `⌊log₂ N⌋ ≤ N`, `exists_stochastic_regret_ge_sqrt_mul_log` applies whenever
`2 ≤ Fintype.card ι ≤ T`. -/
theorem exists_stochastic_regret_ge_sqrt_mul_log_of_card_le (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Fintype.card ι ≤ T) :
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    ∃ (m : ℕ) (ℓ : (Fin m → Bool) → ℕ → ι → ℝ),
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlg H →
        (1 / (4 * √3)) * √((T : ℝ) * log (Fintype.card ι)) ≤
          𝔼 w : Fin m → Bool,
            ((∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) T) :=
  exists_stochastic_regret_ge_sqrt_mul_log hn ((Nat.log_lt_self 2 (by omega)).le.trans hT)

end Cslib.MachineLearning.OnlineLearning.Experts
