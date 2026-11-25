/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeUpdate
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
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

This module formalizes the four regret lower-bound theorems and Exercise 4.5 of
[BlumMansour2007AGT, §4.3, §4.3.1, §4.3.4, and Exercise 4.5, pp. 82–88, 101] in the experts
setting (`Cslib.MachineLearning.OnlineLearning.Experts`):

* **Causal online algorithms** (`IsOnlineAlgorithm`): in each round `t`, after any `[0, 1]`-valued
  loss history `ℓ 0, …, ℓ (t - 1)`, `H ℓ t` is a probability distribution on `ι` depending only on
  earlier rounds. Guarding the predicate by `[0, 1]` histories matches [BlumMansour2007AGT, §4.2,
  p. 81] and admits every positive multiplicative update (`isOnlineAlgorithm_prob`, including both
  Hedge and Polynomial Weights for `η < 1`) as well as Randomized Greedy
  (`isOnlineAlgorithm_randGreedyProb`).
* **Theorem 4.1 — Dynamic regret against `G_all`** (`exists_dynamic_regret_ge` —
  [BlumMansour2007AGT, §4.3, Theorem 4.1, pp. 82–83]): for every causal online algorithm `H` on
  `N ≥ 1` experts and horizon `T`, there exist a `{0, 1}` loss sequence `ℓ` and an action sequence
  `g : ℕ → ι` with zero cumulative loss such that `H` incurs expected loss at least
  `T * (1 - 1 / N)`.
* **Theorem 4.3 — Deterministic lower bound** (`exists_deterministic_loss_eq_and_minCumLoss_eq` —
  [BlumMansour2007AGT, §4.3.1, Theorem 4.3, pp. 83–84]): for every causal deterministic algorithm
  `D` on `N ≥ 1` experts and horizon `T`, there exists a `{0, 1}` loss sequence `ℓ` on which `D`
  incurs loss `T` while `minCumLoss ℓ T = ⌊T / N⌋` holds with exact equality.
* **Theorem 4.7 — Short-horizon stochastic lower bound (`2 ^ T ≤ N`)**
  (`exists_stochastic_loss_eq_half_minCumLoss_zero` — [BlumMansour2007AGT, §4.3.4, Theorem 4.7,
  pp. 87–88]): whenever `2 ^ T ≤ N` (covering `T < log₂ N` and the boundary `N = 2 ^ T`), there is
  a uniform distribution over `Fin T → Bool` of `{0, 1}` loss sequences such that every realization
  has `minCumLoss (ℓ w) T = 0` while every causal online algorithm `H` has expected loss `T / 2`.
* **Theorem 4.8 — Two-expert `Ω(√T)` stochastic lower bound**
  (`exists_two_experts_stochastic_regret_ge` — [BlumMansour2007AGT, §4.3.4, Theorem 4.8, p. 88]):
  for `N ≥ 2` (in particular `N = 2`) and every `T`, under uniform `Fin T → Bool` `{0, 1}` losses,
  every causal online algorithm incurs expected loss `T / 2` and expected external regret at least
  `(1 / (2 e)) * √T`, proved via Khintchine's `L¹` lower bound
  (`Cslib.BitString.sqrt_sum_sq_le_exp_mul_lpNorm`).
* **Exercise 4.5 — General `Ω(√(T log N))` stochastic lower bound**
  (`exists_stochastic_regret_ge_sqrt_mul_log` — [BlumMansour2007AGT, Exercise 4.5, p. 101]): for
  `N ≥ 2` and `⌊log₂ N⌋ ≤ T` (in particular for all `T ≥ N`, since `⌊log₂ N⌋ ≤ N`), partitioning
  the `T` rounds modulo `k = ⌊log₂ N⌋` into `k` blocks embedded via `2 ^ k ≤ N` experts gives
  expected external regret at least `(1 / (4 e)) * √(T * ln N)` for every causal online algorithm.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.IsOnlineAlgorithm`: causal online experts algorithm
  on `[0, 1]` loss sequences.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.isOnlineAlgorithm_prob`,
  `Cslib.MachineLearning.OnlineLearning.Experts.isOnlineAlgorithm_randGreedyProb`: multiplicative
  updates (positive on `[0, 1]`) and Randomized Greedy are online algorithms.
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_dynamic_regret_ge`: [BlumMansour2007AGT,
  Theorem 4.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_deterministic_loss_eq_and_minCumLoss_eq`:
  [BlumMansour2007AGT, Theorem 4.3].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_loss_eq_half_minCumLoss_zero`:
  [BlumMansour2007AGT, Theorem 4.7].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_two_experts_stochastic_regret_ge`:
  [BlumMansour2007AGT, Theorem 4.8].
* `Cslib.MachineLearning.OnlineLearning.Experts.exists_stochastic_regret_ge_sqrt_mul_log`:
  [BlumMansour2007AGT, Exercise 4.5].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real Cslib.BitString
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ### Causal online algorithms -/

/-- A causal online experts algorithm on `[0, 1]`-valued losses [BlumMansour2007AGT, §4.2, p. 81]:
after any `[0, 1]`-valued history `ℓ 0, …, ℓ (t - 1)`, `H ℓ t` is a probability distribution on `ι`
determined solely by those earlier rounds. -/
structure IsOnlineAlgorithm (H : (ℕ → ι → ℝ) → ℕ → ι → ℝ) : Prop where
  /-- Probabilities are nonnegative after any `[0, 1]`-valued history. -/
  nonneg : ∀ {ℓ : ℕ → ι → ℝ} {t : ℕ},
    (∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) → ∀ i, 0 ≤ H ℓ t i
  /-- Probabilities sum to `1` after any `[0, 1]`-valued history. -/
  sum_eq_one : ∀ {ℓ : ℕ → ι → ℝ} {t : ℕ},
    (∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) → ∑ i, H ℓ t i = 1
  /-- Round-`t` distribution depends only on rounds `< t` for `[0, 1]`-valued histories. -/
  congr : ∀ {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ},
    (∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) → (∀ s < t, ℓ s = ℓ' s) → H ℓ t = H ℓ' t

/-- Every multiplicative update whose factor is positive on `[0, 1]` (in particular Hedge for every
`η` and Polynomial Weights for `η < 1`) is an online algorithm. -/
theorem isOnlineAlgorithm_prob [Nonempty ι] {φ : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < φ x) :
    IsOnlineAlgorithm (prob φ : (ℕ → ι → ℝ) → ℕ → ι → ℝ) where
  nonneg hℓ i := prob_nonneg (fun s hs j => hφ _ (hℓ s hs j)) i
  sum_eq_one hℓ := sum_prob (fun s hs j => hφ _ (hℓ s hs j))
  congr _ h := prob_congr h

/-- Randomized Greedy is an online algorithm. -/
theorem isOnlineAlgorithm_randGreedyProb [Nonempty ι] :
    IsOnlineAlgorithm (randGreedyProb (ι := ι)) where
  nonneg _ i := randGreedyProb_nonneg _ _ i
  sum_eq_one _ := sum_randGreedyProb _ _
  congr _ h := randGreedyProb_congr h

/-! ### Theorem 4.1: Dynamic regret against `G_all` -/

/-- **Dynamic regret lower bound against `G_all`** [BlumMansour2007AGT, Theorem 4.1, pp. 82–83]:
for every causal online algorithm `H` on `N ≥ 1` experts and horizon `T`, there exist a `{0, 1}`
loss sequence `ℓ` and an action sequence `g : ℕ → ι` such that `g` incurs total loss `0` while `H`
incurs expected loss at least `T * (1 - 1 / N)`. -/
theorem exists_dynamic_regret_ge [Nonempty ι] {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ}
    (hH : IsOnlineAlgorithm H) (T : ℕ) :
    ∃ (ℓ : ℕ → ι → ℝ) (g : ℕ → ι),
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∑ t ∈ range T, ℓ t (g t) = 0) ∧
      (T : ℝ) * (1 - 1 / Fintype.card ι) ≤ ∑ t ∈ range T, ∑ i, H ℓ t i * ℓ t i := by
  classical
  let lossOf : ι → ι → ℝ := fun a i => if i = a then 0 else 1
  have hlossOf_mem : ∀ a i, lossOf a i ∈ Set.Icc (0 : ℝ) 1 := fun a i => by
    dsimp only [lossOf]
    split_ifs <;> norm_num
  have hN_ne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Choose `g t` adaptively as an action with probability `≤ 1 / N` given the prefix losses.
  let step : ∀ t : ℕ, (∀ s < t, ι) → ι := fun t prev =>
    let ℓ_pre : ℕ → ι → ℝ := fun s => if hs : s < t then lossOf (prev s hs) else 0
    have hpre_mem : ∀ s < t, ∀ i, ℓ_pre s i ∈ Set.Icc (0 : ℝ) 1 := fun s hs i => by
      simp only [ℓ_pre, hs, ↓reduceDIte]
      exact hlossOf_mem _ i
    have hsum : ∑ i : ι, H ℓ_pre t i ≤ ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) := by
      rw [hH.sum_eq_one hpre_mem, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
        div_self hN_ne]
    (exists_le_of_sum_le univ_nonempty hsum).choose
  let g : ℕ → ι := WellFounded.fix Nat.lt_wfRel.wf step
  let ℓ : ℕ → ι → ℝ := fun t => lossOf (g t)
  have hℓ_mem : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1 := fun t i => hlossOf_mem (g t) i
  have hg_le : ∀ t, H ℓ t (g t) ≤ 1 / Fintype.card ι := fun t => by
    let ℓ_pre : ℕ → ι → ℝ := fun s => if hs : s < t then lossOf (g s) else 0
    have hpre_mem : ∀ s < t, ∀ i, ℓ_pre s i ∈ Set.Icc (0 : ℝ) 1 := fun s hs i => by
      simp only [ℓ_pre, hs, ↓reduceDIte]
      exact hlossOf_mem _ i
    have hcongr : H ℓ t = H ℓ_pre t := hH.congr (fun s _ i => hℓ_mem s i) fun s hs => by
      simp only [ℓ, ℓ_pre, hs, ↓reduceDIte]
    have hsum : ∑ i : ι, H ℓ_pre t i ≤ ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) := by
      rw [hH.sum_eq_one hpre_mem, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
        div_self hN_ne]
    have hg_def : g t = (exists_le_of_sum_le univ_nonempty hsum).choose := by
      dsimp only [g]
      rw [WellFounded.fix_eq]
    rw [hcongr, hg_def]
    exact (exists_le_of_sum_le univ_nonempty hsum).choose_spec.2
  refine ⟨ℓ, g, ?_, ?_, ?_⟩
  · intro t _ i
    dsimp only [ℓ, lossOf]
    split_ifs <;> simp only [or_true, true_or]
  · refine sum_eq_zero fun t _ => ?_
    simp only [ℓ, lossOf, ↓reduceIte]
  · calc (T : ℝ) * (1 - 1 / Fintype.card ι)
        = ∑ _t ∈ range T, (1 - 1 / (Fintype.card ι : ℝ)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ range T, ∑ i, H ℓ t i * ℓ t i := sum_le_sum fun t _ => by
          have h1 := hH.sum_eq_one (ℓ := ℓ) (t := t) fun s _ i => hℓ_mem s i
          have hloss : ∑ i, H ℓ t i * ℓ t i = 1 - H ℓ t (g t) := by
            have hpart : ∑ i, H ℓ t i = H ℓ t (g t) + ∑ i, H ℓ t i * ℓ t i := by
              have hgt : H ℓ t (g t) = ∑ i, if i = g t then H ℓ t i else 0 := by
                simp only [sum_ite_eq', mem_univ, ↓reduceIte]
              rw [hgt, ← sum_add_distrib]
              refine sum_congr rfl fun i _ => ?_
              dsimp only [ℓ, lossOf]
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
    (hD : ∀ {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ},
      (∀ s < t, ∀ i, ℓ s i ∈ Set.Icc (0 : ℝ) 1) → (∀ s < t, ℓ s = ℓ' s) → D ℓ t = D ℓ' t)
    (T : ℕ) :
    ∃ ℓ : ℕ → ι → ℝ,
      (∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∑ t ∈ range T, ℓ t (D ℓ t) = T) ∧
      minCumLoss ℓ T = ((T / Fintype.card ι : ℕ) : ℝ) := by
  classical
  set N := Fintype.card ι
  have hN : 0 < N := Fintype.card_pos
  set k := T / N
  -- Give loss `1` to `D`'s chosen action and to any expert whose remaining slack
  -- `(∑ s < t, nℓ s i) + (T - t)` has dropped to `≤ k`, guaranteeing `minCumLoss ℓ T = k`.
  let step : ∀ t : ℕ, (∀ s < t, ι → Bool) → ι → Bool := fun t prev =>
    let ℓ_pre : ℕ → ι → ℝ := fun s i => if hs : s < t then ((prev s hs i).toNat : ℝ) else 0
    let xt := D ℓ_pre t
    fun i =>
      if i = xt ∨ (∑ s ∈ attach (range t), (prev s.1 (mem_range.mp s.2) i).toNat) + (T - t) ≤ k
      then true else false
  let bℓ : ℕ → ι → Bool := WellFounded.fix Nat.lt_wfRel.wf step
  let nℓ : ℕ → ι → ℕ := fun t i => (bℓ t i).toNat
  let ℓ : ℕ → ι → ℝ := fun t i => (nℓ t i : ℝ)
  have hℓ_mem : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1 := fun t i => by
    dsimp only [ℓ, nℓ]
    cases bℓ t i <;> norm_num
  have hnℓ_eq : ∀ t i, nℓ t i =
      if i = D ℓ t ∨ (∑ s ∈ range t, nℓ s i) + (T - t) ≤ k then 1 else 0 := by
    intro t i
    have hfix : bℓ t = step t (fun s _ => bℓ s) := WellFounded.fix_eq Nat.lt_wfRel.wf step t
    have hD_eq : D (fun s j => if hs : s < t then ((bℓ s j).toNat : ℝ) else 0) t = D ℓ t :=
      hD (fun s hs j => by simp only [hs, ↓reduceDIte]; exact hℓ_mem s j)
        (fun s hs => by funext j; simp only [ℓ, nℓ, hs, ↓reduceDIte])
    have hsum_att : (∑ s ∈ attach (range t), (bℓ s.1 i).toNat) = ∑ s ∈ range t, nℓ s i :=
      sum_attach (range t) fun s => nℓ s i
    have h1 := congrArg Bool.toNat (congrFun hfix i)
    dsimp only [step] at h1
    rw [hD_eq, hsum_att] at h1
    dsimp only [nℓ]
    rw [h1]
    split_ifs <;> rfl
  have hnℓ_le_one : ∀ t i, nℓ t i ≤ 1 := fun t i => by
    rw [hnℓ_eq t i]
    split_ifs <;> omega
  have hslack_ge : ∀ t ≤ T, ∀ i, k ≤ (∑ s ∈ range t, nℓ s i) + (T - t) := by
    intro t ht i
    induction t with
    | zero =>
      simp only [range_zero, sum_empty, zero_add, Nat.sub_zero]
      exact Nat.div_le_self T N
    | succ t ih =>
      have ih' := ih (by omega)
      rw [sum_range_succ, hnℓ_eq t i]
      split_ifs <;> omega
  have hcap_of_trigger : ∀ i, ∀ t₀ < T, (∑ s ∈ range t₀, nℓ s i) + (T - t₀) ≤ k →
      ∑ s ∈ range T, nℓ s i ≤ k := by
    intro i t₀ ht₀ htrig
    have htail : ∑ s ∈ Ico t₀ T, nℓ s i ≤ T - t₀ := by
      calc ∑ s ∈ Ico t₀ T, nℓ s i ≤ ∑ _s ∈ Ico t₀ T, 1 :=
            sum_le_sum fun s _ => hnℓ_le_one s i
        _ = T - t₀ := by simp only [sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
    rw [← sum_range_add_sum_Ico _ ht₀.le]
    omega
  have hex_le_k : ∃ i, ∑ s ∈ range T, nℓ s i ≤ k := by
    by_contra! hgt
    have hno_trig : ∀ i, ∀ t < T, nℓ t i = if i = D ℓ t then 1 else 0 := by
      intro i t ht
      have hnot : ¬ ((∑ s ∈ range t, nℓ s i) + (T - t) ≤ k) :=
        fun htr => not_le_of_gt (hgt i) (hcap_of_trigger i t ht htr)
      rw [hnℓ_eq t i]
      simp only [hnot, or_false]
    have htot : ∑ i : ι, ∑ t ∈ range T, nℓ t i = T := by
      rw [sum_comm]
      calc ∑ t ∈ range T, ∑ i : ι, nℓ t i
          = ∑ t ∈ range T, ∑ i : ι, (if i = D ℓ t then 1 else 0) :=
            sum_congr rfl fun t ht => sum_congr rfl fun i _ => hno_trig i t (mem_range.mp ht)
        _ = T := by
            simp only [sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_range, smul_eq_mul,
              mul_one]
    have hge : N * (k + 1) ≤ ∑ i : ι, ∑ t ∈ range T, nℓ t i := by
      calc N * (k + 1) = ∑ _i : ι, (k + 1) := by
            simp only [sum_const, card_univ, smul_eq_mul, N]
        _ ≤ ∑ i : ι, ∑ t ∈ range T, nℓ t i := sum_le_sum fun i _ => hgt i
    have hlt : T < N * (k + 1) := by
      dsimp only [k]
      have hmod := Nat.div_add_mod T N
      have hrem := Nat.mod_lt T hN
      nlinarith
    omega
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro t _ i
    dsimp only [ℓ, nℓ]
    cases bℓ t i <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
      or_true, true_or]
  · calc ∑ t ∈ range T, ℓ t (D ℓ t) = ∑ _t ∈ range T, (1 : ℝ) :=
          sum_congr rfl fun t _ => by
            dsimp only [ℓ]
            rw [hnℓ_eq t (D ℓ t)]
            simp only [true_or, ↓reduceIte, Nat.cast_one]
      _ = T := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  · apply le_antisymm
    · obtain ⟨i₀, hi₀⟩ := hex_le_k
      refine (minCumLoss_le ℓ T i₀).trans ?_
      dsimp only [ℓ]
      exact_mod_cast hi₀
    · refine le_minCumLoss_iff.mpr fun i => ?_
      have hge := hslack_ge T le_rfl i
      rw [Nat.sub_self, add_zero] at hge
      dsimp only [ℓ]
      exact_mod_cast hge

/-! ### Unified block-map stochastic adversary (Theorems 4.7, 4.8, and Exercise 4.5) -/

/-- `{0, 1}` stochastic loss family parameterized by a block assignment `block : Fin T → κ`, an
embedding `emb : (κ → Bool) ↪ ι`, and one fair coin per round `w : Fin T → Bool`. In round `t < T`,
expert `emb u` pays `0` if `u (block t) = w t` and `1` otherwise; unembedded experts pay `0` if
`w t = true` and `1` otherwise; rounds `t ≥ T` have loss `0`. -/
private noncomputable def coinLoss {κ : Type*} {T : ℕ} (block : Fin T → κ)
    (emb : (κ → Bool) ↪ ι) (w : Fin T → Bool) (t : ℕ) (i : ι) : ℝ :=
  open Classical in
  if ht : t < T then
    if hex : ∃ u : κ → Bool, emb u = i then
      if hex.choose (block ⟨t, ht⟩) = w ⟨t, ht⟩ then 0 else 1
    else
      if w ⟨t, ht⟩ then 0 else 1
  else 0

omit [Fintype ι] in
private theorem coinLoss_binary {κ : Type*} {T : ℕ} (block : Fin T → κ)
    (emb : (κ → Bool) ↪ ι) (w : Fin T → Bool) (t : ℕ) (i : ι) :
    coinLoss block emb w t i = 0 ∨ coinLoss block emb w t i = 1 := by
  classical
  unfold coinLoss
  split_ifs <;> norm_num

omit [Fintype ι] in
private theorem coinLoss_mem_Icc {κ : Type*} {T : ℕ} (block : Fin T → κ)
    (emb : (κ → Bool) ↪ ι) (w : Fin T → Bool) (t : ℕ) (i : ι) :
    coinLoss block emb w t i ∈ Set.Icc (0 : ℝ) 1 := by
  rcases coinLoss_binary block emb w t i with h | h <;> simp only [h, Set.mem_Icc] <;> norm_num

omit [Fintype ι] in
private theorem coinLoss_emb_apply {κ : Type*} {T : ℕ} (block : Fin T → κ)
    (emb : (κ → Bool) ↪ ι) (w : Fin T → Bool) {t : ℕ} (ht : t < T) (u : κ → Bool) :
    coinLoss block emb w t (emb u) = if u (block ⟨t, ht⟩) = w ⟨t, ht⟩ then 0 else 1 := by
  classical
  have hex : ∃ u' : κ → Bool, emb u' = emb u := ⟨u, rfl⟩
  have hchoose : hex.choose = u := emb.injective hex.choose_spec
  unfold coinLoss
  simp only [ht, ↓reduceDIte, hex, hchoose]

/-- Under uniform coins `w : Fin T → Bool`, every causal online algorithm `H` incurs expected total
loss `T / 2`. -/
private theorem expect_coinLoss_eq {κ : Type*} {T : ℕ} (block : Fin T → κ)
    (emb : (κ → Bool) ↪ ι) {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ} (hH : IsOnlineAlgorithm H) :
    (𝔼 w : Fin T → Bool,
      ∑ t ∈ range T, ∑ i, H (coinLoss block emb w) t i * coinLoss block emb w t i) =
      (T : ℝ) / 2 := by
  classical
  rw [expect_sum_comm]
  have hround : ∀ t ∈ range T,
      (𝔼 w : Fin T → Bool,
        ∑ i, H (coinLoss block emb w) t i * coinLoss block emb w t i) = 1 / 2 := by
    intro t ht
    have ht' : t < T := mem_range.mp ht
    let t₀ : Fin T := ⟨t, ht'⟩
    rw [← Fintype.expect_expect_update
      (fun w : Fin T → Bool => ∑ i, H (coinLoss block emb w) t i * coinLoss block emb w t i) t₀]
    have hinner : ∀ w : Fin T → Bool,
        (𝔼 b : Bool, ∑ i, H (coinLoss block emb (Function.update w t₀ b)) t i *
          coinLoss block emb (Function.update w t₀ b) t i) = 1 / 2 := by
      intro w
      have hcongr : ∀ b : Bool,
          H (coinLoss block emb (Function.update w t₀ b)) t = H (coinLoss block emb w) t :=
        fun b => hH.congr (fun s _ i => coinLoss_mem_Icc block emb _ s i) fun s hs => by
          funext i
          have hsT : s < T := lt_trans hs ht'
          have hne : (⟨s, hsT⟩ : Fin T) ≠ t₀ := fun h => hs.ne (congrArg Fin.val h)
          unfold coinLoss
          simp only [hsT, ↓reduceDIte, Function.update_of_ne hne]
      have hsum_loss : ∀ i,
          coinLoss block emb (Function.update w t₀ false) t i +
            coinLoss block emb (Function.update w t₀ true) t i = 1 := by
        intro i
        unfold coinLoss
        simp only [ht', ↓reduceDIte]
        have hf : Function.update w t₀ false ⟨t, ht'⟩ = false := Function.update_self t₀ false w
        have htr : Function.update w t₀ true ⟨t, ht'⟩ = true := Function.update_self t₀ true w
        rw [hf, htr]
        by_cases hex : ∃ u : κ → Bool, emb u = i
        · simp only [hex, ↓reduceDIte]
          cases hex.choose (block t₀) <;> norm_num
        · simp only [hex, ↓reduceDIte]
          norm_num
      rw [Fintype.expect_bool, hcongr false, hcongr true, ← sum_add_distrib]
      simp_rw [← mul_add, hsum_loss, mul_one]
      rw [hH.sum_eq_one fun s _ i => coinLoss_mem_Icc block emb w s i]
    simp only [hinner, Fintype.expect_const]
  rw [sum_congr rfl hround, sum_const, card_range, nsmul_eq_mul]
  ring

omit [Fintype ι] in
/-- Pointwise upper bound on `minCumLoss` under `coinLoss`: the embedded expert matching each
block's majority coin achieves cumulative loss
`T / 2 - (1 / 2) * ∑ r, |∑ t, (if block t = r then 1 else 0) * signVal (w t)|`. -/
private theorem minCumLoss_coinLoss_le [Finite ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {T : ℕ}
    (block : Fin T → κ) (emb : (κ → Bool) ↪ ι) (w : Fin T → Bool) :
    minCumLoss (coinLoss block emb w) T ≤
      (T : ℝ) / 2 -
        (1 / 2) * ∑ r : κ, |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| := by
  let S : κ → Finset (Fin T) := fun r => univ.filter fun t : Fin T => block t = r
  let L_bit : κ → Bool → ℝ := fun r b => ∑ t ∈ S r, if b = w t then 0 else 1
  let u_star : κ → Bool := fun r => if L_bit r false ≤ L_bit r true then false else true
  have hblock_min : ∀ r : κ, L_bit r (u_star r) =
      ((S r).card : ℝ) / 2 -
        (1 / 2) * |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| := by
    intro r
    have hsum : L_bit r false + L_bit r true = (S r).card := by
      dsimp only [L_bit]
      rw [← sum_add_distrib]
      calc ∑ t ∈ S r, ((if false = w t then (0 : ℝ) else 1) + if true = w t then 0 else 1)
          = ∑ _t ∈ S r, (1 : ℝ) := sum_congr rfl fun t _ => by cases w t <;> norm_num
        _ = (S r).card := by simp only [sum_const, nsmul_eq_mul, mul_one]
    have hsign : ∑ t ∈ S r, signVal (w t) =
        ∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t) := by
      simp only [S, ite_mul, one_mul, zero_mul, ← sum_filter]
    have hdiff : |L_bit r false - L_bit r true| =
        |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| := by
      have hsub : L_bit r false - L_bit r true = -∑ t ∈ S r, signVal (w t) := by
        dsimp only [L_bit]
        rw [← sum_sub_distrib, ← sum_neg_distrib]
        refine sum_congr rfl fun t _ => ?_
        cases w t <;> norm_num [signVal]
      rw [hsub, abs_neg, hsign]
    dsimp only [u_star]
    rw [← hdiff]
    by_cases hle : L_bit r false ≤ L_bit r true
    · simp only [hle, ↓reduceIte, abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · simp only [hle, ↓reduceIte, abs_of_pos (sub_pos.mpr (lt_of_not_ge hle))]
      linarith
  have hcards : ∑ r : κ, ((S r).card : ℝ) = T := by
    have hfib := sum_fiberwise_of_maps_to (s := (univ : Finset (Fin T)))
      (t := (univ : Finset κ)) (g := block) (fun _ _ => mem_univ _) (fun _ => (1 : ℝ))
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hfib
    exact hfib
  refine (minCumLoss_le _ T (emb u_star)).trans_eq ?_
  rw [sum_range]
  have hfib := sum_fiberwise_of_maps_to (s := (univ : Finset (Fin T)))
    (t := (univ : Finset κ)) (g := block) (fun _ _ => mem_univ _)
    (fun t : Fin T => coinLoss block emb w t.1 (emb u_star))
  rw [← hfib]
  have hinner : ∀ r : κ,
      ∑ t ∈ S r, coinLoss block emb w t.1 (emb u_star) = L_bit r (u_star r) := by
    intro r
    refine sum_congr rfl fun t ht => ?_
    have hr : block t = r := (mem_filter.mp ht).2
    rw [coinLoss_emb_apply block emb w t.2 u_star, Fin.eta, hr]
  calc ∑ r : κ, ∑ t ∈ S r, coinLoss block emb w t.1 (emb u_star)
      = ∑ r : κ, L_bit r (u_star r) := sum_congr rfl fun r _ => hinner r
    _ = ∑ r : κ, (((S r).card : ℝ) / 2 -
          (1 / 2) * |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)|) :=
        sum_congr rfl fun r _ => hblock_min r
    _ = (T : ℝ) / 2 -
          (1 / 2) * ∑ r : κ,
            |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| := by
        rw [sum_sub_distrib, ← sum_div, hcards, ← mul_sum]

/-- Khintchine expected-regret lower bound for `coinLoss`: each block `r` of size `|S_r|`
contributes at least `√|S_r| / (2 e)` to the expected external regret of every causal online
algorithm `H`. -/
private theorem expect_coinLoss_regret_ge {κ : Type*} [Fintype κ] [DecidableEq κ]
    {T : ℕ} (block : Fin T → κ) (emb : (κ → Bool) ↪ ι) {H : (ℕ → ι → ℝ) → ℕ → ι → ℝ}
    (hH : IsOnlineAlgorithm H) :
    (1 / (2 * Real.exp 1)) * ∑ r : κ, √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) ≤
      𝔼 w : Fin T → Bool,
        ((∑ t ∈ range T, ∑ i, H (coinLoss block emb w) t i * coinLoss block emb w t i) -
          minCumLoss (coinLoss block emb w) T) := by
  have hexp_H := expect_coinLoss_eq block emb hH
  have hexp_diff :
      𝔼 w : Fin T → Bool,
        ((∑ t ∈ range T, ∑ i, H (coinLoss block emb w) t i * coinLoss block emb w t i) -
          minCumLoss (coinLoss block emb w) T) =
      𝔼 w : Fin T → Bool, ((T : ℝ) / 2 - minCumLoss (coinLoss block emb w) T) := by
    rw [expect_sub_distrib, expect_sub_distrib, hexp_H, Fintype.expect_const]
  rw [hexp_diff]
  have hmono :
      𝔼 w : Fin T → Bool,
        ((1 / 2 : ℝ) *
          ∑ r : κ, |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)|) ≤
      𝔼 w : Fin T → Bool, ((T : ℝ) / 2 - minCumLoss (coinLoss block emb w) T) :=
    expect_le_expect fun w _ => by linarith [minCumLoss_coinLoss_le block emb w]
  refine le_trans ?_ hmono
  rw [← mul_expect, expect_sum_comm]
  have hkh : ∀ r : κ,
      √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) / Real.exp 1 ≤
        𝔼 w : Fin T → Bool,
          |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| := by
    intro r
    let a : Fin T → ℝ := fun t => if block t = r then 1 else 0
    have hsum_sq : ∑ t : Fin T, a t ^ 2 =
        ((univ.filter fun t : Fin T => block t = r).card : ℝ) := by
      have hsq : ∀ t : Fin T, a t ^ 2 = if block t = r then (1 : ℝ) else 0 := fun t => by
        dsimp only [a]
        split_ifs <;> norm_num
      simp only [hsq, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have h := sqrt_sum_sq_le_exp_mul_lpNorm (p := 1) one_pos one_le_two a
    rw [show (2 : ℝ) / 1 - 1 = 1 by norm_num, lpNorm_one, hsum_sq] at h
    exact (div_le_iff₀' (Real.exp_pos 1)).mpr h
  calc (1 / (2 * Real.exp 1)) *
        ∑ r : κ, √(((univ.filter fun t : Fin T => block t = r).card : ℝ))
      = (1 / 2) * ∑ r : κ,
          √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) / Real.exp 1 := by
        rw [← sum_div]
        ring
    _ ≤ (1 / 2) * ∑ r : κ,
          𝔼 w : Fin T → Bool,
            |∑ t : Fin T, (if block t = r then (1 : ℝ) else 0) * signVal (w t)| :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hkh r) (by norm_num)

/-! ### Theorems 4.7, 4.8, and Exercise 4.5 -/

/-- **Short-horizon stochastic lower bound (`2 ^ T ≤ N`)** [BlumMansour2007AGT, Theorem 4.7,
pp. 87–88]: whenever `2 ^ T ≤ Fintype.card ι` (in particular for all `T < log₂ N`), there is a
uniform `{0, 1}` loss family over `Fin T → Bool` such that every realization satisfies
`minCumLoss (ℓ w) T = 0` while every causal online algorithm `H` incurs expected loss `T / 2`. -/
theorem exists_stochastic_loss_eq_half_minCumLoss_zero {T : ℕ}
    (hTN : 2 ^ T ≤ Fintype.card ι) :
    ∃ ℓ : (Fin T → Bool) → ℕ → ι → ℝ,
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      (∀ w, minCumLoss (ℓ w) T = 0) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlgorithm H →
        (𝔼 w : Fin T → Bool, ∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) = (T : ℝ) / 2 := by
  have hcard : Fintype.card (Fin T → Bool) ≤ Fintype.card ι := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hTN
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨coinLoss id emb, coinLoss_binary id emb, ?_,
    fun H hH => expect_coinLoss_eq id emb hH⟩
  intro w
  apply le_antisymm
  · refine (minCumLoss_le _ T (emb w)).trans_eq ?_
    refine sum_eq_zero fun t ht => ?_
    rw [coinLoss_emb_apply id emb w (mem_range.mp ht) w]
    simp only [id_eq, ↓reduceIte]
  · exact minCumLoss_nonneg fun s _ i => (coinLoss_mem_Icc id emb w s i).1

/-- **Two-expert `Ω(√T)` stochastic external-regret lower bound**
[BlumMansour2007AGT, Theorem 4.8, p. 88]: for `N ≥ 2` experts (in particular `N = 2`) and any
horizon `T`, under uniform fair-coin `{0, 1}` losses `w : Fin T → Bool`, every causal online
algorithm `H` incurs expected loss `T / 2` and expected external regret at least
`(1 / (2 e)) * √T`. -/
theorem exists_two_experts_stochastic_regret_ge (hn : 2 ≤ Fintype.card ι) (T : ℕ) :
    ∃ ℓ : (Fin T → Bool) → ℕ → ι → ℝ,
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlgorithm H →
        (𝔼 w : Fin T → Bool, ∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) = (T : ℝ) / 2 ∧
        (1 / (2 * Real.exp 1)) * √(T : ℝ) ≤
          𝔼 w : Fin T → Bool,
            ((∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) T) := by
  have hcard : Fintype.card (Unit → Bool) ≤ Fintype.card ι := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_unit, pow_one] using hn
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨coinLoss (fun _ : Fin T => ()) emb, coinLoss_binary _ emb, fun H hH => ?_⟩
  refine ⟨expect_coinLoss_eq _ emb hH, ?_⟩
  have h := expect_coinLoss_regret_ge (fun _ : Fin T => ()) emb hH
  simpa only [Fintype.sum_unique, filter_true, card_univ, Fintype.card_fin] using h

/-- **General `Ω(√(T log N))` stochastic external-regret lower bound**
[BlumMansour2007AGT, Exercise 4.5, p. 101]: for `N ≥ 2` experts and `⌊log₂ N⌋ ≤ T` (in particular
for all `T ≥ N`, since `⌊log₂ N⌋ ≤ N`), there exists a uniform `{0, 1}` loss family over
`Fin T → Bool` under which every causal online algorithm incurs expected external regret at least
`(1 / (4 e)) * √(T * ln N)`. -/
theorem exists_stochastic_regret_ge_sqrt_mul_log (hn : 2 ≤ Fintype.card ι) {T : ℕ}
    (hT : Nat.log 2 (Fintype.card ι) ≤ T) :
    ∃ ℓ : (Fin T → Bool) → ℕ → ι → ℝ,
      (∀ w t i, ℓ w t i = 0 ∨ ℓ w t i = 1) ∧
      ∀ H : (ℕ → ι → ℝ) → ℕ → ι → ℝ, IsOnlineAlgorithm H →
        (1 / (4 * Real.exp 1)) * √((T : ℝ) * log (Fintype.card ι)) ≤
          𝔼 w : Fin T → Bool,
            ((∑ t ∈ range T, ∑ i, H (ℓ w) t i * ℓ w t i) - minCumLoss (ℓ w) T) := by
  set N := Fintype.card ι
  set k := Nat.log 2 N
  have hk : 1 ≤ k := Nat.log_pos (by decide) hn
  set B := T / k
  have hB : 1 ≤ B := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have h2k : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hcard : Fintype.card (Fin k → Bool) ≤ Fintype.card ι := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h2k
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  let block : Fin T → Fin k := fun t => ⟨t.1 % k, Nat.mod_lt t.1 hk⟩
  refine ⟨coinLoss block emb, coinLoss_binary block emb, fun H hH => ?_⟩
  have hreg := expect_coinLoss_regret_ge block emb hH
  refine le_trans ?_ hreg
  -- Each residue class mod `k` in `Fin T` contains at least `B = T / k` rounds.
  have hfiber : ∀ r : Fin k, B ≤ (univ.filter fun t : Fin T => block t = r).card := by
    intro r
    let f : Fin B → Fin T := fun q => ⟨q.1 * k + r.1, by
      have h1 : q.1 * k + r.1 < (q.1 + 1) * k := by nlinarith [r.2]
      have h2 : (q.1 + 1) * k ≤ B * k := Nat.mul_le_mul_right k q.2
      have h3 : B * k ≤ T := Nat.div_mul_le_self T k
      omega⟩
    have hf_inj : Function.Injective f := by
      intro q₁ q₂ hq
      have hv : q₁.1 * k + r.1 = q₂.1 * k + r.1 := congrArg Fin.val hq
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hk (Nat.add_right_cancel hv))
    have hf_mem : univ.image f ⊆ univ.filter fun t : Fin T => block t = r := by
      intro t ht
      obtain ⟨q, -, rfl⟩ := mem_image.mp ht
      simp only [mem_filter, mem_univ, true_and, block, f]
      exact Fin.ext (by dsimp only; rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.2])
    calc B = (univ.image f).card := by rw [card_image_of_injective _ hf_inj, card_univ,
          Fintype.card_fin]
      _ ≤ (univ.filter fun t : Fin T => block t = r).card := card_le_card hf_mem
  have hsum_sqrt : (k : ℝ) * √(B : ℝ) ≤
      ∑ r : Fin k, √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) := by
    calc (k : ℝ) * √(B : ℝ) = ∑ _r : Fin k, √(B : ℝ) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ r : Fin k, √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) :=
          sum_le_sum fun r _ => sqrt_le_sqrt (Nat.cast_le.mpr (hfiber r))
  -- Bound `log N ≤ 2 k` and `T ≤ 2 k B`, so `√(T log N) ≤ 2 k √B`.
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
    exact_mod_cast hdiv.le.trans h2
  have hlog0 : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hprod : (T : ℝ) * log (N : ℝ) ≤ 4 * ((k : ℝ) ^ 2 * B) := by
    calc (T : ℝ) * log (N : ℝ) ≤ (2 * ((k : ℝ) * B)) * (2 * (k : ℝ)) :=
          mul_le_mul hT_le hlogN hlog0 (by positivity)
      _ = 4 * ((k : ℝ) ^ 2 * B) := by ring
  have hsqrt : √((T : ℝ) * log (N : ℝ)) ≤ 2 * ((k : ℝ) * √(B : ℝ)) := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [sq_sqrt (mul_nonneg (Nat.cast_nonneg T) hlog0), mul_pow, mul_pow,
      sq_sqrt (Nat.cast_nonneg B)]
    linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  calc (1 / (4 * Real.exp 1)) * √((T : ℝ) * log (N : ℝ))
      ≤ (1 / (4 * Real.exp 1)) * (2 * ((k : ℝ) * √(B : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (1 / (2 * Real.exp 1)) * ((k : ℝ) * √(B : ℝ)) := by ring
    _ ≤ (1 / (2 * Real.exp 1)) *
          ∑ r : Fin k, √(((univ.filter fun t : Fin T => block t = r).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_sqrt (by positivity)

end Cslib.MachineLearning.OnlineLearning.Experts
