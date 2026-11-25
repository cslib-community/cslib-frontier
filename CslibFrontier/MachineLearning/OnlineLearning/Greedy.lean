/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import CslibFrontier.Foundations.NumberTheory.Harmonic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Greedy and randomized greedy algorithms for learning with experts

This module formalizes the warmup external-regret algorithms of [BlumMansour2007AGT, §4.3.1,
pp. 83–84] in the experts setting (`Cslib.MachineLearning.OnlineLearning.Experts`):

* **Best cumulative loss and leaders** (`minCumLoss`, `leaders`): `minCumLoss ℓ t` is the
  minimum cumulative loss `⨅ i, ∑ s ∈ range t, ℓ s i` before round `t` (`L_min^t`), and
  `leaders ℓ t` is the set of actions attaining `minCumLoss ℓ t` (`S^{t-1}`).
* **Deterministic Greedy / Follow-the-Leader** (`greedyPlay`, `greedy_loss_le`,
  `greedyPlay_loss_le` — [BlumMansour2007AGT, Theorem 4.2, p. 83]): any sequence choosing
  `x t ∈ leaders ℓ t` (in particular `greedyPlay`, which breaks ties by a linear order on `ι`)
  satisfies `∑ t ∈ range T, ℓ t (x t) ≤ N * minCumLoss ℓ T + (N - 1)` for every `[0, 1]`-valued
  loss sequence (in particular for `{0, 1}` losses). The proof uses the bounded window potential
  `∑ i, max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i)` instead of the discrete leader-count
  invariant so that it covers real `[0, 1]` losses directly. Note that choosing a leader in every
  round is follow-the-leader (`OCO.IsFTRL Set.univ 0 ℓ x`); the finite-action counting bound here
  applies with zero regularizer, where the strongly convex `FTRL` bounds do not.
* **Randomized Greedy** (`randGreedyProb`, `randGreedy_loss_le_harmonic`, `randGreedy_loss_le_log`
  — [BlumMansour2007AGT, Theorem 4.4, p. 84]): `randGreedyProb ℓ t` plays the uniform distribution
  on `leaders ℓ t`. On `{0, 1}` loss sequences, the harmonic invariant
  `L_RG^T ≤ (H_N - H_{|S^T|}) + H_N * L_min^T` (`randGreedy_loss_le_harmonic`) yields
  `L_RG^T ≤ ln N + (1 + ln N) * L_min^T` (`randGreedy_loss_le_log`). Unlike Theorem 4.2, exact-tie
  `randGreedyProb` requires `{0, 1}` losses: arbitrarily small `[0, 1]` perturbations can keep
  `|leaders ℓ t| = 1` in every round and force deterministic-greedy loss `N * L_min`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.minCumLoss`: minimum cumulative loss `L_min^t`.
* `Cslib.MachineLearning.OnlineLearning.Experts.leaders`: set of current minimum-loss leaders.
* `Cslib.MachineLearning.OnlineLearning.Experts.greedyPlay`: deterministic Greedy (FTL) action
  selection breaking ties by a linear order.
* `Cslib.MachineLearning.OnlineLearning.Experts.randGreedyProb`: Randomized Greedy uniform
  distribution on `leaders ℓ t`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.greedy_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.greedyPlay_loss_le`: [BlumMansour2007AGT,
  Theorem 4.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_harmonic`,
  `Cslib.MachineLearning.OnlineLearning.Experts.randGreedy_loss_le_log`: [BlumMansour2007AGT,
  Theorem 4.4].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*}

/-! ### Minimum cumulative loss and leaders -/

/-- Minimum cumulative loss `⨅ i, ∑ s ∈ range t, ℓ s i` before round `t` (`L_min^t`). -/
noncomputable def minCumLoss (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ⨅ i, ∑ s ∈ range t, ℓ s i

@[simp] theorem minCumLoss_zero (ℓ : ℕ → ι → ℝ) : minCumLoss ℓ 0 = 0 := by
  simp only [minCumLoss, range_zero, sum_empty, Real.iInf_const_zero]

theorem minCumLoss_le [Finite ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    minCumLoss ℓ t ≤ ∑ s ∈ range t, ℓ s i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem le_minCumLoss_iff [Finite ι] [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {c : ℝ} :
    c ≤ minCumLoss ℓ t ↔ ∀ i, c ≤ ∑ s ∈ range t, ℓ s i :=
  le_ciInf_iff (Set.finite_range _).bddBelow

theorem exists_sum_eq_minCumLoss [Finite ι] [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∃ i, ∑ s ∈ range t, ℓ s i = minCumLoss ℓ t :=
  exists_eq_ciInf_of_finite

theorem minCumLoss_nonneg {ℓ : ℕ → ι → ℝ} {t : ℕ} (hℓ : ∀ s < t, ∀ i, 0 ≤ ℓ s i) :
    0 ≤ minCumLoss ℓ t :=
  Real.iInf_nonneg fun i => sum_nonneg fun s hs => hℓ s (mem_range.mp hs) i

theorem minCumLoss_mono_succ [Finite ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} (hℓ : ∀ i, 0 ≤ ℓ t i) :
    minCumLoss ℓ t ≤ minCumLoss ℓ (t + 1) := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp only [minCumLoss, Real.iInf_of_isEmpty, le_rfl]
  · refine le_minCumLoss_iff.mpr fun i => ?_
    rw [sum_range_succ]
    linarith [minCumLoss_le ℓ t i, hℓ i]

theorem minCumLoss_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    minCumLoss ℓ t = minCumLoss ℓ' t := by
  unfold minCumLoss
  congr 1
  funext i
  exact sum_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]

variable [Fintype ι]

/-- The set `S^t` of current minimum-cumulative-loss leaders before round `t`. -/
noncomputable def leaders (ℓ : ℕ → ι → ℝ) (t : ℕ) : Finset ι :=
  open Classical in
  univ.filter fun i => ∑ s ∈ range t, ℓ s i = minCumLoss ℓ t

theorem mem_leaders {ℓ : ℕ → ι → ℝ} {t : ℕ} {i : ι} :
    i ∈ leaders ℓ t ↔ ∑ s ∈ range t, ℓ s i = minCumLoss ℓ t := by
  classical
  simp only [leaders, mem_filter, mem_univ, true_and]

theorem leaders_nonempty [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : (leaders ℓ t).Nonempty := by
  obtain ⟨i, hi⟩ := exists_sum_eq_minCumLoss ℓ t
  exact ⟨i, mem_leaders.mpr hi⟩

@[simp] theorem leaders_zero (ℓ : ℕ → ι → ℝ) : leaders ℓ 0 = univ := by
  ext i
  simp only [mem_leaders, range_zero, sum_empty, minCumLoss_zero, mem_univ]

theorem leaders_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    leaders ℓ t = leaders ℓ' t := by
  ext i
  have hsum : ∑ s ∈ range t, ℓ s i = ∑ s ∈ range t, ℓ' s i :=
    sum_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]
  simp only [mem_leaders, hsum, minCumLoss_congr h]

/-! ### Deterministic Greedy (Follow-the-Leader) and Theorem 4.2 -/

/-- **Deterministic Greedy (Follow-the-Leader)** [BlumMansour2007AGT, §4.3.1, p. 83]: in round `t`,
select the minimum-index action among `leaders ℓ t`. -/
noncomputable def greedyPlay [Nonempty ι] [LinearOrder ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι :=
  (leaders ℓ t).min' (leaders_nonempty ℓ t)

theorem greedyPlay_mem_leaders [Nonempty ι] [LinearOrder ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    greedyPlay ℓ t ∈ leaders ℓ t :=
  min'_mem _ _

theorem greedyPlay_le [Nonempty ι] [LinearOrder ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {i : ι}
    (hi : i ∈ leaders ℓ t) : greedyPlay ℓ t ≤ i :=
  min'_le _ _ hi

theorem greedyPlay_congr [Nonempty ι] [LinearOrder ι] {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) : greedyPlay ℓ t = greedyPlay ℓ' t := by
  simp only [greedyPlay, leaders_congr h]

/-- Window potential `∑ i, max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i)` for the `[0, 1]`
Greedy analysis. -/
private noncomputable def greedyPotential (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i)

private theorem greedyPotential_zero (ℓ : ℕ → ι → ℝ) :
    greedyPotential ℓ 0 = Fintype.card ι := by
  simp only [greedyPotential, minCumLoss_zero, range_zero, sum_empty, add_zero, sub_zero,
    max_eq_right zero_le_one, sum_const, card_univ, nsmul_eq_mul, mul_one]

private theorem one_le_greedyPotential [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    1 ≤ greedyPotential ℓ t := by
  obtain ⟨i₀, hi₀⟩ := exists_sum_eq_minCumLoss ℓ t
  calc (1 : ℝ) = max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i₀) := by
        rw [hi₀, add_sub_cancel_right, max_eq_right zero_le_one]
    _ ≤ greedyPotential ℓ t :=
        single_le_sum (f := fun j => max (0 : ℝ) (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s j))
          (fun j _ => le_max_left (0 : ℝ) _) (mem_univ i₀)

private theorem greedyPotential_step [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ} {x : ι}
    (hx : x ∈ leaders ℓ t) (hℓ : ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) :
    ℓ t x + greedyPotential ℓ (t + 1) - greedyPotential ℓ t ≤
      Fintype.card ι * (minCumLoss ℓ (t + 1) - minCumLoss ℓ t) := by
  classical
  have hx_eq : ∑ s ∈ range t, ℓ s x = minCumLoss ℓ t := mem_leaders.mp hx
  set Δm := minCumLoss ℓ (t + 1) - minCumLoss ℓ t
  have hΔm_nn : 0 ≤ Δm := sub_nonneg.mpr (minCumLoss_mono_succ fun i => (hℓ i).1)
  have hterm_x : max 0 (1 + minCumLoss ℓ (t + 1) - ∑ s ∈ range (t + 1), ℓ s x) -
      max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s x) = Δm - ℓ t x := by
    have h0 : 0 ≤ 1 + minCumLoss ℓ (t + 1) - ∑ s ∈ range (t + 1), ℓ s x := by
      rw [sum_range_succ, hx_eq]
      linarith [(hℓ x).2]
    rw [max_eq_right h0, hx_eq, add_sub_cancel_right, max_eq_right zero_le_one, sum_range_succ,
      hx_eq]
    ring
  have hterm_other (i : ι) : max 0 (1 + minCumLoss ℓ (t + 1) - ∑ s ∈ range (t + 1), ℓ s i) -
      max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i) ≤ Δm := by
    rw [sum_range_succ]
    refine sub_le_iff_le_add'.mpr (max_le ?_ ?_)
    · linarith [le_max_left 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i)]
    · linarith [le_max_right 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i), (hℓ i).1]
  unfold greedyPotential
  rw [add_sub_assoc, ← sum_sub_distrib, ← add_sum_erase _ _ (mem_univ x), hterm_x]
  have herase : ∑ i ∈ univ.erase x,
      (max 0 (1 + minCumLoss ℓ (t + 1) - ∑ s ∈ range (t + 1), ℓ s i) -
        max 0 (1 + minCumLoss ℓ t - ∑ s ∈ range t, ℓ s i)) ≤ ((Fintype.card ι : ℝ) - 1) * Δm :=
    calc ∑ i ∈ univ.erase x, _ ≤ ∑ _i ∈ univ.erase x, Δm :=
          sum_le_sum fun i _ => hterm_other i
      _ = ((univ.erase x).card : ℝ) * Δm := by rw [sum_const, nsmul_eq_mul]
      _ = ((Fintype.card ι : ℝ) - 1) * Δm := by
          rw [card_erase_of_mem (mem_univ x), card_univ,
            Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card ι), Nat.cast_one]
  linarith

/-- **Greedy external-regret bound** [BlumMansour2007AGT, Theorem 4.2, p. 83]: for any tie-breaking
sequence `x` selecting `x t ∈ leaders ℓ t` and any `[0, 1]`-valued loss sequence `ℓ` (in particular
any `{0, 1}` loss sequence), the Greedy learner's total loss satisfies
`∑ t ∈ range T, ℓ t (x t) ≤ N * minCumLoss ℓ T + (N - 1)`. -/
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
noncomputable def randGreedyProb (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  open Classical in
  if i ∈ leaders ℓ t then 1 / (leaders ℓ t).card else 0

theorem randGreedyProb_of_mem {ℓ : ℕ → ι → ℝ} {t : ℕ} {i : ι} (hi : i ∈ leaders ℓ t) :
    randGreedyProb ℓ t i = 1 / (leaders ℓ t).card := by
  unfold randGreedyProb
  simp only [hi, ↓reduceIte]

theorem randGreedyProb_of_notMem {ℓ : ℕ → ι → ℝ} {t : ℕ} {i : ι} (hi : i ∉ leaders ℓ t) :
    randGreedyProb ℓ t i = 0 := by
  unfold randGreedyProb
  simp only [hi, ↓reduceIte]

theorem randGreedyProb_nonneg (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ randGreedyProb ℓ t i := by
  unfold randGreedyProb
  split_ifs <;> positivity

theorem sum_randGreedyProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, randGreedyProb ℓ t i = 1 := by
  classical
  have hpos : (0 : ℝ) < (leaders ℓ t).card := Nat.cast_pos.mpr (leaders_nonempty ℓ t).card_pos
  simp only [randGreedyProb, ← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  field_simp

theorem randGreedyProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    randGreedyProb ℓ t = randGreedyProb ℓ' t := by
  funext i
  have hl := leaders_congr h
  unfold randGreedyProb
  rw [hl]

omit [Fintype ι] in
private theorem sum_nat_of_binary {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ s < t, ∀ i, ℓ s i = 0 ∨ ℓ s i = 1) (i : ι) :
    ∃ n : ℕ, ∑ s ∈ range t, ℓ s i = n := by
  induction t with
  | zero => exact ⟨0, by simp only [range_zero, sum_empty, Nat.cast_zero]⟩
  | succ t ih =>
    obtain ⟨n, hn⟩ := ih fun s hs => hℓ s (by omega)
    rcases hℓ t (by omega) i with h0 | h1
    · exact ⟨n, by rw [sum_range_succ, hn, h0, add_zero]⟩
    · exact ⟨n + 1, by rw [sum_range_succ, hn, h1]; push_cast; ring⟩

private theorem add_one_le_sum_of_notMem_leaders [Nonempty ι] {ℓ : ℕ → ι → ℝ} {t : ℕ}
    (hℓ : ∀ s < t, ∀ i, ℓ s i = 0 ∨ ℓ s i = 1) {i : ι} (hi : i ∉ leaders ℓ t) :
    minCumLoss ℓ t + 1 ≤ ∑ s ∈ range t, ℓ s i := by
  obtain ⟨j, hj⟩ := exists_sum_eq_minCumLoss ℓ t
  obtain ⟨ni, hni⟩ := sum_nat_of_binary hℓ i
  obtain ⟨nj, hnj⟩ := sum_nat_of_binary hℓ j
  have hle : ∑ s ∈ range t, ℓ s j ≤ ∑ s ∈ range t, ℓ s i := hj.trans_le (minCumLoss_le ℓ t i)
  have hne : ∑ s ∈ range t, ℓ s i ≠ minCumLoss ℓ t := mt mem_leaders.mpr hi
  rw [← hj] at hne ⊢
  rw [hni, hnj] at hle hne ⊢
  have hlt : nj < ni := lt_of_le_of_ne (by exact_mod_cast hle) (fun h => hne (by rw [h]))
  exact_mod_cast hlt

/-- **Harmonic invariant for Randomized Greedy** [BlumMansour2007AGT, proof of Theorem 4.4, p. 84]:
on `{0, 1}` loss sequences,
`L_RG^T ≤ (H_N - H_{|S^T|}) + H_N * L_min^T`. -/
theorem randGreedy_loss_le_harmonic [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
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
      simp only [randGreedyProb, S, ite_mul, zero_mul, ← sum_filter, filter_mem_eq_inter,
        univ_inter, one_div, inv_mul_eq_div, ← sum_div]
      congr 1
      have hpart := sum_filter_add_sum_filter_not S (fun i => ℓ t i = 0) (fun _ => (1 : ℝ))
      simp only [sum_const, nsmul_eq_mul, mul_one] at hpart
      have hsum1 : ∑ i ∈ S, ℓ t i = (S.filter fun i => ¬ ℓ t i = 0).card :=
        calc ∑ i ∈ S, ℓ t i = ∑ i ∈ S, if ¬ ℓ t i = 0 then (1 : ℝ) else 0 :=
              sum_congr rfl fun i _ => by rcases hℓ_t i with h | h <;> simp [h]
          _ = (S.filter fun i => ¬ ℓ t i = 0).card := by
              simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [hsum1]
      linarith
    rw [sum_range_succ, hstep_loss]
    have hℓ_nn (i : ι) : 0 ≤ ℓ t i := by rcases hℓ_t i with h | h <;> linarith
    by_cases hA : A.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hA
      have hm_eq : minCumLoss ℓ (t + 1) = minCumLoss ℓ t := by
        refine le_antisymm ?_ (minCumLoss_mono_succ hℓ_nn)
        calc minCumLoss ℓ (t + 1) ≤ ∑ s ∈ range (t + 1), ℓ s i₀ := minCumLoss_le ℓ (t + 1) i₀
          _ = minCumLoss ℓ t := by
            rw [sum_range_succ, mem_leaders.mp (mem_filter.mp hi₀).1, (mem_filter.mp hi₀).2,
              add_zero]
      have hS'_eq : S' = A := by
        ext i
        simp only [S', mem_leaders, hm_eq, A, mem_filter, S, sum_range_succ]
        refine ⟨fun hi => ?_, fun ⟨hi1, hi2⟩ => by linarith⟩
        by_cases hmem : i ∈ leaders ℓ t
        · exact ⟨mem_leaders.mp hmem, by linarith [mem_leaders.mp hmem]⟩
        · linarith [add_one_le_sum_of_notMem_leaders hℓ_prev hmem, hℓ_nn i]
      have hharm :
          ((S.card : ℝ) - S'.card) / S.card ≤ (harmonic S.card : ℝ) - harmonic S'.card := by
        have hq : ((((S.card : ℚ) - S'.card) / S.card : ℚ) : ℝ) ≤
            ((harmonic S.card - harmonic S'.card : ℚ) : ℝ) := by
          exact_mod_cast sub_div_le_harmonic_sub (show S'.card ≤ S.card from
            hS'_eq ▸ card_filter_le S _)
        push_cast at hq
        exact hq
      rw [hm_eq, ← hS'_eq]
      linarith
    · have hA1 (i : ι) (hi : i ∈ S) : ℓ t i = 1 :=
        (hℓ_t i).resolve_left fun h0 => hA ⟨i, mem_filter.mpr ⟨hi, h0⟩⟩
      rw [not_nonempty_iff_eq_empty.mp hA, card_empty, Nat.cast_zero, sub_zero,
        div_self hS_pos.ne']
      obtain ⟨i₀, hi₀⟩ := hS_ne
      have hm_eq : minCumLoss ℓ (t + 1) = minCumLoss ℓ t + 1 := by
        refine le_antisymm ?_ (le_minCumLoss_iff.mpr fun i => ?_)
        · calc minCumLoss ℓ (t + 1) ≤ ∑ s ∈ range (t + 1), ℓ s i₀ := minCumLoss_le ℓ (t + 1) i₀
            _ = minCumLoss ℓ t + 1 := by rw [sum_range_succ, mem_leaders.mp hi₀, hA1 i₀ hi₀]
        · rw [sum_range_succ]
          by_cases hmem : i ∈ S
          · rw [mem_leaders.mp hmem, hA1 i hmem]
          · linarith [add_one_le_sum_of_notMem_leaders hℓ_prev hmem, hℓ_nn i]
      have h1_le_HS : (1 : ℝ) ≤ harmonic S.card := by
        exact_mod_cast one_le_harmonic (card_pos.mpr ⟨i₀, hi₀⟩).ne'
      have hHS'_le : (harmonic S'.card : ℝ) ≤ harmonic (Fintype.card ι) := by
        exact_mod_cast harmonic_mono (card_le_univ S')
      rw [hm_eq, mul_add, mul_one]
      linarith

/-- **Logarithmic bound for Randomized Greedy** [BlumMansour2007AGT, Theorem 4.4, p. 84]: on
`{0, 1}` loss sequences, `L_RG^T ≤ ln N + (1 + ln N) * L_min^T`. -/
theorem randGreedy_loss_le_log [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i = 0 ∨ ℓ t i = 1) :
    ∑ t ∈ range T, ∑ i, randGreedyProb ℓ t i * ℓ t i ≤
      log (Fintype.card ι) + (1 + log (Fintype.card ι)) * minCumLoss ℓ T := by
  have h := randGreedy_loss_le_harmonic hℓ
  have h1 : (1 : ℝ) ≤ harmonic (leaders ℓ T).card := by
    exact_mod_cast one_le_harmonic (leaders_nonempty ℓ T).card_pos.ne'
  have hlog : (harmonic (Fintype.card ι) : ℝ) ≤ 1 + log (Fintype.card ι) :=
    harmonic_le_one_add_log (Fintype.card ι)
  have hm_nn : 0 ≤ minCumLoss ℓ T :=
    minCumLoss_nonneg fun s hs i => by rcases hℓ s hs i with h0 | h1 <;> linarith
  nlinarith

end Cslib.MachineLearning.OnlineLearning.Experts
