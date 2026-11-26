/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.ZeroSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Lattice

/-!
# External regret in constant-sum games and the online-learning minimax proof

This module formalizes [BlumMansour2007AGT, §4.4.1–§4.4.2, pp. 88–90], reusing
`Cslib.Probability.IsMinimaxValue` and `Cslib.MachineLearning.OnlineLearning.Experts.averageProb`
from `ZeroSum.lean`:

* **Value duality in constant-sum games** (`isMinimaxValue_swap_of_add_eq` —
  [BlumMansour2007AGT, §4.4.2, p. 89]):
  If two players' loss matrices `s₁, s₂ : I → J → ℝ` satisfy `∀ i j, s₁ i j + s₂ i j = c` and `s₁`
  has minimax value `v₁`, then player 2's transposed loss matrix `Function.swap s₂` has minimax
  value `c - v₁`.
* **Theorem 4.9 — Average loss against an arbitrary opponent**
  (`average_loss_le_of_isMinimaxValue`, `constantSum_col_average_loss_le`,
  `constantSum_average_loss_mem_Icc` — [BlumMansour2007AGT, §4.4.2, Theorem 4.9, p. 89]):
  In any finite matrix game `M` with minimax value `v`, a row learner achieving external regret at
  most `R` over `T > 0` rounds incurs average expected loss at most `v + R / T` against *every*
  sequence `q` of mixed opponent strategies (not only best-response play). Symmetrically, in a
  constant-sum game `s₁ + s₂ = c`, a column learner with external regret at most `R` incurs average
  expected loss at most `(c - v₁) + R / T`, and when both players achieve external regrets `R₁` and
  `R₂` simultaneously, player 1's average expected loss lies in `[v₁ - R₂ / T, v₁ + R₁ / T]`.
* **§4.4.2 — Coupled no-regret proof of von Neumann's minimax theorem**
  (`ciSup_ciInf_eq_ciInf_ciSup`, `isMinimaxValue_ciInf_ciSup` — [BlumMansour2007AGT, §4.4.2,
  pp. 89–90]):
  Running two horizon-`T` multiplicative-weights learners (`mw_regret_le_sqrt_of_mem_Icc`)
  simultaneously against each other on `M` affine-rescaled into `[0, 1]` bounds the gap between
  `v_max^1 = ⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j` and
  `v_min^1 = ⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j` by `O(1 / √T)` for every
  `T ≥ 1`, proving `v_min^1 = v_max^1` (`ciSup_ciInf_eq_ciInf_ciSup`) and, via compactness of
  `StdSimplex ℝ`, `IsMinimaxValue M v_max^1` (`isMinimaxValue_ciInf_ciSup`) without invoking
  `exists_isMinimaxValue` or Sion's theorem.
  *(Source note: the displayed formulas on [BlumMansour2007AGT, p. 89] transpose the outer and
  inner `min`/`max` operators in both `v_min^1` and `v_max^1`, writing `min_{x_1} max_z` and
  `max_{x_2} min_z`; the prose definitions immediately following on p. 89 and the proof on p. 90 use
  `v_min^1 = max_{z ∈ Δ(X_2)} min_{x_1 ∈ X_1} E_{x_2 ~ z}[s_1(x_1, x_2)]` and
  `v_max^1 = min_{z ∈ Δ(X_1)} max_{x_2 ∈ X_2} E_{x_1 ~ z}[s_1(x_1, x_2)]`.)*

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.isMinimaxValue_swap_of_add_eq`: player 2's minimax
  value `c - v₁` in a constant-sum game `s₁ + s₂ = c`.
* `Cslib.MachineLearning.OnlineLearning.Experts.average_loss_le_of_isMinimaxValue`,
  `Cslib.MachineLearning.OnlineLearning.Experts.constantSum_col_average_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.constantSum_average_loss_mem_Icc`:
  [BlumMansour2007AGT, Theorem 4.9 and §4.4.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.ciSup_ciInf_eq_ciInf_ciSup`,
  `Cslib.MachineLearning.OnlineLearning.Experts.isMinimaxValue_ciInf_ciSup`: online-learning proof
  of von Neumann's minimax theorem [BlumMansour2007AGT, §4.4.2].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Function Real Convexity Cslib.Probability

variable {I J : Type*} [Fintype I] [Fintype J]

private theorem sum_mul_sum_comm (p : I → ℝ) (q : J → ℝ) (M : I → J → ℝ) :
    ∑ j, q j * ∑ i, p i * M i j = ∑ i, p i * ∑ j, q j * M i j := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

private theorem sum_mul_mem_Icc {K : Type*} [Fintype K] {w f : K → ℝ} (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (hf : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1) :
    ∑ k, w k * f k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sum_nonneg fun k _ => mul_nonneg (hw0 k) (hf k).1,
    (sum_le_sum fun k _ => mul_le_of_le_one_right (hw0 k) (hf k).2).trans_eq hw1⟩

/-! ### Constant-sum value duality and Theorem 4.9 -/

/-- If `s₁` and `s₂` sum to `c` on every outcome and `s₁` has minimax value `v₁`, then player 2's
transposed loss matrix `Function.swap s₂` has minimax value `c - v₁`
[BlumMansour2007AGT, §4.4.2, p. 89]. -/
theorem isMinimaxValue_swap_of_add_eq {s₁ s₂ : I → J → ℝ} {c v₁ : ℝ}
    (hcs : ∀ i j, s₁ i j + s₂ i j = c) (hv₁ : IsMinimaxValue s₁ v₁) :
    IsMinimaxValue (swap s₂) (c - v₁) := by
  have hsub (i : I) (j : J) : s₂ i j = c - s₁ i j := eq_sub_of_add_eq' (hcs i j)
  obtain ⟨⟨p, hp⟩, q, hq⟩ := hv₁
  refine ⟨⟨q, fun i => ?_⟩, p, fun j => ?_⟩
  · simp only [swap, hsub, mul_sub, sum_sub_distrib, ← sum_mul, q.total_of_fintype, one_mul]
    linarith [hq i]
  · simp only [swap, hsub, mul_sub, sum_sub_distrib, ← sum_mul, p.total_of_fintype, one_mul]
    linarith [hp j]

/-- **Average loss of an external-regret row learner against an arbitrary opponent**
[BlumMansour2007AGT, §4.4.2, Theorem 4.9, p. 89]: if `M` has minimax value `v`, `q` is any sequence
of mixed column strategies over `T > 0` rounds, and `p` achieves external regret at most `R`
against the induced stage loss vectors `i ↦ ∑ j, q t j * M i j`, then the row learner's average
expected loss is at most `v + R / T`. -/
theorem average_loss_le_of_isMinimaxValue {M : I → J → ℝ} {v R : ℝ} (hv : IsMinimaxValue M v)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hq0 : ∀ t < T, ∀ j, 0 ≤ q t j) (hq1 : ∀ t < T, ∑ j, q t j = 1)
    (hreg : ∀ i : I, ∑ t ∈ range T, ∑ i', p t i' * ∑ j, q t j * M i' j ≤
      (∑ t ∈ range T, ∑ j, q t j * M i j) + R) :
    (∑ t ∈ range T, ∑ i, p t i * ∑ j, q t j * M i j) / T ≤ v + R / T := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨i_star, hi_star⟩ := hv.exists_ge (averageProb_nonneg hq0) (sum_averageProb hT hq1)
  have hcum : (∑ t ∈ range T, ∑ j, q t j * M i_star j) / T =
      ∑ j, averageProb q T j * M i_star j := by
    simp only [averageProb_apply, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
  calc (∑ t ∈ range T, ∑ i, p t i * ∑ j, q t j * M i j) / T
      ≤ ((∑ t ∈ range T, ∑ j, q t j * M i_star j) + R) / T :=
        div_le_div_of_nonneg_right (hreg i_star) hT'.le
    _ = (∑ t ∈ range T, ∑ j, q t j * M i_star j) / T + R / T := add_div _ _ _
    _ = ∑ j, averageProb q T j * M i_star j + R / T := by rw [hcum]
    _ ≤ v + R / T := by linarith

/-- **Average loss of an external-regret column learner in a constant-sum game**
[BlumMansour2007AGT, §4.4.2, Theorem 4.9, p. 89]: if `∀ i j, s₁ i j + s₂ i j = c` and `s₁` has
minimax value `v₁`, then any column learner `q` achieving external regret at most `R` over `T > 0`
rounds against `j ↦ ∑ i, p t i * s₂ i j` incurs average expected loss at most `(c - v₁) + R / T`
against *every* sequence `p` of mixed row strategies. -/
theorem constantSum_col_average_loss_le {s₁ s₂ : I → J → ℝ} {c v₁ R : ℝ}
    (hcs : ∀ i j, s₁ i j + s₂ i j = c) (hv₁ : IsMinimaxValue s₁ v₁)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hp0 : ∀ t < T, ∀ i, 0 ≤ p t i) (hp1 : ∀ t < T, ∑ i, p t i = 1)
    (hreg : ∀ j : J, ∑ t ∈ range T, ∑ j', q t j' * ∑ i, p t i * s₂ i j' ≤
      (∑ t ∈ range T, ∑ i, p t i * s₂ i j) + R) :
    (∑ t ∈ range T, ∑ j, q t j * ∑ i, p t i * s₂ i j) / T ≤ (c - v₁) + R / T :=
  average_loss_le_of_isMinimaxValue (M := swap s₂) (isMinimaxValue_swap_of_add_eq hcs hv₁)
    hT hp0 hp1 hreg

/-- **Simultaneous external-regret bounds in a constant-sum game**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]: when player 1 achieves external regret at most `R₁` and
player 2 achieves external regret at most `R₂` over `T > 0` rounds of a constant-sum game
`s₁ + s₂ = c` with player-1 value `v₁`, player 1's average expected loss lies in
`[v₁ - R₂ / T, v₁ + R₁ / T]`. -/
theorem constantSum_average_loss_mem_Icc {s₁ s₂ : I → J → ℝ} {c v₁ R₁ R₂ : ℝ}
    (hcs : ∀ i j, s₁ i j + s₂ i j = c) (hv₁ : IsMinimaxValue s₁ v₁)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hp0 : ∀ t < T, ∀ i, 0 ≤ p t i) (hp1 : ∀ t < T, ∑ i, p t i = 1)
    (hq0 : ∀ t < T, ∀ j, 0 ≤ q t j) (hq1 : ∀ t < T, ∑ j, q t j = 1)
    (hreg₁ : ∀ i : I, ∑ t ∈ range T, ∑ i', p t i' * ∑ j, q t j * s₁ i' j ≤
      (∑ t ∈ range T, ∑ j, q t j * s₁ i j) + R₁)
    (hreg₂ : ∀ j : J, ∑ t ∈ range T, ∑ j', q t j' * ∑ i, p t i * s₂ i j' ≤
      (∑ t ∈ range T, ∑ i, p t i * s₂ i j) + R₂) :
    (∑ t ∈ range T, ∑ i, p t i * ∑ j, q t j * s₁ i j) / T ∈
      Set.Icc (v₁ - R₂ / T) (v₁ + R₁ / T) := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hup₁ := average_loss_le_of_isMinimaxValue hv₁ hT hq0 hq1 hreg₁
  have hup₂ := constantSum_col_average_loss_le hcs hv₁ hT hp0 hp1 hreg₂
  have hstage_sum : ∀ t < T,
      (∑ i, p t i * ∑ j, q t j * s₁ i j) + (∑ j, q t j * ∑ i, p t i * s₂ i j) = c := by
    intro t ht
    rw [sum_mul_sum_comm (p t) (q t) s₂, ← sum_add_distrib]
    calc ∑ i, (p t i * ∑ j, q t j * s₁ i j + p t i * ∑ j, q t j * s₂ i j)
        = ∑ i, p t i * ∑ j, q t j * (s₁ i j + s₂ i j) :=
          sum_congr rfl fun i _ => by rw [← mul_add, ← sum_add_distrib]; simp only [mul_add]
      _ = ∑ i, p t i * ∑ j, q t j * c :=
          sum_congr rfl fun _ _ => congrArg _ (sum_congr rfl fun _ _ => congrArg _ (hcs _ _))
      _ = c := by simp only [← sum_mul, hq1 t ht, hp1 t ht, one_mul]
  have havg_sum :
      (∑ t ∈ range T, ∑ i, p t i * ∑ j, q t j * s₁ i j) / T +
      (∑ t ∈ range T, ∑ j, q t j * ∑ i, p t i * s₂ i j) / T = c := by
    rw [← add_div, ← sum_add_distrib, sum_congr rfl fun t ht => hstage_sum t (mem_range.mp ht)]
    simp only [sum_const, card_range, nsmul_eq_mul]
    exact mul_div_cancel_left₀ c hT'.ne'
  exact ⟨by linarith, hup₁⟩

/-! ### §4.4.2: Coupled no-regret proof of von Neumann's minimax theorem -/

section OnlineMinimax

variable [Nonempty I] [Nonempty J]

omit [Fintype J] [Nonempty I] in
private theorem bddBelow_range_ciSup_loss [Finite J] (M : I → J → ℝ) :
    BddBelow (Set.range fun p : StdSimplex ℝ I => ⨆ j : J, ∑ i, p.weights i * M i j) := by
  cases nonempty_fintype J
  obtain ⟨j₀⟩ := ‹Nonempty J›
  let B := ∑ i : I, |M i j₀|
  refine ⟨-B, ?_⟩
  rintro _ ⟨p, rfl⟩
  dsimp only
  rw [← sup'_univ_eq_ciSup]
  refine le_trans ?_ (le_sup' (fun j => ∑ i, p.weights i * M i j) (mem_univ j₀))
  have hle : ∀ i, p.weights i ≤ 1 := fun i =>
    (single_le_sum (fun i' _ => p.weights_nonneg i') (mem_univ i)).trans_eq p.total_of_fintype
  calc -B = -(∑ i, |M i j₀|) := rfl
    _ = ∑ i, -|M i j₀| := by rw [sum_neg_distrib]
    _ ≤ ∑ i, p.weights i * M i j₀ := sum_le_sum fun i _ => by
        nlinarith [neg_abs_le (M i j₀), p.weights_nonneg i, hle i, abs_nonneg (M i j₀)]

omit [Fintype I] [Nonempty J] in
private theorem bddAbove_range_ciInf_loss [Finite I] (M : I → J → ℝ) :
    BddAbove (Set.range fun q : StdSimplex ℝ J => ⨅ i : I, ∑ j, q.weights j * M i j) := by
  cases nonempty_fintype I
  obtain ⟨i₀⟩ := ‹Nonempty I›
  let B := ∑ j : J, |M i₀ j|
  refine ⟨B, ?_⟩
  rintro _ ⟨q, rfl⟩
  dsimp only
  rw [← inf'_univ_eq_ciInf]
  refine (inf'_le (fun i => ∑ j, q.weights j * M i j) (mem_univ i₀)).trans ?_
  have hle : ∀ j, q.weights j ≤ 1 := fun j =>
    (single_le_sum (fun j' _ => q.weights_nonneg j') (mem_univ j)).trans_eq q.total_of_fintype
  calc ∑ j, q.weights j * M i₀ j ≤ ∑ j, |M i₀ j| := sum_le_sum fun j _ => by
        nlinarith [le_abs_self (M i₀ j), q.weights_nonneg j, hle j, abs_nonneg (M i₀ j)]
    _ = B := rfl

/-- Coupled horizon-`T` multiplicative-weights self-play on `[0, 1]` matrices: running
`prob (mwFactor η₁)` against `prob (mwFactor η₂)` produces empirical mixed strategies whose
expected losses are within `2 * (√(ln |I|) + √(ln |J|)) / √T` for every pair `(i, j)`. -/
private theorem coupledMW_gap_le {M₀ : I → J → ℝ} (hM₀ : ∀ i j, M₀ i j ∈ Set.Icc (0 : ℝ) 1)
    {T : ℕ} (hT : 0 < T) :
    ∃ (p_bar : I → ℝ) (q_bar : J → ℝ),
      (∀ i, 0 ≤ p_bar i) ∧ ∑ i, p_bar i = 1 ∧
      (∀ j, 0 ≤ q_bar j) ∧ ∑ j, q_bar j = 1 ∧
      ∀ (i : I) (j : J),
        ∑ i', p_bar i' * M₀ i' j ≤
          ∑ j', q_bar j' * M₀ i j' +
            2 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) := by
  set η₁ := min √(log (Fintype.card I) / T) (1 / 2)
  set η₂ := min √(log (Fintype.card J) / T) (1 / 2)
  have hη₁_le : η₁ ≤ 1 / 2 := min_le_right _ _
  have hη₂_le : η₂ ≤ 1 / 2 := min_le_right _ _
  have hη₁_nn : 0 ≤ η₁ := le_min (sqrt_nonneg _) (by norm_num)
  have hη₂_nn : 0 ≤ η₂ := le_min (sqrt_nonneg _) (by norm_num)
  let step : ∀ t : ℕ, (∀ s < t, (I → ℝ) × (J → ℝ)) → (I → ℝ) × (J → ℝ) := fun t prev =>
    let ℓ₁_pre : ℕ → I → ℝ := fun s => if hs : s < t then (prev s hs).1 else 0
    let ℓ₂_pre : ℕ → J → ℝ := fun s => if hs : s < t then (prev s hs).2 else 0
    let pt := prob (mwFactor η₁) ℓ₁_pre t
    let qt := prob (mwFactor η₂) ℓ₂_pre t
    (fun i => ∑ j, qt j * M₀ i j, fun j => 1 - ∑ i, pt i * M₀ i j)
  let run : ℕ → (I → ℝ) × (J → ℝ) := WellFounded.fix Nat.lt_wfRel.wf step
  let ℓ₁ : ℕ → I → ℝ := fun t => (run t).1
  let ℓ₂ : ℕ → J → ℝ := fun t => (run t).2
  let p : ℕ → I → ℝ := prob (mwFactor η₁) ℓ₁
  let q : ℕ → J → ℝ := prob (mwFactor η₂) ℓ₂
  have hrun_eq : ∀ t,
      run t = (fun i => ∑ j, q t j * M₀ i j, fun j => 1 - ∑ i, p t i * M₀ i j) := fun t => by
    have hfix : run t = step t (fun s _ => run s) := WellFounded.fix_eq Nat.lt_wfRel.wf step t
    dsimp only [step] at hfix
    rw [hfix, prob_congr (ℓ' := ℓ₁) fun s hs => by simp only [ℓ₁, hs, ↓reduceDIte],
      prob_congr (ℓ' := ℓ₂) fun s hs => by simp only [ℓ₂, hs, ↓reduceDIte]]
  have hℓ₁_eq : ∀ t i, ℓ₁ t i = ∑ j, q t j * M₀ i j :=
    fun t => congrFun (congrArg Prod.fst (hrun_eq t))
  have hℓ₂_eq : ∀ t j, ℓ₂ t j = 1 - ∑ i, p t i * M₀ i j :=
    fun t => congrFun (congrArg Prod.snd (hrun_eq t))
  have hinv : ∀ t,
      (∀ i, ℓ₁ t i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ j, ℓ₂ t j ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1 ∧
      (∀ j, 0 ≤ q t j) ∧ ∑ j, q t j = 1 := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      have hφ₁ : ∀ s < t, ∀ i, 0 < mwFactor η₁ (ℓ₁ s i) := fun s hs i => by
        rw [mwFactor_apply]; nlinarith [((ih s hs).1 i).2]
      have hφ₂ : ∀ s < t, ∀ j, 0 < mwFactor η₂ (ℓ₂ s j) := fun s hs j => by
        rw [mwFactor_apply]; nlinarith [((ih s hs).2.1 j).2]
      have hp0 : ∀ i, 0 ≤ p t i := prob_nonneg hφ₁
      have hp1 : ∑ i, p t i = 1 := sum_prob hφ₁
      have hq0 : ∀ j, 0 ≤ q t j := prob_nonneg hφ₂
      have hq1 : ∑ j, q t j = 1 := sum_prob hφ₂
      refine ⟨fun i => hℓ₁_eq t i ▸ sum_mul_mem_Icc hq0 hq1 fun j => hM₀ i j, fun j => ?_,
        hp0, hp1, hq0, hq1⟩
      have h := sum_mul_mem_Icc hp0 hp1 fun i => hM₀ i j
      exact hℓ₂_eq t j ▸ ⟨sub_nonneg.mpr h.2, sub_le_self _ h.1⟩
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsT : 0 < √(T : ℝ) := sqrt_pos.mpr hT_pos
  refine ⟨averageProb p T, averageProb q T,
    averageProb_nonneg (fun t _ => (hinv t).2.2.1),
    sum_averageProb hT (fun t _ => (hinv t).2.2.2.1),
    averageProb_nonneg (fun t _ => (hinv t).2.2.2.2.1),
    sum_averageProb hT (fun t _ => (hinv t).2.2.2.2.2), fun i j => ?_⟩
  have hr₁ := mw_regret_le_sqrt_of_mem_Icc (T := T) (fun s _ => (hinv s).1) i
  have hr₂ := mw_regret_le_sqrt_of_mem_Icc (T := T) (fun s _ => (hinv s).2.1) j
  have hround_sum : ∀ t, (∑ i', p t i' * ℓ₁ t i') + (∑ j', q t j' * ℓ₂ t j') = 1 := fun t => by
    simp only [hℓ₁_eq, hℓ₂_eq, mul_sub, mul_one, sum_sub_distrib]
    linarith [sum_mul_sum_comm (p t) (q t) M₀, (hinv t).2.2.2.2.2]
  have htot : (∑ t ∈ range T, ∑ i', p t i' * ℓ₁ t i') +
      (∑ t ∈ range T, ∑ j', q t j' * ℓ₂ t j') = T := by
    rw [← sum_add_distrib, sum_congr rfl fun t _ => hround_sum t]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hcum₁ : ∑ t ∈ range T, ℓ₁ t i = (T : ℝ) * ∑ j', averageProb q T j' * M₀ i j' := by
    simp only [hℓ₁_eq, averageProb_apply, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm, mul_div_cancel₀ _ hT_pos.ne']
  have hcum₂ : ∑ t ∈ range T, ℓ₂ t j = (T : ℝ) - (T : ℝ) * ∑ i', averageProb p T i' * M₀ i' j := by
    simp only [hℓ₂_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one,
      averageProb_apply, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm, mul_div_cancel₀ _ hT_pos.ne']
  have hsum_reg : (T : ℝ) * ∑ i', averageProb p T i' * M₀ i' j ≤
      (T : ℝ) * ∑ j', averageProb q T j' * M₀ i j' +
        (2 * √(T * log (Fintype.card I)) + 2 * √(T * log (Fintype.card J))) := by
    dsimp only [p, q, η₁, η₂] at htot; linarith
  have hrad : (2 * √(T * log (Fintype.card I)) + 2 * √(T * log (Fintype.card J))) / T =
      2 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) := by
    rw [sqrt_mul hT_pos.le, sqrt_mul hT_pos.le]
    calc (2 * (√(T : ℝ) * √(log (Fintype.card I))) +
          2 * (√(T : ℝ) * √(log (Fintype.card J)))) / T
        = √(T : ℝ) * (2 * (√(log (Fintype.card I)) + √(log (Fintype.card J)))) /
            (√(T : ℝ) * √(T : ℝ)) := by
            rw [mul_self_sqrt hT_pos.le]
            ring
      _ = 2 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) :=
            mul_div_mul_left _ _ hsT.ne'
  have hdiv := div_le_div_of_nonneg_right hsum_reg hT_pos.le
  rwa [add_div, mul_div_cancel_left₀ _ hT_pos.ne', mul_div_cancel_left₀ _ hT_pos.ne', hrad] at hdiv

/-- **Online-learning proof of von Neumann's minimax identity**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]:
`(⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j)` equals
`⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j` for every finite real matrix game `M`,
proved via coupled `mwFactor` self-play and `T → ∞` without LP duality or Sion's theorem. -/
theorem ciSup_ciInf_eq_ciInf_ciSup (M : I → J → ℝ) :
    (⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j) =
      ⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j := by
  have : Nonempty (StdSimplex ℝ I) := ‹Nonempty I›.map StdSimplex.single
  have : Nonempty (StdSimplex ℝ J) := ‹Nonempty J›.map StdSimplex.single
  apply le_antisymm
  · refine ciSup_le fun q => le_ciInf fun p => ?_
    rw [← inf'_univ_eq_ciInf, ← sup'_univ_eq_ciSup]
    calc (univ.inf' univ_nonempty fun i => ∑ j, q.weights j * M i j)
        = ∑ i, p.weights i * (univ.inf' univ_nonempty fun i' => ∑ j, q.weights j * M i' j) := by
          rw [← sum_mul, p.total_of_fintype, one_mul]
      _ ≤ ∑ i, p.weights i * ∑ j, q.weights j * M i j :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (inf'_le (fun i' => ∑ j, q.weights j * M i' j) (mem_univ i)) (p.weights_nonneg i)
      _ = ∑ j, q.weights j * ∑ i, p.weights i * M i j := (sum_mul_sum_comm _ _ _).symm
      _ ≤ ∑ j, q.weights j * (univ.sup' univ_nonempty fun j' => ∑ i, p.weights i * M i j') :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (le_sup' (fun j' => ∑ i, p.weights i * M i j') (mem_univ j)) (q.weights_nonneg j)
      _ = univ.sup' univ_nonempty fun j' => ∑ i, p.weights i * M i j' := by
          rw [← sum_mul, q.total_of_fintype, one_mul]
  · set Bmax := ∑ i : I, ∑ j : J, |M i j|
    have hBmax_nn : 0 ≤ Bmax := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
    set B := Bmax + 1
    have hB : 0 < B := by linarith
    let M₀ : I → J → ℝ := fun i j => (M i j + B) / (2 * B)
    have hM₀ : ∀ i j, M₀ i j ∈ Set.Icc (0 : ℝ) 1 := fun i j => by
      have habs : |M i j| ≤ Bmax := by
        calc |M i j| ≤ ∑ j' : J, |M i j'| :=
              single_le_sum (f := fun j' : J => |M i j'|) (fun _ _ => abs_nonneg _) (mem_univ j)
          _ ≤ Bmax :=
              single_le_sum (f := fun i' : I => ∑ j' : J, |M i' j'|)
                (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i)
      have hlow : -B ≤ M i j := by linarith [neg_le_of_abs_le habs]
      have hhigh : M i j ≤ B := by linarith [le_of_abs_le habs]
      dsimp only [M₀]
      exact ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩
    set C := 2 * B * (2 * (√(log (Fintype.card I)) + √(log (Fintype.card J))))
    have hgap : ∀ T : ℕ, 0 < T →
        (⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j) ≤
          (⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j) + C / √(T : ℝ) := by
      intro T hT
      obtain ⟨p_bar, q_bar, hp0, hp1, hq0, hq1, hle₀⟩ := coupledMW_gap_le hM₀ hT
      obtain ⟨sp, hsp'⟩ : p_bar ∈ Set.range fun s : StdSimplex ℝ I => (s.weights : I → ℝ) :=
        StdSimplex.range_toFun_comp_weights.symm.subset ⟨Set.mem_iInter.2 hp0, hp1⟩
      obtain ⟨sq, hsq'⟩ : q_bar ∈ Set.range fun s : StdSimplex ℝ J => (s.weights : J → ℝ) :=
        StdSimplex.range_toFun_comp_weights.symm.subset ⟨Set.mem_iInter.2 hq0, hq1⟩
      dsimp only at hsp' hsq'
      have hpair : ∀ (i : I) (j : J),
          ∑ i', p_bar i' * M i' j ≤ ∑ j', q_bar j' * M i j' + C / √(T : ℝ) := fun i j => by
        have hM_eq (i' : I) (j' : J) : M i' j' = 2 * B * M₀ i' j' - B := by
          simp only [M₀, mul_div_cancel₀ _ (mul_pos zero_lt_two hB).ne', add_sub_cancel_right]
        have hlhs : ∑ i', p_bar i' * M i' j = 2 * B * (∑ i', p_bar i' * M₀ i' j) - B := by
          simp only [hM_eq, mul_sub, mul_left_comm _ (2 * B), sum_sub_distrib, ← mul_sum,
            ← sum_mul, hp1, one_mul]
        have hrhs : ∑ j', q_bar j' * M i j' = 2 * B * (∑ j', q_bar j' * M₀ i j') - B := by
          simp only [hM_eq, mul_sub, mul_left_comm _ (2 * B), sum_sub_distrib, ← mul_sum,
            ← sum_mul, hq1, one_mul]
        have hmul := mul_le_mul_of_nonneg_left (hle₀ i j) (mul_nonneg zero_le_two hB.le)
        rw [mul_add (2 * B), ← mul_div_assoc] at hmul
        linarith
      have hsup_inf : (⨆ j : J, ∑ i, sp.weights i * M i j) ≤
          (⨅ i : I, ∑ j, sq.weights j * M i j) + C / √(T : ℝ) := by
        rw [hsp', hsq', ← sup'_univ_eq_ciSup, ← inf'_univ_eq_ciInf]
        exact Finset.sup'_le _ _ fun j _ => sub_le_iff_le_add.mp
          (Finset.le_inf' univ_nonempty _ fun i _ => sub_le_iff_le_add.mpr (hpair i j))
      linarith [ciInf_le (bddBelow_range_ciSup_loss M) sp,
        le_ciSup (bddAbove_range_ciInf_loss M) sq]
    by_contra! hlt
    set δ := (⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j) -
      ⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j
    have hδ : 0 < δ := sub_pos.mpr hlt
    obtain ⟨T, hT_gt⟩ := exists_nat_gt ((C / δ) ^ 2 + 1)
    have hT_pos : 0 < T :=
      Nat.cast_pos.mp ((add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one).trans hT_gt)
    have hsT : C / δ < √(T : ℝ) := by
      have h1 : (C / δ) ^ 2 < T := by linarith
      calc C / δ ≤ √((C / δ) ^ 2) := le_sqrt_of_sq_le le_rfl
        _ < √(T : ℝ) := sqrt_lt_sqrt (sq_nonneg _) h1
    have hC_lt : C / √(T : ℝ) < δ := (div_lt_iff₀ (sqrt_pos.mpr (Nat.cast_pos.mpr hT_pos))).mpr
      (by linarith [(div_lt_iff₀ hδ).mp hsT])
    linarith [hgap T hT_pos]

/-- **Attained minimax value via coupled no-regret learning**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]: combining `ciSup_ciInf_eq_ciInf_ciSup` with compactness of
`StdSimplex ℝ` yields optimal mixed strategies witnessing
`IsMinimaxValue M (⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j)` without invoking
`exists_isMinimaxValue` or Sion's theorem. -/
theorem isMinimaxValue_ciInf_ciSup (M : I → J → ℝ) :
    IsMinimaxValue M (⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j) := by
  have : Nonempty (StdSimplex ℝ I) := ‹Nonempty I›.map StdSimplex.single
  have : Nonempty (StdSimplex ℝ J) := ‹Nonempty J›.map StdSimplex.single
  have hcont_wI : Continuous (fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous
  have hcont_wJ : Continuous (fun q : StdSimplex ℝ J => (q.weights : J → ℝ)) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous
  have hcont_row : Continuous (fun p : StdSimplex ℝ I => ⨆ j : J, ∑ i, p.weights i * M i j) := by
    simp_rw [← sup'_univ_eq_ciSup]
    exact Continuous.finset_sup'_apply univ_nonempty fun j _ =>
      continuous_finsetSum univ fun i _ => ((continuous_apply i).comp hcont_wI).mul continuous_const
  have hcont_col : Continuous (fun q : StdSimplex ℝ J => ⨅ i : I, ∑ j, q.weights j * M i j) := by
    simp_rw [← inf'_univ_eq_ciInf]
    exact Continuous.finset_inf'_apply univ_nonempty fun i _ =>
      continuous_finsetSum univ fun j _ => ((continuous_apply j).comp hcont_wJ).mul continuous_const
  obtain ⟨p_opt, -, hp_min⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hcont_row.continuousOn
  obtain ⟨q_opt, -, hq_max⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont_col.continuousOn
  have hp_val : (⨆ j : J, ∑ i, p_opt.weights i * M i j) =
      ⨅ p : StdSimplex ℝ I, ⨆ j : J, ∑ i, p.weights i * M i j :=
    le_antisymm (le_ciInf fun p => hp_min (Set.mem_univ p))
      (ciInf_le (bddBelow_range_ciSup_loss M) p_opt)
  have hq_val : (⨅ i : I, ∑ j, q_opt.weights j * M i j) =
      ⨆ q : StdSimplex ℝ J, ⨅ i : I, ∑ j, q.weights j * M i j :=
    le_antisymm (le_ciSup (bddAbove_range_ciInf_loss M) q_opt)
      (ciSup_le fun q => hq_max (Set.mem_univ q))
  refine ⟨⟨p_opt, fun j => ?_⟩, q_opt, fun i => ?_⟩
  · rw [← hp_val, ← sup'_univ_eq_ciSup]
    exact le_sup' (fun j' => ∑ i, p_opt.weights i * M i j') (mem_univ j)
  · rw [← ciSup_ciInf_eq_ciInf_ciSup M, ← hq_val, ← inf'_univ_eq_ciInf]
    exact inf'_le (fun i' => ∑ j, q_opt.weights j * M i' j) (mem_univ i)

end OnlineMinimax

end Cslib.MachineLearning.OnlineLearning.Experts
