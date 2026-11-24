/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.Greedy
public import CslibFrontier.MachineLearning.OnlineLearning.InternalRegret
public import CslibFrontier.Probability.Minimax.Value
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# External regret in constant-sum games and the online-learning minimax proof

This module formalizes [BlumMansour2007AGT, §4.4, §4.4.1 (Theorem 4.9), and §4.4.2, pp. 88–90]:
external regret guarantees in two-player constant-sum games against *arbitrary* opponent play,
convergence of simultaneous low-regret play to the game value, and the coupled online-learning
proof of von Neumann's minimax theorem (`maxminValue M = minmaxValue M` and
`isMinimaxValue_minmaxValue_of_noRegret`, proved via coupled `anytimeHedgeProb` dynamics rather than
linear-programming duality or Sion's theorem).

## Overview and source mapping

* **Constant-sum games and value duality** (`IsConstantSum`, `IsConstantSum.isMinimaxValue_col`,
  `IsConstantSum.add_eq` — [BlumMansour2007AGT, §4.4, p. 88]):
  Two loss matrices `s₁ s₂ : I → J → ℝ` form a constant-sum game with constant `c` when
  `∀ i j, s₁ i j + s₂ i j = c`. If `s₁` has minimax value `v₁`, then player 2's transposed loss
  matrix `(fun j i => s₂ i j)` has minimax value `v₂ = c - v₁`, so `v₁ + v₂ = c`.
* **Theorem 4.9 — Average loss against an arbitrary opponent** (`constantSum_row_average_loss_le`,
  `constantSum_col_average_loss_le`, `constantSum_average_loss_mem_Icc` —
  [BlumMansour2007AGT, §4.4.1, Theorem 4.9, p. 89]):
  In any finite matrix game with minimax value `v₁`, a row learner with external regret at most `R`
  over `T > 0` rounds achieves average expected loss at most `v₁ + R / T` against *every* sequence
  `q` of mixed opponent strategies (not merely best responses). In a constant-sum game, a column
  learner with external regret at most `R₂` likewise achieves average expected loss at most
  `(c - v₁) + R₂ / T`, and when *both* players run external-regret learners simultaneously, player
  1's average expected loss lies in `[v₁ - R₂ / T, v₁ + R₁ / T]`.
* **§4.4.2 — Coupled no-regret proof of the minimax theorem** (`rowWorstLoss`, `colBestPayoff`,
  `minmaxValue`, `maxminValue`, `coupledHedge_gap_le`, `maxminValue_eq_minmaxValue`,
  `isMinimaxValue_minmaxValue_of_noRegret` — [BlumMansour2007AGT, §4.4.2, pp. 89–90]):
  Define `maxminValue M = ⨆ q : StdSimplex ℝ J, min_i ∑ j, q j * M i j` (`v_min^1` in
  [BlumMansour2007AGT, §4.4.2]) and `minmaxValue M = ⨅ p : StdSimplex ℝ I, max_j ∑ i, p i * M i j`
  (`v_max^1`).
  *(Source note: the displayed formula on [BlumMansour2007AGT, p. 89] swaps the `min`/`max`
  operators in `v_min^1`, writing `min_q max_i`; the immediately following sentence on p. 89 and the
  proof on p. 90 define `v_min^1 = max_q min_i E_{j~q}[s_1(i, j)] ≤ v_max^1`.)*
  Running two `anytimeHedgeProb` learners against each other on `M` affine-rescaled into `[0, 1]`
  bounds `minmaxValue M - maxminValue M ≤ C / √T` for every `T ≥ 1` using only elementary finite
  sums, forcing `maxminValue M = minmaxValue M` as `T → ∞`; compactness of `StdSimplex ℝ` then
  yields optimal strategies witnessing `IsMinimaxValue M (minmaxValue M)` without invoking LP
  duality (`exists_isMinimaxValue`) or Sion's theorem.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.IsConstantSum`: constant-sum relation
  `∀ i j, s₁ i j + s₂ i j = c` between two players' loss matrices.
* `Cslib.MachineLearning.OnlineLearning.Experts.inducedRowLoss`,
  `Cslib.MachineLearning.OnlineLearning.Experts.inducedColLoss`: stage loss vectors induced by the
  opponent's mixed strategy sequence.
* `Cslib.MachineLearning.OnlineLearning.Experts.rowWorstLoss`,
  `Cslib.MachineLearning.OnlineLearning.Experts.colBestPayoff`: worst-case expected loss of a row
  strategy and best-response lower bound of a column strategy.
* `Cslib.MachineLearning.OnlineLearning.Experts.minmaxValue`,
  `Cslib.MachineLearning.OnlineLearning.Experts.maxminValue`: `inf_p max_j` and `sup_q min_i` values
  over `Convexity.StdSimplex ℝ`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.IsConstantSum.isMinimaxValue_col`,
  `Cslib.MachineLearning.OnlineLearning.Experts.IsConstantSum.add_eq`: value duality `v₁ + v₂ = c`
  in constant-sum games.
* `Cslib.MachineLearning.OnlineLearning.Experts.constantSum_row_average_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.constantSum_col_average_loss_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.constantSum_average_loss_mem_Icc`:
  [BlumMansour2007AGT, Theorem 4.9 and §4.4.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.coupledHedge_gap_le`: explicit `O(1 / √T)` duality
  gap from coupled `anytimeHedgeProb` self-play.
* `Cslib.MachineLearning.OnlineLearning.Experts.maxminValue_eq_minmaxValue`,
  `Cslib.MachineLearning.OnlineLearning.Experts.isMinimaxValue_minmaxValue_of_noRegret`:
  online-learning proof of von Neumann's minimax theorem [BlumMansour2007AGT, §4.4.2].

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real Convexity Cslib.Probability

variable {I J : Type*} [Fintype I] [Fintype J]

/-! ### Constant-sum games and value duality -/

/-- Two loss matrices `s₁, s₂ : I → J → ℝ` define a constant-sum game with constant `c` if the two
players' losses sum to `c` on every outcome `(i, j)` [BlumMansour2007AGT, §4.4, p. 88]. -/
@[expose] def IsConstantSum (s₁ s₂ : I → J → ℝ) (c : ℝ) : Prop :=
  ∀ i j, s₁ i j + s₂ i j = c

omit [Fintype I] [Fintype J] in
theorem isConstantSum_iff {s₁ s₂ : I → J → ℝ} {c : ℝ} :
    IsConstantSum s₁ s₂ c ↔ ∀ i j, s₁ i j + s₂ i j = c :=
  Iff.rfl

omit [Fintype I] [Fintype J] in
theorem IsConstantSum.col_eq_sub {s₁ s₂ : I → J → ℝ} {c : ℝ} (hcs : IsConstantSum s₁ s₂ c)
    (i : I) (j : J) : s₂ i j = c - s₁ i j := by
  linarith [hcs i j]

/-- If `s₁` has minimax value `v₁` in a constant-sum game with sum `c`, then player 2's transposed
loss matrix `(fun j i => s₂ i j)` has minimax value `c - v₁` [BlumMansour2007AGT, §4.4, p. 88]. -/
theorem IsConstantSum.isMinimaxValue_col {s₁ s₂ : I → J → ℝ} {c v₁ : ℝ}
    (hcs : IsConstantSum s₁ s₂ c) (hv₁ : IsMinimaxValue s₁ v₁) :
    IsMinimaxValue (fun j i => s₂ i j) (c - v₁) := by
  obtain ⟨⟨p, hp⟩, q, hq⟩ := hv₁
  refine ⟨⟨q, fun i => ?_⟩, p, fun j => ?_⟩
  · have hsum : ∑ j, q.weights j * s₂ i j = c - ∑ j, q.weights j * s₁ i j := by
      simp only [hcs.col_eq_sub, mul_sub, sum_sub_distrib, ← sum_mul, q.total_of_fintype, one_mul]
    linarith [hq i]
  · have hsum : ∑ i, p.weights i * s₂ i j = c - ∑ i, p.weights i * s₁ i j := by
      simp only [hcs.col_eq_sub, mul_sub, sum_sub_distrib, ← sum_mul, p.total_of_fintype, one_mul]
    linarith [hp j]

/-- In a constant-sum game with sum `c`, the two players' minimax values satisfy `v₁ + v₂ = c`. -/
theorem IsConstantSum.add_eq {s₁ s₂ : I → J → ℝ} {c v₁ v₂ : ℝ}
    (hcs : IsConstantSum s₁ s₂ c) (hv₁ : IsMinimaxValue s₁ v₁)
    (hv₂ : IsMinimaxValue (fun j i => s₂ i j) v₂) :
    v₁ + v₂ = c := by
  have heq := hv₂.unique (hcs.isMinimaxValue_col hv₁)
  linarith

/-! ### Theorem 4.9: Average loss under external-regret learning -/

/-- Stage loss vector `i ↦ ∑ j, q t j * s₁ i j` faced by the row player against mixed column play
`q`. -/
def inducedRowLoss (s₁ : I → J → ℝ) (q : ℕ → J → ℝ) (t : ℕ) (i : I) : ℝ :=
  ∑ j, q t j * s₁ i j

/-- Stage loss vector `j ↦ ∑ i, p t i * s₂ i j` faced by the column player against mixed row play
`p`. -/
def inducedColLoss (s₂ : I → J → ℝ) (p : ℕ → I → ℝ) (t : ℕ) (j : J) : ℝ :=
  ∑ i, p t i * s₂ i j

private noncomputable def timeAvg {α : Type*} (x : ℕ → α → ℝ) (T : ℕ) (a : α) : ℝ :=
  (∑ t ∈ range T, x t a) / T

private theorem timeAvg_nonneg {α : Type*} {x : ℕ → α → ℝ} {T : ℕ}
    (hx : ∀ t < T, ∀ a, 0 ≤ x t a) (a : α) : 0 ≤ timeAvg x T a :=
  div_nonneg (sum_nonneg fun t ht => hx t (mem_range.mp ht) a) (Nat.cast_nonneg T)

private theorem sum_timeAvg {α : Type*} [Fintype α] {x : ℕ → α → ℝ} {T : ℕ} (hT : 0 < T)
    (hx : ∀ t < T, ∑ a, x t a = 1) : ∑ a, timeAvg x T a = 1 := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  simp only [timeAvg, ← sum_div]
  rw [sum_comm, sum_congr rfl fun t ht => hx t (mem_range.mp ht)]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  exact div_self hT'

/-- **Average loss of an external-regret row learner** [BlumMansour2007AGT, Theorem 4.9, p. 89]:
if `s₁` has minimax value `v₁`, `q` is *any* sequence of opponent mixed strategies over `T > 0`
rounds, and `p` achieves regret at most `R` against every fixed row `i` on `inducedRowLoss s₁ q`,
then player 1's average expected loss is at most `v₁ + R / T`. -/
theorem constantSum_row_average_loss_le {s₁ : I → J → ℝ} {v₁ R : ℝ} (hv₁ : IsMinimaxValue s₁ v₁)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hq0 : ∀ t < T, ∀ j, 0 ≤ q t j) (hq1 : ∀ t < T, ∑ j, q t j = 1)
    (hreg : ∀ i : I, ∑ t ∈ range T, ∑ i', p t i' * inducedRowLoss s₁ q t i' ≤
      cumLoss (inducedRowLoss s₁ q) T i + R) :
    (∑ t ∈ range T, ∑ i, p t i * inducedRowLoss s₁ q t i) / T ≤ v₁ + R / T := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨i_star, hi_star⟩ := hv₁.exists_ge (timeAvg_nonneg hq0) (sum_timeAvg hT hq1)
  have hcum : cumLoss (inducedRowLoss s₁ q) T i_star / T =
      ∑ j, timeAvg q T j * s₁ i_star j := by
    simp only [cumLoss, inducedRowLoss, timeAvg, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
  calc (∑ t ∈ range T, ∑ i, p t i * inducedRowLoss s₁ q t i) / T
      ≤ (cumLoss (inducedRowLoss s₁ q) T i_star + R) / T :=
        div_le_div_of_nonneg_right (hreg i_star) hT'.le
    _ = cumLoss (inducedRowLoss s₁ q) T i_star / T + R / T := add_div _ _ _
    _ = ∑ j, timeAvg q T j * s₁ i_star j + R / T := by rw [hcum]
    _ ≤ v₁ + R / T := by linarith

/-- **Average loss of an external-regret column learner in a constant-sum game**
[BlumMansour2007AGT, Theorem 4.9, p. 89]: if `s₁ + s₂ = c` and `s₁` has minimax value `v₁`, any
column learner `q` with external regret at most `R` over `T > 0` rounds achieves average expected
loss at most `(c - v₁) + R / T` against *every* sequence `p` of row mixed strategies. -/
theorem constantSum_col_average_loss_le {s₁ s₂ : I → J → ℝ} {c v₁ R : ℝ}
    (hcs : IsConstantSum s₁ s₂ c) (hv₁ : IsMinimaxValue s₁ v₁)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hp0 : ∀ t < T, ∀ i, 0 ≤ p t i) (hp1 : ∀ t < T, ∑ i, p t i = 1)
    (hreg : ∀ j : J, ∑ t ∈ range T, ∑ j', q t j' * inducedColLoss s₂ p t j' ≤
      cumLoss (inducedColLoss s₂ p) T j + R) :
    (∑ t ∈ range T, ∑ j, q t j * inducedColLoss s₂ p t j) / T ≤ (c - v₁) + R / T :=
  constantSum_row_average_loss_le (s₁ := fun j i => s₂ i j) (hcs.isMinimaxValue_col hv₁)
    hT hp0 hp1 hreg

/-- **Simultaneous low-regret play in a constant-sum game** [BlumMansour2007AGT, §4.4.1, p. 89]:
when player 1 has external regret at most `R₁` and player 2 has external regret at most `R₂` over
`T > 0` rounds, player 1's average expected loss lies in `[v₁ - R₂ / T, v₁ + R₁ / T]`. -/
theorem constantSum_average_loss_mem_Icc {s₁ s₂ : I → J → ℝ} {c v₁ R₁ R₂ : ℝ}
    (hcs : IsConstantSum s₁ s₂ c) (hv₁ : IsMinimaxValue s₁ v₁)
    {p : ℕ → I → ℝ} {q : ℕ → J → ℝ} {T : ℕ} (hT : 0 < T)
    (hp0 : ∀ t < T, ∀ i, 0 ≤ p t i) (hp1 : ∀ t < T, ∑ i, p t i = 1)
    (hq0 : ∀ t < T, ∀ j, 0 ≤ q t j) (hq1 : ∀ t < T, ∑ j, q t j = 1)
    (hreg₁ : ∀ i : I, ∑ t ∈ range T, ∑ i', p t i' * inducedRowLoss s₁ q t i' ≤
      cumLoss (inducedRowLoss s₁ q) T i + R₁)
    (hreg₂ : ∀ j : J, ∑ t ∈ range T, ∑ j', q t j' * inducedColLoss s₂ p t j' ≤
      cumLoss (inducedColLoss s₂ p) T j + R₂) :
    (∑ t ∈ range T, ∑ i, p t i * inducedRowLoss s₁ q t i) / T ∈
      Set.Icc (v₁ - R₂ / T) (v₁ + R₁ / T) := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hup₁ := constantSum_row_average_loss_le hv₁ hT hq0 hq1 hreg₁
  have hup₂ := constantSum_col_average_loss_le hcs hv₁ hT hp0 hp1 hreg₂
  have hstage_sum : ∀ t < T,
      (∑ i, p t i * inducedRowLoss s₁ q t i) + (∑ j, q t j * inducedColLoss s₂ p t j) = c := by
    intro t ht
    unfold inducedRowLoss inducedColLoss
    have hswap : ∑ j, q t j * ∑ i, p t i * s₂ i j = ∑ i, p t i * ∑ j, q t j * s₂ i j := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [hswap, ← sum_add_distrib]
    calc ∑ i, (p t i * ∑ j, q t j * s₁ i j + p t i * ∑ j, q t j * s₂ i j)
        = ∑ i, p t i * ∑ j, q t j * (s₁ i j + s₂ i j) :=
          sum_congr rfl fun i _ => by rw [← mul_add, ← sum_add_distrib]; simp only [mul_add]
      _ = ∑ i, p t i * ∑ j, q t j * c :=
          sum_congr rfl fun i _ => by
            congr 1; exact sum_congr rfl fun j _ => by rw [hcs i j]
      _ = c := by simp only [← sum_mul, hq1 t ht, hp1 t ht, one_mul]
  have havg_sum :
      (∑ t ∈ range T, ∑ i, p t i * inducedRowLoss s₁ q t i) / T +
      (∑ t ∈ range T, ∑ j, q t j * inducedColLoss s₂ p t j) / T = c := by
    rw [← add_div, ← sum_add_distrib, sum_congr rfl fun t ht => hstage_sum t (mem_range.mp ht)]
    simp only [sum_const, card_range, nsmul_eq_mul]
    exact mul_div_cancel_left₀ c hT'.ne'
  exact ⟨by linarith, hup₁⟩

/-! ### §4.4.2: Coupled no-regret proof of von Neumann's minimax theorem -/

section OnlineMinimax

variable [Nonempty I] [Nonempty J]

/-- Worst-case expected loss `max_j ∑ i, p i * M i j` of a row distribution `p`. -/
def rowWorstLoss (M : I → J → ℝ) (p : I → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun j => ∑ i, p i * M i j

/-- Best-response lower bound `min_i ∑ j, q j * M i j` of a column distribution `q`. -/
def colBestPayoff (M : I → J → ℝ) (q : J → ℝ) : ℝ :=
  univ.inf' univ_nonempty fun i => ∑ j, q j * M i j

/-- Minimax value `⨅ p : StdSimplex ℝ I, max_j ∑ i, p i * M i j` (`v_max^1` in
[BlumMansour2007AGT, §4.4.2, p. 89]). -/
noncomputable def minmaxValue (M : I → J → ℝ) : ℝ :=
  ⨅ p : StdSimplex ℝ I, rowWorstLoss M p.weights

/-- Maximin value `⨆ q : StdSimplex ℝ J, min_i ∑ j, q j * M i j` (`v_min^1` in
[BlumMansour2007AGT, §4.4.2, p. 89]). -/
noncomputable def maxminValue (M : I → J → ℝ) : ℝ :=
  ⨆ q : StdSimplex ℝ J, colBestPayoff M q.weights

private def matrixAbsBound (M : I → J → ℝ) : ℝ :=
  (univ ×ˢ univ : Finset (I × J)).sup' (univ_nonempty.product univ_nonempty)
    fun ij => |M ij.1 ij.2|

private theorem abs_entry_le_matrixAbsBound (M : I → J → ℝ) (i : I) (j : J) :
    |M i j| ≤ matrixAbsBound M := by
  have hij : (i, j) ∈ (univ ×ˢ univ : Finset (I × J)) := mem_product.mpr ⟨mem_univ i, mem_univ j⟩
  exact le_sup' (fun ij : I × J => |M ij.1 ij.2|) hij

private theorem matrixAbsBound_nonneg (M : I → J → ℝ) : 0 ≤ matrixAbsBound M := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨j₀⟩ := ‹Nonempty J›
  exact (abs_nonneg (M i₀ j₀)).trans (abs_entry_le_matrixAbsBound M i₀ j₀)

private theorem bddBelow_range_rowWorstLoss (M : I → J → ℝ) :
    BddBelow (Set.range fun p : StdSimplex ℝ I => rowWorstLoss M p.weights) := by
  refine ⟨-matrixAbsBound M, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨j₀⟩ := ‹Nonempty J›
  refine le_trans ?_ (le_sup' (fun j => ∑ i, p.weights i * M i j) (mem_univ j₀))
  calc -matrixAbsBound M = ∑ i, p.weights i * (-matrixAbsBound M) := by
        rw [← sum_mul, p.total_of_fintype, one_mul]
    _ ≤ ∑ i, p.weights i * M i j₀ := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (neg_le_of_abs_le (abs_entry_le_matrixAbsBound M i j₀)) (p.weights_nonneg i)

private theorem bddAbove_range_colBestPayoff (M : I → J → ℝ) :
    BddAbove (Set.range fun q : StdSimplex ℝ J => colBestPayoff M q.weights) := by
  refine ⟨matrixAbsBound M, ?_⟩
  rintro _ ⟨q, rfl⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  refine (inf'_le (fun i => ∑ j, q.weights j * M i j) (mem_univ i₀)).trans ?_
  calc ∑ j, q.weights j * M i₀ j ≤ ∑ j, q.weights j * matrixAbsBound M :=
        sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left
            (le_of_abs_le (abs_entry_le_matrixAbsBound M i₀ j)) (q.weights_nonneg j)
    _ = matrixAbsBound M := by rw [← sum_mul, q.total_of_fintype, one_mul]

private theorem minmaxValue_le_of_weights (M : I → J → ℝ) {p : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    minmaxValue M ≤ rowWorstLoss M p := by
  have hmem : p ∈ Set.range (fun s : StdSimplex ℝ I => (s.weights : I → ℝ)) := by
    rw [StdSimplex.range_toFun_comp_weights]
    exact ⟨Set.mem_iInter.2 hp0, hp1⟩
  obtain ⟨s, rfl⟩ := hmem
  exact ciInf_le (bddBelow_range_rowWorstLoss M) s

private theorem le_maxminValue_of_weights (M : I → J → ℝ) {q : J → ℝ}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) :
    colBestPayoff M q ≤ maxminValue M := by
  have hmem : q ∈ Set.range (fun s : StdSimplex ℝ J => (s.weights : J → ℝ)) := by
    rw [StdSimplex.range_toFun_comp_weights]
    exact ⟨Set.mem_iInter.2 hq0, hq1⟩
  obtain ⟨s, rfl⟩ := hmem
  exact le_ciSup (bddAbove_range_colBestPayoff M) s

/-- Weak minimax duality: `maxminValue M ≤ minmaxValue M` for every finite real game. -/
theorem maxminValue_le_minmaxValue (M : I → J → ℝ) : maxminValue M ≤ minmaxValue M := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have : Nonempty (StdSimplex ℝ I) := ⟨StdSimplex.single i₀⟩
  have : Nonempty (StdSimplex ℝ J) := ⟨StdSimplex.single j₀⟩
  refine ciSup_le fun q => le_ciInf fun p => ?_
  calc colBestPayoff M q.weights
      ≤ ∑ i, p.weights i * colBestPayoff M q.weights := by
        rw [← sum_mul, p.total_of_fintype, one_mul]
    _ ≤ ∑ i, p.weights i * ∑ j, q.weights j * M i j :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (inf'_le (fun i' => ∑ j, q.weights j * M i' j) (mem_univ i)) (p.weights_nonneg i)
    _ = ∑ j, q.weights j * ∑ i, p.weights i * M i j := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    _ ≤ ∑ j, q.weights j * rowWorstLoss M p.weights :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (le_sup' (fun j' => ∑ i, p.weights i * M i j') (mem_univ j)) (q.weights_nonneg j)
    _ = rowWorstLoss M p.weights := by rw [← sum_mul, q.total_of_fintype, one_mul]

/-- Unconditional regret of `anytimeHedgeProb` (extending `anytimeHedge_regret_le` to `card = 1`,
where regret is `0`). -/
private theorem anytimeHedge_regret_le_all {ι : Type*} [Fintype ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ j, ℓ s j ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    ∑ t ∈ range T, ∑ j, anytimeHedgeProb ℓ t j * ℓ t j ≤
      cumLoss ℓ T k + 3 * √(T * log (Fintype.card ι)) := by
  by_cases hn : 2 ≤ Fintype.card ι
  · exact anytimeHedge_regret_le hn hℓ k
  · have : Nonempty ι := ⟨k⟩
    have hcard1 : Fintype.card ι = 1 := by
      have := Fintype.card_pos (α := ι)
      omega
    have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard1.le
    have hlhs : ∑ t ∈ range T, ∑ j, anytimeHedgeProb ℓ t j * ℓ t j = cumLoss ℓ T k := by
      unfold cumLoss
      refine sum_congr rfl fun t _ => ?_
      rw [Fintype.sum_subsingleton _ k]
      have h1 := sum_anytimeHedgeProb ℓ t
      rw [Fintype.sum_subsingleton _ k] at h1
      rw [h1, one_mul]
    rw [hlhs, hcard1, Nat.cast_one, log_one, mul_zero, sqrt_zero, mul_zero, add_zero]

/-- **Coupled `anytimeHedgeProb` approximate minimax inequality**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]: for any matrix `M₀ : I → J → ℝ` with entries in `[0, 1]`
and any horizon `T > 0`, running two `anytimeHedgeProb` learners simultaneously produces empirical
mixed strategies `p̄` and `q̄` with
`rowWorstLoss M₀ p̄ ≤ colBestPayoff M₀ q̄ + 3 * (√(ln |I|) + √(ln |J|)) / √T`. -/
theorem coupledHedge_gap_le {M₀ : I → J → ℝ} (hM₀ : ∀ i j, M₀ i j ∈ Set.Icc (0 : ℝ) 1)
    {T : ℕ} (hT : 0 < T) :
    ∃ (p_bar : I → ℝ) (q_bar : J → ℝ),
      (∀ i, 0 ≤ p_bar i) ∧ ∑ i, p_bar i = 1 ∧
      (∀ j, 0 ≤ q_bar j) ∧ ∑ j, q_bar j = 1 ∧
      rowWorstLoss M₀ p_bar ≤ colBestPayoff M₀ q_bar +
        3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) := by
  -- Construct coupled stage losses `(ℓ₁ t, ℓ₂ t)` by well-founded recursion on `t`:
  let step : ∀ t : ℕ, (∀ s < t, (I → ℝ) × (J → ℝ)) → (I → ℝ) × (J → ℝ) := fun t prev =>
    let ℓ₁_pre : ℕ → I → ℝ := fun s => if hs : s < t then (prev s hs).1 else 0
    let ℓ₂_pre : ℕ → J → ℝ := fun s => if hs : s < t then (prev s hs).2 else 0
    let pt := anytimeHedgeProb ℓ₁_pre t
    let qt := anytimeHedgeProb ℓ₂_pre t
    (fun i => ∑ j, qt j * M₀ i j, fun j => 1 - ∑ i, pt i * M₀ i j)
  let run : ℕ → (I → ℝ) × (J → ℝ) := WellFounded.fix Nat.lt_wfRel.wf step
  let ℓ₁ : ℕ → I → ℝ := fun t => (run t).1
  let ℓ₂ : ℕ → J → ℝ := fun t => (run t).2
  let p : ℕ → I → ℝ := anytimeHedgeProb ℓ₁
  let q : ℕ → J → ℝ := anytimeHedgeProb ℓ₂
  have hrun : ∀ t, run t = step t (fun s _ => run s) := fun t =>
    WellFounded.fix_eq Nat.lt_wfRel.wf step t
  have hℓ₁_eq : ∀ t i, ℓ₁ t i = ∑ j, q t j * M₀ i j := fun t i => by
    have h1 := congrArg Prod.fst (hrun t)
    have hq_eq : anytimeHedgeProb (fun s => if hs : s < t then (run s).2 else 0) t = q t :=
      anytimeHedgeProb_congr fun s hs => by simp [ℓ₂, hs]
    have hi := congrFun h1 i
    dsimp only [step] at hi
    rwa [hq_eq] at hi
  have hℓ₂_eq : ∀ t j, ℓ₂ t j = 1 - ∑ i, p t i * M₀ i j := fun t j => by
    have h2 := congrArg Prod.snd (hrun t)
    have hp_eq : anytimeHedgeProb (fun s => if hs : s < t then (run s).1 else 0) t = p t :=
      anytimeHedgeProb_congr fun s hs => by simp [ℓ₁, hs]
    have hj := congrFun h2 j
    dsimp only [step] at hj
    rwa [hp_eq] at hj
  have hℓ₁_Icc : ∀ s < T, ∀ i, ℓ₁ s i ∈ Set.Icc (0 : ℝ) 1 := fun s _ i => by
    rw [hℓ₁_eq]
    refine ⟨sum_nonneg fun j _ => mul_nonneg (anytimeHedgeProb_nonneg ℓ₂ s j) (hM₀ i j).1, ?_⟩
    calc ∑ j, q s j * M₀ i j ≤ ∑ j, q s j * 1 :=
          sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hM₀ i j).2 (anytimeHedgeProb_nonneg ℓ₂ s j)
      _ = 1 := by simp only [mul_one]; exact sum_anytimeHedgeProb ℓ₂ s
  have hℓ₂_Icc : ∀ s < T, ∀ j, ℓ₂ s j ∈ Set.Icc (0 : ℝ) 1 := fun s _ j => by
    rw [hℓ₂_eq]
    have h0 : 0 ≤ ∑ i, p s i * M₀ i j :=
      sum_nonneg fun i _ => mul_nonneg (anytimeHedgeProb_nonneg ℓ₁ s i) (hM₀ i j).1
    have h1 : ∑ i, p s i * M₀ i j ≤ 1 := by
      calc ∑ i, p s i * M₀ i j ≤ ∑ i, p s i * 1 :=
            sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hM₀ i j).2 (anytimeHedgeProb_nonneg ℓ₁ s i)
        _ = 1 := by simp only [mul_one]; exact sum_anytimeHedgeProb ℓ₁ s
    exact ⟨by linarith, by linarith⟩
  -- Constant sum `1` in every round:
  have hround_sum : ∀ t, (∑ i, p t i * ℓ₁ t i) + (∑ j, q t j * ℓ₂ t j) = 1 := fun t => by
    simp only [hℓ₁_eq, hℓ₂_eq, mul_sub, mul_one, sum_sub_distrib]
    have hswap : ∑ j, q t j * ∑ i, p t i * M₀ i j = ∑ i, p t i * ∑ j, q t j * M₀ i j := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    have hq1 : ∑ j, q t j = 1 := sum_anytimeHedgeProb ℓ₂ t
    linarith
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsT : 0 < √(T : ℝ) := sqrt_pos.mpr hT_pos
  refine ⟨timeAvg p T, timeAvg q T,
    timeAvg_nonneg fun t _ i => anytimeHedgeProb_nonneg ℓ₁ t i,
    sum_timeAvg hT fun t _ => sum_anytimeHedgeProb ℓ₁ t,
    timeAvg_nonneg fun t _ j => anytimeHedgeProb_nonneg ℓ₂ t j,
    sum_timeAvg hT fun t _ => sum_anytimeHedgeProb ℓ₂ t, ?_⟩
  -- Show that for ALL `(i, j)`, `∑ i', p_bar i' * M₀ i' j ≤ ∑ j', q_bar j' * M₀ i j' + gap`:
  have hpair : ∀ (i : I) (j : J),
      ∑ i', timeAvg p T i' * M₀ i' j ≤
        ∑ j', timeAvg q T j' * M₀ i j' +
          3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) := by
    intro i j
    have hr₁ := anytimeHedge_regret_le_all hℓ₁_Icc i
    have hr₂ := anytimeHedge_regret_le_all hℓ₂_Icc j
    have htot : (∑ t ∈ range T, ∑ i', p t i' * ℓ₁ t i') +
        (∑ t ∈ range T, ∑ j', q t j' * ℓ₂ t j') = T := by
      rw [← sum_add_distrib, sum_congr rfl fun t _ => hround_sum t]
      simp
    have hcum₁ : cumLoss ℓ₁ T i = (T : ℝ) * ∑ j', timeAvg q T j' * M₀ i j' := by
      simp only [cumLoss, hℓ₁_eq, timeAvg, div_mul_eq_mul_div, ← sum_div, sum_mul]
      rw [sum_comm, mul_div_cancel₀ _ hT_pos.ne']
    have hcum₂ : cumLoss ℓ₂ T j = (T : ℝ) - (T : ℝ) * ∑ i', timeAvg p T i' * M₀ i' j := by
      simp only [cumLoss, hℓ₂_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one,
        timeAvg, div_mul_eq_mul_div, ← sum_div, sum_mul]
      rw [sum_comm, mul_div_cancel₀ _ hT_pos.ne']
    have hsum_reg : (T : ℝ) * ∑ i', timeAvg p T i' * M₀ i' j ≤
        (T : ℝ) * ∑ j', timeAvg q T j' * M₀ i j' +
          (3 * √(T * log (Fintype.card I)) + 3 * √(T * log (Fintype.card J))) := by
      dsimp only [p, q] at htot
      linarith
    have hrad : (3 * √(T * log (Fintype.card I)) + 3 * √(T * log (Fintype.card J))) / T =
        3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) := by
      rw [sqrt_mul hT_pos.le, sqrt_mul hT_pos.le]
      calc (3 * (√(T : ℝ) * √(log (Fintype.card I))) +
            3 * (√(T : ℝ) * √(log (Fintype.card J)))) / T
          = √(T : ℝ) * (3 * (√(log (Fintype.card I)) + √(log (Fintype.card J)))) /
              (√(T : ℝ) * √(T : ℝ)) := by
              rw [mul_self_sqrt hT_pos.le]
              ring
        _ = 3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) :=
              mul_div_mul_left _ _ hsT.ne'
    have hdiv := div_le_div_of_nonneg_right hsum_reg hT_pos.le
    rw [add_div, mul_div_cancel_left₀ _ hT_pos.ne', mul_div_cancel_left₀ _ hT_pos.ne', hrad] at hdiv
    exact hdiv
  unfold rowWorstLoss colBestPayoff
  refine Finset.sup'_le _ _ fun j _ => ?_
  have hle_inf : ∑ i', timeAvg p T i' * M₀ i' j -
      3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ) ≤
      univ.inf' univ_nonempty (fun i => ∑ j', timeAvg q T j' * M₀ i j') :=
    Finset.le_inf' _ _ fun i _ => by linarith [hpair i j]
  linarith

/-- **Online-learning proof of von Neumann's minimax identity**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]: `maxminValue M = minmaxValue M` for every finite real
matrix game `M`, proved directly from `coupledHedge_gap_le` by letting `T → ∞` (without LP duality
or Sion's theorem). -/
theorem maxminValue_eq_minmaxValue (M : I → J → ℝ) : maxminValue M = minmaxValue M := by
  apply le_antisymm (maxminValue_le_minmaxValue M)
  -- Rescale `M` into `[0, 1]` via `M₀ i j = (M i j + B) / (2 * B)` (`B = matrixAbsBound M + 1`):
  set B := matrixAbsBound M + 1
  have hB : 0 < B := by linarith [matrixAbsBound_nonneg M]
  let M₀ : I → J → ℝ := fun i j => (M i j + B) / (2 * B)
  have hM₀ : ∀ i j, M₀ i j ∈ Set.Icc (0 : ℝ) 1 := fun i j => by
    have habs := abs_entry_le_matrixAbsBound M i j
    have hlow : -B ≤ M i j := by linarith [neg_le_of_abs_le habs]
    have hhigh : M i j ≤ B := by linarith [le_of_abs_le habs]
    dsimp only [M₀]
    exact ⟨div_nonneg (by linarith) (by positivity),
      (div_le_one (by positivity)).mpr (by linarith)⟩
  set C := 2 * B * (3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))))
  have hC_nn : 0 ≤ C := by
    dsimp only [C]
    positivity
  -- For every `T ≥ 1`, `minmaxValue M ≤ maxminValue M + C / √T`:
  have hgap : ∀ T : ℕ, 0 < T → minmaxValue M ≤ maxminValue M + C / √(T : ℝ) := by
    intro T hT
    obtain ⟨p_bar, q_bar, hp0, hp1, hq0, hq1, hle₀⟩ := coupledHedge_gap_le hM₀ hT
    have hrow_aff : rowWorstLoss M p_bar = 2 * B * rowWorstLoss M₀ p_bar - B := by
      have hlin : ∀ j, ∑ i, p_bar i * M i j = 2 * B * (∑ i, p_bar i * M₀ i j) - B := fun j => by
        have h1 : ∀ i, M i j = 2 * B * M₀ i j - B := fun i => by dsimp only [M₀]; field_simp; ring
        simp only [h1, mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul]
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun i _ => by ring
      unfold rowWorstLoss
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun j _ => ?_
        rw [hlin j]
        have hj := le_sup' (fun j' => ∑ i, p_bar i * M₀ i j') (mem_univ j)
        nlinarith
      · obtain ⟨j_max, _, hj_max⟩ := exists_mem_eq_sup' univ_nonempty
          (fun j' => ∑ i, p_bar i * M₀ i j')
        rw [hj_max, ← hlin j_max]
        exact le_sup' (fun j' => ∑ i, p_bar i * M i j') (mem_univ j_max)
    have hcol_aff : colBestPayoff M q_bar = 2 * B * colBestPayoff M₀ q_bar - B := by
      have hlin : ∀ i, ∑ j, q_bar j * M i j = 2 * B * (∑ j, q_bar j * M₀ i j) - B := fun i => by
        have h1 : ∀ j, M i j = 2 * B * M₀ i j - B := fun j => by dsimp only [M₀]; field_simp; ring
        simp only [h1, mul_sub, sum_sub_distrib, ← sum_mul, hq1, one_mul]
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun j _ => by ring
      unfold colBestPayoff
      apply le_antisymm
      · obtain ⟨i_min, _, hi_min⟩ := exists_mem_eq_inf' univ_nonempty
          (fun i' => ∑ j, q_bar j * M₀ i' j)
        rw [hi_min, ← hlin i_min]
        exact inf'_le (fun i' => ∑ j, q_bar j * M i' j) (mem_univ i_min)
      · refine Finset.le_inf' _ _ fun i _ => ?_
        rw [hlin i]
        have hi := inf'_le (fun i' => ∑ j, q_bar j * M₀ i' j) (mem_univ i)
        nlinarith
    have hmin_le := minmaxValue_le_of_weights M hp0 hp1
    have hmax_ge := le_maxminValue_of_weights M hq0 hq1
    have hscaled : rowWorstLoss M p_bar ≤ colBestPayoff M q_bar + C / √(T : ℝ) := by
      rw [hrow_aff, hcol_aff]
      have hmul := mul_le_mul_of_nonneg_left hle₀ (mul_nonneg zero_le_two hB.le)
      have hC_eq : 2 * B * (colBestPayoff M₀ q_bar +
          3 * (√(log (Fintype.card I)) + √(log (Fintype.card J))) / √(T : ℝ)) =
          2 * B * colBestPayoff M₀ q_bar + C / √(T : ℝ) := by
        dsimp only [C]
        ring
      linarith
    linarith
  -- Conclude `minmaxValue M ≤ maxminValue M` by contradiction via the Archimedean property:
  by_contra! hlt
  set δ := minmaxValue M - maxminValue M
  have hδ : 0 < δ := sub_pos.mpr hlt
  obtain ⟨T, hT_gt⟩ := exists_nat_gt ((C / δ) ^ 2 + 1)
  have hT_pos : 0 < T := by
    have : (0 : ℝ) < (C / δ) ^ 2 + 1 := by positivity
    have : (0 : ℝ) < T := lt_trans this hT_gt
    exact_mod_cast this
  have hsT : C / δ < √(T : ℝ) := by
    have h1 : (C / δ) ^ 2 < T := by linarith
    calc C / δ ≤ √((C / δ) ^ 2) := le_sqrt_of_sq_le le_rfl
      _ < √(T : ℝ) := sqrt_lt_sqrt (sq_nonneg _) h1
  have hC_lt : C / √(T : ℝ) < δ := by
    have hsT_pos : 0 < √(T : ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hT_pos)
    rw [div_lt_iff₀ hsT_pos]
    have := (div_lt_iff₀ hδ).mp hsT
    linarith
  linarith [hgap T hT_pos]

private theorem continuous_sum_real {X α : Type*} [TopologicalSpace X] (s : Finset α)
    {g : α → X → ℝ} (hg : ∀ a ∈ s, Continuous (g a)) :
    Continuous (fun x => ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact continuous_const
  | insert a t hat ih =>
    simp only [sum_insert hat]
    exact (hg a (mem_insert_self a t)).add (ih fun b hb => hg b (mem_insert_of_mem hb))

private theorem continuous_sup'_real {X α : Type*} [TopologicalSpace X] {s : Finset α}
    (hs : s.Nonempty) {g : α → X → ℝ} (hg : ∀ a ∈ s, Continuous (g a)) :
    Continuous (fun x => s.sup' hs fun a => g a x) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [sup'_singleton]
    exact hg a (mem_singleton_self a)
  | cons a t hat hne ih =>
    simp only [sup'_cons hne]
    exact (hg a (mem_cons_self a t)).max (ih fun b hb => hg b (mem_cons_of_mem hb))

private theorem continuous_inf'_real {X α : Type*} [TopologicalSpace X] {s : Finset α}
    (hs : s.Nonempty) {g : α → X → ℝ} (hg : ∀ a ∈ s, Continuous (g a)) :
    Continuous (fun x => s.inf' hs fun a => g a x) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [inf'_singleton]
    exact hg a (mem_singleton_self a)
  | cons a t hat hne ih =>
    simp only [inf'_cons hne]
    exact (hg a (mem_cons_self a t)).min (ih fun b hb => hg b (mem_cons_of_mem hb))

/-- **Attained minimax value via coupled no-regret learning**
[BlumMansour2007AGT, §4.4.2, pp. 89–90]: combining `maxminValue_eq_minmaxValue` with compactness of
`StdSimplex ℝ` yields optimal mixed strategies witnessing `IsMinimaxValue M (minmaxValue M)` without
using LP duality (`exists_isMinimaxValue`) or Sion's theorem. -/
theorem isMinimaxValue_minmaxValue_of_noRegret (M : I → J → ℝ) :
    IsMinimaxValue M (minmaxValue M) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have : Nonempty (StdSimplex ℝ I) := ⟨StdSimplex.single i₀⟩
  have : Nonempty (StdSimplex ℝ J) := ⟨StdSimplex.single j₀⟩
  have hcont_wI : Continuous (fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous
  have hcont_wJ : Continuous (fun q : StdSimplex ℝ J => (q.weights : J → ℝ)) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous
  have hcont_row : Continuous (fun p : StdSimplex ℝ I => rowWorstLoss M p.weights) :=
    continuous_sup'_real univ_nonempty fun j _ =>
      continuous_sum_real univ fun i _ => ((continuous_apply i).comp hcont_wI).mul continuous_const
  have hcont_col : Continuous (fun q : StdSimplex ℝ J => colBestPayoff M q.weights) :=
    continuous_inf'_real univ_nonempty fun i _ =>
      continuous_sum_real univ fun j _ => ((continuous_apply j).comp hcont_wJ).mul continuous_const
  obtain ⟨p_opt, -, hp_min⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hcont_row.continuousOn
  obtain ⟨q_opt, -, hq_max⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont_col.continuousOn
  have hp_val : rowWorstLoss M p_opt.weights = minmaxValue M := by
    apply le_antisymm
    · exact le_ciInf fun p => hp_min (Set.mem_univ p)
    · exact ciInf_le (bddBelow_range_rowWorstLoss M) p_opt
  have hq_val : colBestPayoff M q_opt.weights = maxminValue M := by
    apply le_antisymm
    · exact le_ciSup (bddAbove_range_colBestPayoff M) q_opt
    · exact ciSup_le fun q => hq_max (Set.mem_univ q)
  refine ⟨⟨p_opt, fun j => ?_⟩, q_opt, fun i => ?_⟩
  · rw [← hp_val]
    exact le_sup' (fun j' => ∑ i, p_opt.weights i * M i j') (mem_univ j)
  · rw [← maxminValue_eq_minmaxValue M, ← hq_val]
    exact inf'_le (fun i' => ∑ j, q_opt.weights j * M i' j) (mem_univ i)

end OnlineMinimax

end Cslib.MachineLearning.OnlineLearning.Experts
