/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Bimatrix.CorrelatedPolytope
import CslibFrontier.GameTheory.Bimatrix.ZeroSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for zero-sum LP duality and the correlated-equilibrium polytope

Kernel-checked witnesses exercising `Bimatrix.ZeroSum` and `Bimatrix.CorrelatedPolytope` as an
ordinary `module` client:

1. **Zero-sum matrix games and [TardosVazirani2007], Theorem 1.11**:
   * `2 × 2` Matching Pennies (`zeroSum !![1, -1; -1, 1]`): unique minimax value `0`, optimal
     primal/dual `(1/2, 1/2)`, negative witnesses for non-feasible pure strategies and suboptimal
     bounds, and `isMinimaxValue_transpose_iff`.
   * Rectangular `2 × 3` zero-sum game (`zeroSum !![2, 2, 3; 2, 2, 1]`): minimax value `2` with
     multiple optimal row and column strategies (`![1, 0]` vs `![1/2, 1/2]`, `![1, 0, 0]` vs
     `![0, 1, 0]`), exercising `IsZeroSum.isNash_exchange`, `IsZeroSum.payoff₁_eq_of_isNash`,
     `IsZeroSum.convex_isNash`, and suboptimal action witnesses.
2. **Degenerate `2 × 2` boundary witnesses (necessity of `IsNondegenerate`)**:
   * `evenNashGame = ⟨!![1, 0; 0, 0], !![1, 0; 0, 0]⟩`: degenerate `2 × 2` game with a finite even
     number (`ncard = 2`) of Nash equilibria.
   * `degPolyGame = ⟨!![1, 0; 0, 0], !![0, 0; 0, 1]⟩`: degenerate `2 × 2` game exhibiting a Nash
     equilibrium `(![1, 0], ![1/2, 1/2])` with unequal support sizes (`1 ≠ 2`), strict inclusion
     `Function.support x ⊂ {j | IsPureBestResponse₂ x j}` at `(![1, 0], ![1, 0])`, and non-extreme
     product matrix `vecMulVec ![1, 0] ![1/2, 1/2] ∉ correlatedPolytope.extremePoints ℝ`.
3. **Three-player non-vertex Nash equilibrium ([Papadimitriou2007], Section 2.7.1, pp. 47–48)**:
   * `oddCyclePennies : CostGame (Fin 3) (fun _ => Bool)`: three-player odd-cycle matching pennies,
     whose **unique** mixed Nash equilibrium is uniform `(1/2, 1/2)` for every player, yet whose
     induced product distribution (`1/8` on each of the `8` profiles) is the midpoint of the
     distinct even-parity and odd-parity correlated equilibria (`∉ extremePoints ℝ`).
4. **Chicken ([Papadimitriou2007], Figure 2.4) and Traffic Light ([TardosVazirani2007],
   Example 1.10)**:
   * Extreme-point membership and unique linear-objective maximizer for the three Nash equilibria
     of `chickenGame`, `CostGame` correlated-equilibrium bridges, and strict `CE \ conv(NE)`
     welfare separation.
   * Exact `(-100, 1, 0)` Traffic Light matrix of [TardosVazirani2007], Example 1.10 (pp. 14–15),
     checking its `ε = 1/101` symmetric mixed equilibrium as an extreme point of
     `correlatedPolytope`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.ZeroSumCorrelatedPolytope

open Convexity Cslib.GameTheory Cslib.GameTheory.BimatrixGame Finset Function Matrix

private theorem isMixedStrategy_fin2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    IsMixedStrategy ![a, b] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> assumption,
    by simp [Fin.sum_univ_two, h]⟩

private theorem isMixedStrategy_fin3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : IsMixedStrategy ![a, b, c] :=
  isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> assumption,
    by simp [Fin.sum_univ_three, h]⟩

/-! ### 1. Zero-sum matrix games and Theorem 1.11 -/

private def penniesMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -1; -1, 1]

private theorem pennies_maximinFeasible :
    IsMaximinFeasible penniesMat ![1 / 2, 1 / 2] 0 := by
  refine ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num), fun j => ?_⟩
  fin_cases j <;> norm_num [penniesMat, vecMul, dotProduct, Fin.sum_univ_two]

private theorem pennies_minimaxFeasible :
    IsMinimaxFeasible penniesMat ![1 / 2, 1 / 2] 0 := by
  refine ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num), fun i => ?_⟩
  fin_cases i <;> norm_num [penniesMat, mulVec, dotProduct, Fin.sum_univ_two]

theorem pennies_lpOptimal :
    IsMaximinOptimal penniesMat ![1 / 2, 1 / 2] 0 ∧
      IsMinimaxOptimal penniesMat ![1 / 2, 1 / 2] 0 :=
  isMaximinOptimal_and_isMinimaxOptimal_of_feasible pennies_maximinFeasible pennies_minimaxFeasible

/-- Theorem 1.11 applied to Matching Pennies: optimal primal/dual strategies form a Nash
equilibrium with equilibrium payoff `0`, and `0` is the `IsMinimaxValue` of `penniesMatᵀ`. -/
example : (zeroSum penniesMat).IsNash ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] ∧
    (zeroSum penniesMat).payoff₁ ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] = 0 ∧
    Cslib.Probability.IsMinimaxValue penniesMatᵀ 0 :=
  ⟨isNash_zeroSum_of_lpOptimal pennies_lpOptimal.1 pennies_lpOptimal.2,
    payoff₁_zeroSum_eq_of_lpOptimal pennies_lpOptimal.1 pennies_lpOptimal.2,
    (isMinimaxValue_transpose_iff penniesMat 0).2
      ⟨⟨![1 / 2, 1 / 2], pennies_lpOptimal.1⟩, ⟨![1 / 2, 1 / 2], pennies_lpOptimal.2⟩⟩⟩

/-- Negative witness: no pure row strategy guarantees value `0` in Matching Pennies, and `-1` is
maximin-feasible for `(1/2, 1/2)` but not maximin-optimal. -/
example : ¬IsMaximinFeasible penniesMat ![1, 0] 0 ∧
    IsMaximinFeasible penniesMat ![1 / 2, 1 / 2] (-1) ∧
    ¬IsMaximinOptimal penniesMat ![1 / 2, 1 / 2] (-1) := by
  refine ⟨fun h => ?_, ?_, fun h => ?_⟩
  · have h1 := h.le_vecMul 1
    norm_num [penniesMat, vecMul, dotProduct, Fin.sum_univ_two] at h1
  · refine ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num), fun j => ?_⟩
    fin_cases j <;> norm_num [penniesMat, vecMul, dotProduct, Fin.sum_univ_two]
  · have hle := h.2 ![1 / 2, 1 / 2] 0 pennies_maximinFeasible
    linarith

/-- Rectangular `2 × 3` zero-sum game with minimax value `2` and multiple optimal row and column
strategies. -/
private def rectMat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![2, 2, 3; 2, 2, 1]

private theorem rect_nash₁ : (zeroSum rectMat).IsNash ![1, 0] ![1, 0, 0] := by
  have hx : IsMaximinFeasible rectMat ![1, 0] 2 := by
    refine ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num), fun j => ?_⟩
    fin_cases j <;> norm_num [rectMat, vecMul, dotProduct, Fin.sum_univ_two]
  have hy : IsMinimaxFeasible rectMat ![1, 0, 0] 2 := by
    refine ⟨isMixedStrategy_fin3 zero_le_one le_rfl le_rfl (by norm_num), fun i => ?_⟩
    fin_cases i <;> norm_num [rectMat, mulVec, dotProduct, Fin.sum_univ_three]
  obtain ⟨hx_opt, hy_opt⟩ := isMaximinOptimal_and_isMinimaxOptimal_of_feasible hx hy
  exact isNash_zeroSum_of_lpOptimal hx_opt hy_opt

private theorem rect_nash₂ : (zeroSum rectMat).IsNash ![1 / 2, 1 / 2] ![0, 1, 0] := by
  have hx : IsMaximinFeasible rectMat ![1 / 2, 1 / 2] 2 := by
    refine ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num), fun j => ?_⟩
    fin_cases j <;> norm_num [rectMat, vecMul, dotProduct, Fin.sum_univ_two]
  have hy : IsMinimaxFeasible rectMat ![0, 1, 0] 2 := by
    refine ⟨isMixedStrategy_fin3 le_rfl zero_le_one le_rfl (by norm_num), fun i => ?_⟩
    fin_cases i <;> norm_num [rectMat, mulVec, dotProduct, Fin.sum_univ_three]
  obtain ⟨hx_opt, hy_opt⟩ := isMaximinOptimal_and_isMinimaxOptimal_of_feasible hx hy
  exact isNash_zeroSum_of_lpOptimal hx_opt hy_opt

/-- Exchangeability, unique value, convexity, and suboptimal boundary witnesses on `rectMat`. -/
example :
    (![1, 0] : Fin 2 → ℝ) ≠ ![1 / 2, 1 / 2] ∧
    (![1, 0, 0] : Fin 3 → ℝ) ≠ ![0, 1, 0] ∧
    (zeroSum rectMat).IsNash ![1, 0] ![0, 1, 0] ∧
    (zeroSum rectMat).IsNash ![1 / 2, 1 / 2] ![1, 0, 0] ∧
    (zeroSum rectMat).payoff₁ ![1, 0] ![1, 0, 0] =
      (zeroSum rectMat).payoff₁ ![1 / 2, 1 / 2] ![0, 1, 0] ∧
    (zeroSum rectMat).IsNash ((1 / 2 : ℝ) • ![1, 0] + (1 / 2 : ℝ) • ![1 / 2, 1 / 2])
      ((1 / 2 : ℝ) • ![1, 0, 0] + (1 / 2 : ℝ) • ![0, 1, 0]) ∧
    ¬(zeroSum rectMat).IsNash ![0, 1] ![1, 0, 0] ∧
    ¬(zeroSum rectMat).IsNash ![1, 0] ![0, 0, 1] := by
  have hzs := isZeroSum_zeroSum rectMat
  refine ⟨?_, ?_, hzs.isNash_exchange rect_nash₁ rect_nash₂,
    hzs.isNash_exchange rect_nash₂ rect_nash₁,
    hzs.payoff₁_eq_of_isNash rect_nash₁ rect_nash₂,
    hzs.convex_isNash (x := (![1, 0], ![1, 0, 0])) rect_nash₁
      (y := (![1 / 2, 1 / 2], ![0, 1, 0])) rect_nash₂ (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num),
    fun h => ?_, fun h => ?_⟩
  · intro heq
    have h0 := congrFun heq 0
    norm_num at h0
  · intro heq
    have h0 := congrFun heq 0
    norm_num at h0
  · obtain ⟨hx, -⟩ := isNash_zeroSum_iff_lpOptimal_payoff₁.1 h
    have hv := eq_of_isMaximinOptimal_of_isMinimaxOptimal hx
      (isNash_zeroSum_iff_lpOptimal_payoff₁.1 rect_nash₁).2
    have hpay : (zeroSum rectMat).payoff₁ ![1, 0] ![1, 0, 0] = 2 := by
      norm_num [payoff₁_eq_dotProduct, rectMat, mulVec, dotProduct, Fin.sum_univ_two,
        Fin.sum_univ_three]
    have hj := hx.isMaximinFeasible.le_vecMul 2
    rw [hv, hpay] at hj
    norm_num [rectMat, vecMul, dotProduct, Fin.sum_univ_two] at hj
  · obtain ⟨-, hy⟩ := isNash_zeroSum_iff_lpOptimal_payoff₁.1 h
    have hv := eq_of_isMaximinOptimal_of_isMinimaxOptimal
      (isNash_zeroSum_iff_lpOptimal_payoff₁.1 rect_nash₁).1 hy
    have hpay : (zeroSum rectMat).payoff₁ ![1, 0] ![1, 0, 0] = 2 := by
      norm_num [payoff₁_eq_dotProduct, rectMat, mulVec, dotProduct, Fin.sum_univ_two,
        Fin.sum_univ_three]
    have hi := hy.isMinimaxFeasible.mulVec_le 0
    rw [← hv, hpay] at hi
    norm_num [rectMat, mulVec, dotProduct, Fin.sum_univ_three] at hi

/-! ### 2. Degenerate `2 × 2` boundary witnesses -/

/-- A degenerate `2 × 2` game with finitely many Nash equilibria of **even** cardinality (`2`):
`{(![1, 0], ![1, 0]), (![0, 1], ![0, 1])}`. -/
private def evenNashGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![1, 0; 0, 0], !![1, 0; 0, 0]⟩

private theorem fin2_eq (v : Fin 2 → ℝ) : v = ![v 0, v 1] := by
  funext i; fin_cases i <;> rfl

theorem evenNashGame_not_isNondegenerate : ¬evenNashGame.IsNondegenerate := by
  intro h
  have h1 := (isNondegenerate_iff.1 h).1 ![0, 1]
    (isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num))
  have hbr : {j | evenNashGame.IsPureBestResponse₂ ![0, 1] j} = Set.univ := by
    refine Set.eq_univ_of_forall fun j => isPureBestResponse₂_iff.2 fun j' => ?_
    fin_cases j <;> fin_cases j' <;>
      norm_num [evenNashGame, vecMul, dotProduct, Fin.sum_univ_two]
  have hsupp : Function.support (![0, 1] : Fin 2 → ℝ) = {1} := by
    ext i; fin_cases i <;> simp
  rw [hbr, hsupp, Set.ncard_univ, Set.ncard_singleton, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h1
  omega

theorem evenNashGame_setOf_isNash :
    {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | evenNashGame.IsNash p.1 p.2} =
      {(![1, 0], ![1, 0]), (![0, 1], ![0, 1])} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
    have hx := h₁.isMixedStrategy
    have hy := h₂.isMixedStrategy
    have hxs : x 0 + x 1 = 1 := by simpa only [Fin.sum_univ_two] using hx.sum_eq_one
    have hys : y 0 + y 1 = 1 := by simpa only [Fin.sum_univ_two] using hy.sum_eq_one
    rcases (hy.nonneg 0).eq_or_lt with hy0 | hy0
    · have hy1 : y 1 = 1 := by linarith
      have hbr2 := isPureBestResponse₂_iff.1 ((isBestResponse₂_iff.1 h₂).2 1 (by linarith)) 0
      simp only [evenNashGame, vecMul, dotProduct, Fin.sum_univ_two, of_apply, cons_val',
        cons_val_zero, cons_val_one, empty_val', cons_val_fin_one] at hbr2
      have hx0 : x 0 = 0 := le_antisymm (by linarith) (hx.nonneg 0)
      have hx1 : x 1 = 1 := by linarith
      right
      exact ⟨by rw [fin2_eq x, hx0, hx1], by rw [fin2_eq y, ← hy0, hy1]⟩
    · have hx1 : x 1 = 0 := by
        by_contra hx1_ne
        have hx1_pos : 0 < x 1 := (hx.nonneg 1).lt_of_ne' hx1_ne
        have hbr1 := isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 h₁).2 1 hx1_pos) 0
        simp only [evenNashGame, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val',
          cons_val_zero, cons_val_one, empty_val', cons_val_fin_one] at hbr1
        linarith
      have hx0 : x 0 = 1 := by linarith
      have hy1 : y 1 = 0 := by
        by_contra hy1_ne
        have hy1_pos : 0 < y 1 := (hy.nonneg 1).lt_of_ne' hy1_ne
        have hbr2 := isPureBestResponse₂_iff.1 ((isBestResponse₂_iff.1 h₂).2 1 hy1_pos) 0
        simp only [evenNashGame, vecMul, dotProduct, Fin.sum_univ_two, of_apply, cons_val',
          cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, hx0, hx1] at hbr2
        linarith
      have hy0_one : y 0 = 1 := by linarith
      left
      exact ⟨by rw [fin2_eq x, hx0, hx1], by rw [fin2_eq y, hy0_one, hy1]⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl
        (by norm_num), fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
        isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num),
          fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
      · revert hi; fin_cases i <;> fin_cases i' <;>
          norm_num [evenNashGame, mulVec, dotProduct, Fin.sum_univ_two]
      · revert hj; fin_cases j <;> fin_cases j' <;>
          norm_num [evenNashGame, vecMul, dotProduct, Fin.sum_univ_two]
    · refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 le_rfl zero_le_one
        (by norm_num), fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
        isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num),
          fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
      · revert hi; fin_cases i <;> fin_cases i' <;>
          norm_num [evenNashGame, mulVec, dotProduct, Fin.sum_univ_two]
      · revert hj; fin_cases j <;> fin_cases j' <;>
          norm_num [evenNashGame, vecMul, dotProduct, Fin.sum_univ_two]

theorem evenNashGame_ncard_eq_two :
    {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | evenNashGame.IsNash p.1 p.2}.ncard = 2 := by
  rw [evenNashGame_setOf_isNash, Set.ncard_pair]
  intro h
  have h0 := congrFun (Prod.mk.inj h).1 0
  norm_num at h0

/-- A degenerate `2 × 2` game where `(![1, 0], ![1/2, 1/2])` has unequal support sizes (`1 ≠ 2`)
and is **not** an extreme point of `correlatedPolytope`. -/
private def degPolyGame : BimatrixGame (Fin 2) (Fin 2) :=
  ⟨!![1, 0; 0, 0], !![0, 0; 0, 1]⟩

private theorem degPolyGame_nash_pure₀ : degPolyGame.IsNash ![1, 0] ![1, 0] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl
    (by norm_num), fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
    isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl (by norm_num),
      fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · revert hi; fin_cases i <;> fin_cases i' <;>
      norm_num [degPolyGame, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj; fin_cases j <;> fin_cases j' <;>
      norm_num [degPolyGame, vecMul, dotProduct, Fin.sum_univ_two]

private theorem degPolyGame_nash_pure₁ : degPolyGame.IsNash ![1, 0] ![0, 1] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl
    (by norm_num), fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
    isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 le_rfl zero_le_one (by norm_num),
      fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · revert hi; fin_cases i <;> fin_cases i' <;>
      norm_num [degPolyGame, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj; fin_cases j <;> fin_cases j' <;>
      norm_num [degPolyGame, vecMul, dotProduct, Fin.sum_univ_two]

private theorem degPolyGame_nash_mixed : degPolyGame.IsNash ![1, 0] ![1 / 2, 1 / 2] := by
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 zero_le_one le_rfl
    (by norm_num), fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩,
    isBestResponse₂_iff.2 ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num),
      fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · revert hi; fin_cases i <;> fin_cases i' <;>
      norm_num [degPolyGame, mulVec, dotProduct, Fin.sum_univ_two]
  · revert hj; fin_cases j <;> fin_cases j' <;>
      norm_num [degPolyGame, vecMul, dotProduct, Fin.sum_univ_two]

/-- `IsNondegenerate` is essential for `IsNash.ncard_support_eq`,
`IsNondegenerate.support_right_eq_of_isNash`, and Theorem 2.5
(`IsNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope`). -/
theorem degPolyGame_counterexamples :
    degPolyGame.IsNash ![1, 0] ![1 / 2, 1 / 2] ∧
    (Function.support (![1, 0] : Fin 2 → ℝ)).ncard = 1 ∧
    (Function.support (![1 / 2, 1 / 2] : Fin 2 → ℝ)).ncard = 2 ∧
    Function.support (![1, 0] : Fin 2 → ℝ) ≠ {j | degPolyGame.IsPureBestResponse₂ ![1, 0] j} ∧
    Matrix.vecMulVec (![1, 0] : Fin 2 → ℝ) ![1 / 2, 1 / 2] ∉
      degPolyGame.correlatedPolytope.extremePoints ℝ := by
  refine ⟨degPolyGame_nash_mixed, ?_, ?_, ?_, ?_⟩
  · have hs : Function.support (![1, 0] : Fin 2 → ℝ) = {0} := by
      ext i; fin_cases i <;> simp
    rw [hs, Set.ncard_singleton]
  · have hs : Function.support (![1 / 2, 1 / 2] : Fin 2 → ℝ) = Set.univ := by
      ext i; fin_cases i <;> norm_num [Function.mem_support]
    rw [hs, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro heq
    have hmem : (1 : Fin 2) ∈ {j | degPolyGame.IsPureBestResponse₂ ![1, 0] j} := by
      rw [Set.mem_ofPred_eq, isPureBestResponse₂_iff]
      intro j'
      fin_cases j' <;> norm_num [degPolyGame, vecMul, dotProduct, Fin.sum_univ_two]
    rw [← heq] at hmem
    exact hmem rfl
  · intro hext
    let P₀ := Matrix.vecMulVec (![1, 0] : Fin 2 → ℝ) ![1, 0]
    let P₁ := Matrix.vecMulVec (![1, 0] : Fin 2 → ℝ) ![0, 1]
    have hP₀ : P₀ ∈ degPolyGame.correlatedPolytope :=
      mem_correlatedPolytope_iff.2 degPolyGame_nash_pure₀.isCorrelated_vecMulVec
    have hP₁ : P₁ ∈ degPolyGame.correlatedPolytope :=
      mem_correlatedPolytope_iff.2 degPolyGame_nash_pure₁.isCorrelated_vecMulVec
    have hseg : Matrix.vecMulVec (![1, 0] : Fin 2 → ℝ) ![1 / 2, 1 / 2] ∈
        openSegment ℝ P₀ P₁ := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [P₀, P₁, vecMulVec_apply]
    have heq := (mem_extremePoints_iff_left.1 hext).2 P₀ hP₀ P₁ hP₁ hseg
    have h00 := congrFun (congrFun heq 0) 0
    norm_num [P₀, vecMulVec_apply] at h00

/-! ### 3. Three-player non-vertex Nash equilibrium ([Papadimitriou2007], p. 48) -/

/-- Three-player odd-cycle matching pennies: player `0` wants `s 0 = s 1`, player `1` wants
`s 1 = s 2`, and player `2` wants `s 2 ≠ s 0`. -/
private def oddCyclePennies : CostGame (Fin 3) (fun _ => Bool) where
  cost
    | 0 => fun s => if s 0 = s 1 then 0 else 1
    | 1 => fun s => if s 1 = s 2 then 0 else 1
    | 2 => fun s => if s 2 = s 0 then 1 else 0

private noncomputable def unif₃ : Fin 3 → Bool → ℝ := fun _ _ => 1 / 2

private def profileFin3Equiv : (Fin 3 → Bool) ≃ Bool × Bool × Bool where
  toFun s := (s 0, s 1, s 2)
  invFun
    | (b₀, b₁, b₂), 0 => b₀
    | (b₀, b₁, b₂), 1 => b₁
    | (b₀, b₁, b₂), 2 => b₂
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

private theorem sum_fin3_bool (f : (Fin 3 → Bool) → ℝ) :
    ∑ s : Fin 3 → Bool, f s =
      ∑ x : Bool × Bool × Bool, f (profileFin3Equiv.symm x) := by
  rw [← profileFin3Equiv.symm.sum_comp]

private theorem oddCyclePennies_deviationCost (p : Fin 3 → Bool → ℝ)
    (hp0 : p 0 false + p 0 true = 1) (hp1 : p 1 false + p 1 true = 1)
    (hp2 : p 2 false + p 2 true = 1) :
    oddCyclePennies.deviationCost p 0 false = p 1 true ∧
    oddCyclePennies.deviationCost p 0 true = p 1 false ∧
    oddCyclePennies.deviationCost p 1 false = p 2 true ∧
    oddCyclePennies.deviationCost p 1 true = p 2 false ∧
    oddCyclePennies.deviationCost p 2 false = p 0 false ∧
    oddCyclePennies.deviationCost p 2 true = p 0 true := by
  have hprod : ∀ s : Fin 3 → Bool, productWeight p s = p 0 (s 0) * p 1 (s 1) * p 2 (s 2) := by
    intro s
    rw [productWeight_def, Fin.prod_univ_three]
  have hp0' : p 0 false = 1 - p 0 true := by linarith
  have hp1' : p 1 false = 1 - p 1 true := by linarith
  have hp2' : p 2 false = 1 - p 2 true := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [CostGame.deviationCost_def, sum_fin3_bool]
    simp only [hprod, Fintype.sum_prod_type, Fintype.sum_bool, profileFin3Equiv,
      Equiv.coe_fn_symm_mk, oddCyclePennies, Function.update]
    norm_num
    try rw [hp0']
    try rw [hp1']
    try rw [hp2']
    ring

/-- `unif₃` (`1/2` on each action for all `3` players) is the **unique** mixed Nash equilibrium of
`oddCyclePennies`. -/
theorem oddCyclePennies_isMixedNash_iff (p : Fin 3 → Bool → ℝ) :
    oddCyclePennies.IsMixedNash p ↔ p = unif₃ := by
  constructor
  · intro h
    have hp0 : p 0 false + p 0 true = 1 := by
      have h0 := (h.1 0).sum_eq_one; rw [Fintype.sum_bool] at h0; linarith
    have hp1 : p 1 false + p 1 true = 1 := by
      have h1 := (h.1 1).sum_eq_one; rw [Fintype.sum_bool] at h1; linarith
    have hp2 : p 2 false + p 2 true = 1 := by
      have h2 := (h.1 2).sum_eq_one; rw [Fintype.sum_bool] at h2; linarith
    obtain ⟨hd0f, hd0t, hd1f, hd1t, hd2f, hd2t⟩ :=
      oddCyclePennies_deviationCost p hp0 hp1 hp2
    have h0_le_1 : p 1 true < 1 / 2 → p 0 true = 0 := by
      intro hlt
      by_contra hne
      have hpos : 0 < p 0 true := ((h.1 0).nonneg true).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 0 hpos
      have hle := h.2 0 false
      linarith
    have h0_ge_1 : 1 / 2 < p 1 true → p 0 false = 0 := by
      intro hgt
      by_contra hne
      have hpos : 0 < p 0 false := ((h.1 0).nonneg false).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 0 hpos
      have hle := h.2 0 true
      linarith
    have h1_le_2 : p 2 true < 1 / 2 → p 1 true = 0 := by
      intro hlt
      by_contra hne
      have hpos : 0 < p 1 true := ((h.1 1).nonneg true).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 1 hpos
      have hle := h.2 1 false
      linarith
    have h1_ge_2 : 1 / 2 < p 2 true → p 1 false = 0 := by
      intro hgt
      by_contra hne
      have hpos : 0 < p 1 false := ((h.1 1).nonneg false).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 1 hpos
      have hle := h.2 1 true
      linarith
    have h2_le_0 : 1 / 2 < p 0 true → p 2 true = 0 := by
      intro hgt
      by_contra hne
      have hpos : 0 < p 2 true := ((h.1 2).nonneg true).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 2 hpos
      have hle := h.2 2 false
      linarith
    have h2_ge_0 : p 0 true < 1 / 2 → p 2 false = 0 := by
      intro hlt
      by_contra hne
      have hpos : 0 < p 2 false := ((h.1 2).nonneg false).lt_of_ne' hne
      have heq := h.deviationCost_eq_of_pos 2 hpos
      have hle := h.2 2 true
      linarith
    have hp1t : p 1 true = 1 / 2 := by
      rcases lt_trichotomy (p 1 true) (1 / 2) with hlt | heq | hgt
      · have hp0t := h0_le_1 hlt
        have hp2f := h2_ge_0 (by linarith)
        have hp1f := h1_ge_2 (by linarith)
        linarith
      · exact heq
      · have hp0f := h0_ge_1 hgt
        have hp2t := h2_le_0 (by linarith)
        have hp1t := h1_le_2 (by linarith)
        linarith
    have hp0t : p 0 true = 1 / 2 := by
      rcases lt_trichotomy (p 0 true) (1 / 2) with hlt | heq | hgt
      · have hp2f := h2_ge_0 hlt
        have hp1f := h1_ge_2 (by linarith)
        linarith
      · exact heq
      · have hp2t := h2_le_0 hgt
        have hp1t0 := h1_le_2 (by linarith)
        linarith
    have hp2t : p 2 true = 1 / 2 := by
      rcases lt_trichotomy (p 2 true) (1 / 2) with hlt | heq | hgt
      · have hp1t0 := h1_le_2 hlt
        linarith
      · exact heq
      · have hp1f := h1_ge_2 hgt
        linarith
    funext i b
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    rcases hi with rfl | rfl | rfl <;> cases b <;> dsimp only [unif₃] <;> linarith
  · rintro rfl
    have hmix : ∀ i : Fin 3, IsMixedStrategy (unif₃ i) := fun _ =>
      isMixedStrategy_iff.2 ⟨fun b => by cases b <;> norm_num [unif₃],
        by norm_num [unif₃, Fintype.sum_bool]⟩
    obtain ⟨hd0f, hd0t, hd1f, hd1t, hd2f, hd2t⟩ :=
      oddCyclePennies_deviationCost unif₃ (by norm_num [unif₃]) (by norm_num [unif₃])
        (by norm_num [unif₃])
    refine ⟨hmix, fun i a => ?_⟩
    rw [← oddCyclePennies.sum_mul_deviationCost_eq_expectedCost unif₃ (hmix i).sum_eq_one,
      Fintype.sum_bool]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    rcases hi with rfl | rfl | rfl <;> cases a
    · rw [hd0t, hd0f]; norm_num [unif₃]
    · rw [hd0t, hd0f]; norm_num [unif₃]
    · rw [hd1t, hd1f]; norm_num [unif₃]
    · rw [hd1t, hd1f]; norm_num [unif₃]
    · rw [hd2t, hd2f]; norm_num [unif₃]
    · rw [hd2t, hd2f]; norm_num [unif₃]

private def oddCycleCEPolytope : Set ((Fin 3 → Bool) → ℝ) :=
  {w | IsMixedStrategy w ∧
    ∀ (i : Fin 3) (δ : Bool → Bool),
      ∑ s, w s * oddCyclePennies.cost i s ≤
        ∑ s, w s * oddCyclePennies.cost i (update s i (δ (s i)))}

private noncomputable def evenParityWeight (s : Fin 3 → Bool) : ℝ :=
  if xor (s 0) (xor (s 1) (s 2)) = false then 1 / 4 else 0

private noncomputable def oddParityWeight (s : Fin 3 → Bool) : ℝ :=
  if xor (s 0) (xor (s 1) (s 2)) = true then 1 / 4 else 0

/-- **Three-player failure of Theorem 2.5** ([Papadimitriou2007], Section 2.7.1, pp. 47–48):
`oddCyclePennies` has a unique mixed Nash equilibrium `unif₃`, yet its induced product distribution
`productWeight unif₃` is the midpoint of `evenParityWeight` and `oddParityWeight` in
`oddCycleCEPolytope`, hence is **not** an extreme point of `oddCycleCEPolytope`. -/
theorem oddCyclePennies_productWeight_not_mem_extremePoints :
    oddCyclePennies.IsMixedNash unif₃ ∧
    evenParityWeight ∈ oddCycleCEPolytope ∧
    oddParityWeight ∈ oddCycleCEPolytope ∧
    evenParityWeight ≠ oddParityWeight ∧
    productWeight unif₃ ∉ oddCycleCEPolytope.extremePoints ℝ := by
  have hunif : oddCyclePennies.IsMixedNash unif₃ :=
    (oddCyclePennies_isMixedNash_iff unif₃).2 rfl
  have heven : evenParityWeight ∈ oddCycleCEPolytope := by
    refine ⟨isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩, fun i δ => ?_⟩
    · dsimp only [evenParityWeight]; split_ifs <;> norm_num
    · rw [sum_fin3_bool]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, evenParityWeight, profileFin3Equiv,
        Equiv.coe_fn_symm_mk]
      norm_num
    · rw [sum_fin3_bool, sum_fin3_bool]
      fin_cases i <;> cases hF : δ false <;> cases hT : δ true <;>
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, evenParityWeight, profileFin3Equiv,
          Equiv.coe_fn_symm_mk, oddCyclePennies, Function.update, hF, hT] <;>
        norm_num
  have hodd : oddParityWeight ∈ oddCycleCEPolytope := by
    refine ⟨isMixedStrategy_iff.2 ⟨fun s => ?_, ?_⟩, fun i δ => ?_⟩
    · dsimp only [oddParityWeight]; split_ifs <;> norm_num
    · rw [sum_fin3_bool]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, oddParityWeight, profileFin3Equiv,
        Equiv.coe_fn_symm_mk]
      norm_num
    · rw [sum_fin3_bool, sum_fin3_bool]
      fin_cases i <;> cases hF : δ false <;> cases hT : δ true <;>
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, oddParityWeight, profileFin3Equiv,
          Equiv.coe_fn_symm_mk, oddCyclePennies, Function.update, hF, hT] <;>
        norm_num
  have hne : evenParityWeight ≠ oddParityWeight := by
    intro h
    have h0 := congrFun h (fun _ => false)
    norm_num [evenParityWeight, oddParityWeight] at h0
  refine ⟨hunif, heven, hodd, hne, fun hext => ?_⟩
  have hseg : productWeight unif₃ ∈ openSegment ℝ evenParityWeight oddParityWeight := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext s
    rw [productWeight_def, Fin.prod_univ_three]
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      norm_num [unif₃, evenParityWeight, oddParityWeight, h0, h1, h2]
  have heq := (mem_extremePoints_iff_left.1 hext).2 evenParityWeight heven oddParityWeight hodd hseg
  have h0 := congrFun heq (fun _ => false)
  rw [productWeight_def, Fin.prod_univ_three] at h0
  norm_num [evenParityWeight, unif₃] at h0

/-! ### 4. Chicken ([Papadimitriou2007]) and Traffic Light ([TardosVazirani2007], Example 1.10) -/

/-- All three Nash equilibria of `chickenGame` are extreme points of
`chickenGame.correlatedPolytope` by Theorem 2.5, and the mixed equilibrium `(![1/2, 1/2],
![1/2, 1/2])` is the unique maximizer of some linear objective over
`chickenGame.correlatedPolytope`. -/
example :
    Matrix.vecMulVec (![0, 1] : Fin 2 → ℝ) ![1, 0] ∈
      chickenGame.correlatedPolytope.extremePoints ℝ ∧
    Matrix.vecMulVec (![1, 0] : Fin 2 → ℝ) ![0, 1] ∈
      chickenGame.correlatedPolytope.extremePoints ℝ ∧
    Matrix.vecMulVec (![1 / 2, 1 / 2] : Fin 2 → ℝ) ![1 / 2, 1 / 2] ∈
      chickenGame.correlatedPolytope.extremePoints ℝ ∧
    ∃ W : Matrix (Fin 2) (Fin 2) ℝ, ∀ P ∈ chickenGame.correlatedPolytope,
      (∑ i, ∑ j, W i j * P i j ≤
        ∑ i, ∑ j, W i j * Matrix.vecMulVec (![1 / 2, 1 / 2] : Fin 2 → ℝ) ![1 / 2, 1 / 2] i j) ∧
      (∑ i, ∑ j, W i j * P i j =
        ∑ i, ∑ j, W i j * Matrix.vecMulVec (![1 / 2, 1 / 2] : Fin 2 → ℝ) ![1 / 2, 1 / 2] i j ↔
        P = Matrix.vecMulVec ![1 / 2, 1 / 2] ![1 / 2, 1 / 2]) := by
  have hN₁ : chickenGame.IsNash ![0, 1] ![1, 0] :=
    chickenGame_isNash_iff.2 (.inl ⟨rfl, rfl⟩)
  have hN₂ : chickenGame.IsNash ![1, 0] ![0, 1] :=
    chickenGame_isNash_iff.2 (.inr (.inl ⟨rfl, rfl⟩))
  have hN₃ : chickenGame.IsNash ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] :=
    chickenGame_isNash_iff.2 (.inr (.inr ⟨rfl, rfl⟩))
  exact ⟨chickenGame_isNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope hN₁,
    chickenGame_isNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope hN₂,
    chickenGame_isNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope hN₃,
    chickenGame_isNondegenerate.exists_unique_maximizer_correlatedPolytope hN₃⟩

/-- Exercise `isCorrelated_iff_toCostGame` on `chickenOptimalCorrelated`. -/
example : IsMixedStrategy (jointWeight chickenOptimalCorrelated) ∧
    ∀ b (δ : PureStrategy (Fin 2) (Fin 2) b → PureStrategy (Fin 2) (Fin 2) b),
      ∑ s, jointWeight chickenOptimalCorrelated s * chickenGame.toCostGame.cost b s ≤
        ∑ s, jointWeight chickenOptimalCorrelated s *
          chickenGame.toCostGame.cost b (update s b (δ (s b))) :=
  (chickenGame.isCorrelated_iff_toCostGame chickenOptimalCorrelated).1
    (mem_correlatedPolytope_iff.1 chickenOptimalCorrelated_mem_correlatedPolytope)

/-- The exact `(-100, 1, 0)` Traffic Light game of [TardosVazirani2007], Example 1.10, p. 15
(`0` = Cross, `1` = Stop). -/
private def tardosTrafficGame : BimatrixGame (Fin 2) (Fin 2) :=
  ofSymmetric !![-100, 1; 0, 0]

theorem tardosTrafficGame_isNondegenerate : tardosTrafficGame.IsNondegenerate := by
  have hrow : ∀ y : Fin 2 → ℝ, IsMixedStrategy y →
      {i | tardosTrafficGame.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard := by
    intro y hy
    have hys : y 0 + y 1 = 1 := by simpa only [Fin.sum_univ_two] using hy.sum_eq_one
    have hr₀ : (tardosTrafficGame.A *ᵥ y) 0 = 1 - 101 * y 0 := by
      simp only [tardosTrafficGame, ofSymmetric_A, mulVec, dotProduct, Fin.sum_univ_two, of_apply,
        cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      linarith
    have hr₁ : (tardosTrafficGame.A *ᵥ y) 1 = 0 := by
      simp only [tardosTrafficGame, ofSymmetric_A, mulVec, dotProduct, Fin.sum_univ_two, of_apply,
        cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      ring
    by_cases hcrit : y 0 = 1 / 101
    · have hy1 : y 1 = 100 / 101 := by linarith
      have hsupp : Function.support y = Set.univ := by
        ext i; fin_cases i
        · simp only [Fin.zero_eta, Function.mem_support, hcrit, Set.mem_univ, iff_true]; norm_num
        · simp only [Fin.mk_one, Function.mem_support, hy1, Set.mem_univ, iff_true]; norm_num
      rw [hsupp]
      exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    · obtain ⟨j₀, hj₀⟩ := hy.exists_pos
      have hge1 : 1 ≤ (Function.support y).ncard := by
        simpa only [Set.ncard_singleton] using
          Set.ncard_le_ncard (Set.singleton_subset_iff.2 hj₀.ne') (Set.toFinite _)
      rcases lt_or_gt_of_ne hcrit with hlt | hgt
      · have hsub : {i | tardosTrafficGame.IsPureBestResponse₁ y i} ⊆ {0} := by
          intro i hi
          rw [Set.mem_ofPred_eq, isPureBestResponse₁_iff] at hi
          fin_cases i
          · exact Set.mem_singleton 0
          · exfalso
            have h01 : (tardosTrafficGame.A *ᵥ y) 0 ≤ (tardosTrafficGame.A *ᵥ y) 1 := hi 0
            linarith
        exact ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans_eq (Set.ncard_singleton 0)).trans
          hge1
      · have hsub : {i | tardosTrafficGame.IsPureBestResponse₁ y i} ⊆ {1} := by
          intro i hi
          rw [Set.mem_ofPred_eq, isPureBestResponse₁_iff] at hi
          fin_cases i
          · exfalso
            have h10 : (tardosTrafficGame.A *ᵥ y) 1 ≤ (tardosTrafficGame.A *ᵥ y) 0 := hi 1
            linarith
          · exact Set.mem_singleton 1
        exact ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans_eq (Set.ncard_singleton 1)).trans
          hge1
  refine isNondegenerate_iff.2 ⟨fun x hx => ?_, hrow⟩
  have hsymm : tardosTrafficGame.IsSymmetric := isSymmetric_ofSymmetric _
  have hswap : {j | tardosTrafficGame.IsPureBestResponse₂ x j} =
      {j | tardosTrafficGame.IsPureBestResponse₁ x j} := by
    ext j
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← isPureBestResponse₁_swap, hsymm.swap_eq]
  rw [hswap]
  exact hrow x hx

/-- In [TardosVazirani2007], Example 1.10 (p. 15), the symmetric mixed Nash equilibrium crossing
with probability `ε = 1/101` is an extreme point of `tardosTrafficGame.correlatedPolytope`. -/
theorem tardosTrafficGame_mixedNash_extremePoint :
    tardosTrafficGame.IsNash ![1 / 101, 100 / 101] ![1 / 101, 100 / 101] ∧
    Matrix.vecMulVec (![1 / 101, 100 / 101] : Fin 2 → ℝ) ![1 / 101, 100 / 101] ∈
      tardosTrafficGame.correlatedPolytope.extremePoints ℝ := by
  have hsymm : tardosTrafficGame.IsSymmetric := isSymmetric_ofSymmetric _
  have hbr : tardosTrafficGame.IsBestResponse₁ ![1 / 101, 100 / 101] ![1 / 101, 100 / 101] := by
    refine isBestResponse₁_iff.2 ⟨isMixedStrategy_fin2 (by norm_num) (by norm_num) (by norm_num),
      fun i _ => isPureBestResponse₁_iff.2 fun i' => ?_⟩
    fin_cases i <;> fin_cases i' <;>
      norm_num [tardosTrafficGame, mulVec, dotProduct, Fin.sum_univ_two]
  have hNash : tardosTrafficGame.IsNash ![1 / 101, 100 / 101] ![1 / 101, 100 / 101] :=
    isNash_iff.2 ⟨hbr, hsymm.isBestResponse₂_iff_isBestResponse₁.2 hbr⟩
  exact ⟨hNash, tardosTrafficGame_isNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope
    hNash⟩

end CslibFrontierTests.GameTheory.ZeroSumCorrelatedPolytope
