/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.Core
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Second Welfare Theorem, Debreu–Scarf core shrinking, and Fisher fairness: checked witnesses

This test module imports only the public surface of `CslibFrontier.GameTheory.Market.Core` (and
transitively `CslibFrontier.GameTheory.Market.Welfare`), exercising the headline theorems on
concrete non-vacuous markets and sharpness counterexamples without `import all`:

1. **Second Welfare Theorem decentralization with lump-sum redistribution:** in a `2 × 2` Edgeworth
   box (`welfareBox`), the asymmetric interior allocation `![![3 / 2, 3 / 2], ![1 / 2, 1 / 2]]` is
   Pareto optimal, fails individual rationality (hence lies outside the core and admits **no**
   competitive equilibrium from initial endowments), and is decentralized as a full competitive
   equilibrium of `welfareBox.reendow` by
   `ExchangeMarket.exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal`.
2. **Arrow's corner counterexample (sharpness of positive income in the Second Welfare Theorem):**
   a `2 × 2` economy (`arrowCorner`, `u_0(b) = √(b_0) + b_1`, `u_1(b) = b_0`) at the corner
   allocation `x_0 = ![0, 1]`, `x_1 = ![1, 0]` is Pareto optimal and forms a price
   quasi-equilibrium at `p = ![1, 0]` (where trader `0` has zero income), yet admits **no**
   competitive equilibrium at any price vector `p`.
3. **Debreu–Scarf core shrinking from `r = 1` to `r = 2` (`cobbDouglasBox`):** in a `2 × 2`
   Cobb–Douglas Edgeworth box (`w_0 = ![2, 0]`, `w_1 = ![0, 2]`, `u_i(b) = b_0 * b_1`), the
   symmetric equilibrium `![![1, 1], ![1, 1]]` belongs to `(cobbDouglasBox.replica r).IsInCore` for
   every `r : ℕ`, whereas the asymmetric allocation `![![3 / 2, 3 / 2], ![1 / 2, 1 / 2]]` belongs
   to the `r = 1` core (`cobbDouglasBox.IsInCore`) and is **blocked** in `cobbDouglasBox.replica 2`
   by the `3`-trader coalition `{(0, 0), (1, 0), (1, 1)}`.
4. **Fisher market budget-weighted envy-freeness vs. unweighted envy:** in an unequal-budget linear
   Fisher market (`![3, 7]`), buyer `0` strictly envies buyer `1`'s bundle in unweighted terms while
   satisfying budget-weighted envy-freeness (`budget_mul_utility_le`) and `proportional_share`; an
   equal-budget Fisher market satisfies exact envy-freeness (`envyFree_of_budget_eq`).
-/

public section

namespace CslibFrontierTests.GameTheory.CoreWelfare

open Cslib.GameTheory.Market
open Finset

/-! ### 1. Second Welfare Theorem decentralization vs. failure without transfers -/

/-- `2 × 2` linear Edgeworth box with endowments `w_0 = ![2, 0]`, `w_1 = ![0, 2]` and identical
additive utilities `u_i(b) = b 0 + b 1`. -/
noncomputable def welfareBox : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 0], ![0, 2]]
  utility _ := linearUtility ![1, 1]
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> simp

/-- Asymmetric interior allocation giving `3 / 2` of each good to trader `0` and `1 / 2` to
trader `1`. -/
noncomputable def asymAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![3 / 2, 3 / 2], ![1 / 2, 1 / 2]]

theorem asymAlloc_pos : ∀ (i g : Fin 2), 0 < asymAlloc i g := by
  simp [Fin.forall_fin_two, asymAlloc]

theorem welfareBox_asymAlloc_isParetoOptimal : welfareBox.IsParetoOptimal asymAlloc := by
  refine ⟨⟨fun i g => (asymAlloc_pos i g).le, fun g => ?_⟩, ?_⟩
  · fin_cases g <;>
      simp [welfareBox, asymAlloc, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two] <;>
      norm_num
  · rintro ⟨y, ⟨_, hy_sup⟩, hy_ge, hex⟩
    have h0 := hy_sup 0
    have h1 := hy_sup 1
    simp only [welfareBox, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hu0 := hy_ge 0
    have hu1 := hy_ge 1
    simp only [welfareBox, asymAlloc, linearUtility_eq_sum, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hu0 hu1
    rcases Fin.exists_fin_two.1 hex with hi₀ | hi₁ <;>
      simp only [welfareBox, asymAlloc, linearUtility_eq_sum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at * <;>
      linarith

/-- Without lump-sum redistribution, `asymAlloc` violates individual rationality for trader `1`
(`u_1(x_1) = 1 < 2 = u_1(w_1)`), so it lies outside the core and cannot be a competitive
equilibrium from initial endowments. -/
theorem welfareBox_asymAlloc_not_isInCore : ¬ welfareBox.IsInCore asymAlloc := by
  intro hcore
  have hir := hcore.individuallyRational 1
  simp only [welfareBox, asymAlloc, linearUtility_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hir
  norm_num at hir

theorem welfareBox_asymAlloc_no_equilibrium_without_transfers :
    ∀ p : Fin 2 → ℝ, ¬ welfareBox.IsCompetitiveEquilibrium asymAlloc p := by
  intro p heq
  have hlns : ∀ i : Fin 2, IsLocallyNonsatiated (welfareBox.utility i) := fun _ =>
    (isLocallyNonsatiated_linearUtility_iff ![1, 1]).2 ⟨0, by simp⟩
  exact welfareBox_asymAlloc_not_isInCore (heq.isInCore hlns)

/-- **Second Welfare Theorem witness:** after re-endowing `welfareBox` with `asymAlloc`, there
exists a nonzero nonnegative price vector supporting `asymAlloc` as a full competitive
equilibrium. -/
theorem welfareBox_asymAlloc_second_welfare :
    ∃ p : Fin 2 → ℝ, (∃ g, 0 < p g) ∧
      (welfareBox.reendow asymAlloc
        welfareBox_asymAlloc_isParetoOptimal.nonneg).IsCompetitiveEquilibrium asymAlloc p ∧
      ∀ g, p g * welfareBox.excessDemand asymAlloc g = 0 := by
  have hlns : ∀ i : Fin 2, IsLocallyNonsatiated (welfareBox.utility i) := fun _ =>
    (isLocallyNonsatiated_linearUtility_iff ![1, 1]).2 ⟨0, by simp⟩
  have hconv : ∀ i : Fin 2, HasConvexPreferences (welfareBox.utility i) := fun _ =>
    hasConvexPreferences_linearUtility ![1, 1]
  have hcont : ∀ i : Fin 2, ContinuousOn (welfareBox.utility i) {b : Fin 2 → ℝ | ∀ g, 0 ≤ b g} := by
    intro _
    have hfun : linearUtility (![1, 1] : Fin 2 → ℝ) = fun b : Fin 2 → ℝ => b 0 + b 1 := by
      funext b
      simp [linearUtility_eq_sum, Fin.sum_univ_two]
    dsimp only [welfareBox]
    rw [hfun]
    exact ((continuous_apply 0).add (continuous_apply 1)).continuousOn
  exact welfareBox.exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal
    hlns hconv hcont welfareBox_asymAlloc_isParetoOptimal asymAlloc_pos

/-! ### 2. Arrow's corner counterexample: quasi-equilibrium with no competitive equilibrium -/

/-- Arrow's corner economy: trader `0` holds `![0, 1]` with `u_0(b) = √(b 0) + b 1` (infinite
marginal rate of substitution at `b 0 = 0`), while trader `1` holds `![1, 0]` and desires only
good `0` (`u_1(b) = b 0`). -/
noncomputable def arrowAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1, 0]]

noncomputable def arrowCorner : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := arrowAlloc
  utility := ![fun b => Real.sqrt (b 0) + b 1, fun b => b 0]
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> simp [arrowAlloc]

theorem arrowCorner_isParetoOptimal : arrowCorner.IsParetoOptimal arrowAlloc := by
  refine ⟨⟨arrowCorner.endowment_nonneg, fun g => ?_⟩, ?_⟩
  · simp [arrowCorner, ExchangeMarket.totalSupply_eq_sum]
  · rintro ⟨y, ⟨hy_nn, hy_sup⟩, hy_ge, hex⟩
    have hsup0 : y 0 0 + y 1 0 ≤ 1 := by
      simpa [arrowCorner, arrowAlloc, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two]
        using hy_sup 0
    have hsup1 : y 0 1 + y 1 1 ≤ 1 := by
      simpa [arrowCorner, arrowAlloc, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two]
        using hy_sup 1
    have hu1 : 1 ≤ y 1 0 := by simpa [arrowCorner, arrowAlloc] using hy_ge 1
    have hy00_nn : 0 ≤ y 0 0 := hy_nn 0 0
    have hy00 : y 0 0 = 0 := by linarith
    have hy10 : y 1 0 = 1 := by linarith
    have hy01 : y 0 1 ≤ 1 := by linarith [hy_nn 1 1]
    rcases Fin.exists_fin_two.1 hex with hi₀ | hi₁
    · simp only [arrowCorner, arrowAlloc, Matrix.cons_val_zero, Matrix.cons_val_one, hy00,
        Real.sqrt_zero, zero_add] at hi₀
      linarith
    · simp only [arrowCorner, arrowAlloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hi₁
      linarith

/-- At `p = ![1, 0]`, `(arrowAlloc, ![1, 0])` **is** a price quasi-equilibrium of `arrowCorner`
(trader `0` has zero income `E.income ![1, 0] 0 = 0`). -/
theorem arrowCorner_isPriceQuasiEquilibrium :
    arrowCorner.IsPriceQuasiEquilibrium arrowAlloc ![1, 0] := by
  refine ⟨?_, ⟨0, by simp⟩, ?_, ?_, ?_⟩
  · simp [Fin.forall_fin_two]
  · rw [Fin.forall_fin_two]
    constructor
    · refine ⟨⟨arrowCorner.endowment_nonneg 0, by rw [ExchangeMarket.income_eq]; rfl⟩,
        fun b hb_nn _ => ?_⟩
      simp [arrowCorner, arrowAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
        Fin.sum_univ_two, hb_nn 0]
    · refine ⟨⟨arrowCorner.endowment_nonneg 1, by rw [ExchangeMarket.income_eq]; rfl⟩,
        fun b _ hub => ?_⟩
      simp only [arrowCorner, arrowAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
        add_zero] at hub ⊢
      exact hub.le
  · intro g
    simp [arrowCorner, ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum]
  · intro g
    simp [arrowCorner, ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum]

/-- Despite Pareto optimality and quasi-equilibrium decentralizability, `arrowAlloc` admits **no**
competitive equilibrium in `arrowCorner` at **any** price vector `p`: positive income / Slater's
cheaper-point condition in `exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal` cannot be
dropped. -/
theorem arrowCorner_no_isCompetitiveEquilibrium (p : Fin 2 → ℝ) :
    ¬ arrowCorner.IsCompetitiveEquilibrium arrowAlloc p := by
  rintro ⟨hp_nn, hdem, -, -⟩
  have hdem0 := (mem_demandSet).1 ((arrowCorner.mem_demandSet).1 (hdem 0))
  have hdem1 := (mem_demandSet).1 ((arrowCorner.mem_demandSet).1 (hdem 1))
  have hp0_pos : 0 < p 0 := by
    rcases eq_or_lt_of_le (hp_nn 0) with hp0_zero | hp0_pos
    · exfalso
      have hfeas : IsBudgetFeasible p (arrowCorner.income p 1) ![2, 0] := by
        refine ⟨by simp [Fin.forall_fin_two], ?_⟩
        simp [arrowCorner, arrowAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two, ← hp0_zero]
      have hle := hdem1.2 ![2, 0] hfeas
      simp only [arrowCorner, arrowAlloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hle
      norm_num at hle
    · exact hp0_pos
  have hp1_pos : 0 < p 1 := by
    rcases eq_or_lt_of_le (hp_nn 1) with hp1_zero | hp1_pos
    · exfalso
      have hfeas : IsBudgetFeasible p (arrowCorner.income p 0) ![0, 2] := by
        refine ⟨by simp [Fin.forall_fin_two], ?_⟩
        simp [arrowCorner, arrowAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two, ← hp1_zero]
      have hle := hdem0.2 ![0, 2] hfeas
      simp only [arrowCorner, arrowAlloc, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.sqrt_zero, zero_add] at hle
      norm_num at hle
    · exact hp1_pos
  -- Both prices are positive: trader `0` can trade `(p 0 / p 1) * s^2` of good `1` for `s^2` of
  -- good `0`, gaining `s - (p 0 / p 1) * s^2 > 0` in utility!
  let s : ℝ := min 1 (p 1 / (2 * p 0))
  have hs_pos : 0 < s := lt_min zero_lt_one (div_pos hp1_pos (by positivity))
  have hs_le_one : s ≤ 1 := min_le_left _ _
  have hs_le_ratio : s ≤ p 1 / (2 * p 0) := min_le_right _ _
  have hp0s_le : p 0 * s ≤ p 1 / 2 := by
    have := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp0_pos)).1 hs_le_ratio
    linarith
  have hcost_ratio_le : (p 0 / p 1) * s ^ 2 ≤ s / 2 := by
    have hdiv : (p 0 / p 1) * s ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hp1_pos (by norm_num)]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hdiv hs_pos.le
    linarith [show (p 0 / p 1) * s * s = (p 0 / p 1) * s ^ 2 by ring,
      show 1 / 2 * s = s / 2 by ring]
  let b : Fin 2 → ℝ := ![s ^ 2, 1 - (p 0 / p 1) * s ^ 2]
  have hb_feas : IsBudgetFeasible p (arrowCorner.income p 0) b := by
    refine ⟨?_, ?_⟩
    · rw [Fin.forall_fin_two]
      refine ⟨sq_nonneg s, ?_⟩
      simp only [b, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
    · simp only [arrowCorner, arrowAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
        Fin.sum_univ_two, b, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add]
      field_simp [hp1_pos.ne']
      ring_nf
      exact le_rfl
  have hle := hdem0.2 b hb_feas
  simp only [arrowCorner, arrowAlloc, b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sqrt_zero, Real.sqrt_sq hs_pos.le, zero_add] at hle
  linarith

/-! ### 3. Debreu–Scarf core shrinking from `r = 1` to `r = 2` -/

/-- `2 × 2` Cobb–Douglas Edgeworth box (`w_0 = ![2, 0]`, `w_1 = ![0, 2]`, `u_i(b) = b 0 * b 1`). -/
noncomputable def cobbDouglasBox : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 0], ![0, 2]]
  utility _ b := b 0 * b 1
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> simp

theorem cobbDouglasBox_locallyNonsatiated (i : Fin 2) :
    IsLocallyNonsatiated (cobbDouglasBox.utility i) := by
  intro b hb_nn ε hε
  refine ⟨fun g => b g + ε / 2, fun g => by linarith [hb_nn g], fun g => ?_, ?_⟩
  · have : b g + ε / 2 - b g = ε / 2 := by ring
    rw [this, abs_of_pos (half_pos hε)]
    linarith
  · dsimp only [cobbDouglasBox]
    have hb0 := hb_nn 0
    have hb1 := hb_nn 1
    nlinarith [mul_pos (half_pos hε) (half_pos hε)]

/-- Symmetric allocation `![![1, 1], ![1, 1]]` at equal prices `![1, 1]`. -/
def symAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![1, 1], ![1, 1]]

theorem cobbDouglasBox_symAlloc_equilibrium :
    cobbDouglasBox.IsCompetitiveEquilibrium symAlloc ![1, 1] := by
  refine ⟨by simp [Fin.forall_fin_two], ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    constructor
    · rw [cobbDouglasBox.mem_demandSet, mem_demandSet]
      refine ⟨⟨by simp [Fin.forall_fin_two, symAlloc], ?_⟩, fun b hb => ?_⟩
      · simp [cobbDouglasBox, symAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two]
        norm_num
      · have hexp := hb.2
        simp only [cobbDouglasBox, symAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hexp ⊢
        nlinarith [sq_nonneg (b 0 - b 1), hb.1 0, hb.1 1]
    · rw [cobbDouglasBox.mem_demandSet, mem_demandSet]
      refine ⟨⟨by simp [Fin.forall_fin_two, symAlloc], ?_⟩, fun b hb => ?_⟩
      · simp [cobbDouglasBox, symAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two]
        norm_num
      · have hexp := hb.2
        simp only [cobbDouglasBox, symAlloc, ExchangeMarket.income_eq, expenditure_eq_sum,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hexp ⊢
        nlinarith [sq_nonneg (b 0 - b 1), hb.1 0, hb.1 1]
  · intro g
    fin_cases g <;>
      simp [cobbDouglasBox, symAlloc, ExchangeMarket.excessDemand_eq,
        ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two] <;>
      norm_num
  · intro g
    fin_cases g <;>
      simp [cobbDouglasBox, symAlloc, ExchangeMarket.excessDemand_eq,
        ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two] <;>
      norm_num

/-- The symmetric competitive equilibrium remains in the core of **every** replica economy
`cobbDouglasBox.replica r`. -/
theorem cobbDouglasBox_symAlloc_replica_isInCore (r : ℕ) :
    (cobbDouglasBox.replica r).IsInCore (fun ic => symAlloc ic.1) :=
  cobbDouglasBox_symAlloc_equilibrium.replica_isInCore cobbDouglasBox_locallyNonsatiated r

/-- In the un-replicated economy (`r = 1`), the asymmetric allocation `asymAlloc`
(`![![3 / 2, 3 / 2], ![1 / 2, 1 / 2]]`) **does** belong to the core! -/
theorem cobbDouglasBox_asymAlloc_isInCore : cobbDouglasBox.IsInCore asymAlloc := by
  refine ⟨⟨fun i g => (asymAlloc_pos i g).le, fun g => ?_⟩, fun S z hblock => ?_⟩
  · fin_cases g <;>
      simp [cobbDouglasBox, asymAlloc, ExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two] <;>
      norm_num
  · obtain ⟨hS_ne, hz_nn, hz_endow, hz_le, ⟨i₀, hi₀S, hi₀_lt⟩⟩ := hblock
    by_cases h0 : (0 : Fin 2) ∈ S
    · by_cases h1 : (1 : Fin 2) ∈ S
      · -- `S = univ`: AM-GM forces `(z 0 0 + z 0 1) + (z 1 0 + z 1 1) > 3 + 1 = 4`.
        have hS_univ : S = univ := by
          ext j
          fin_cases j <;> simp [h0, h1]
        subst hS_univ
        have he0 : z 0 0 + z 1 0 ≤ 2 := by
          simpa [cobbDouglasBox, Fin.sum_univ_two] using hz_endow 0
        have he1 : z 0 1 + z 1 1 ≤ 2 := by
          simpa [cobbDouglasBox, Fin.sum_univ_two] using hz_endow 1
        have hu0 : (3 / 2 : ℝ) * (3 / 2) ≤ z 0 0 * z 0 1 := by
          simpa [cobbDouglasBox, asymAlloc] using hz_le 0 (mem_univ 0)
        have hu1 : (1 / 2 : ℝ) * (1 / 2) ≤ z 1 0 * z 1 1 := by
          simpa [cobbDouglasBox, asymAlloc] using hz_le 1 (mem_univ 1)
        have hz0_sum : 3 ≤ z 0 0 + z 0 1 := by
          nlinarith [sq_nonneg (z 0 0 - z 0 1), hz_nn 0 (mem_univ 0) 0, hz_nn 0 (mem_univ 0) 1]
        have hz1_sum : 1 ≤ z 1 0 + z 1 1 := by
          nlinarith [sq_nonneg (z 1 0 - z 1 1), hz_nn 1 (mem_univ 1) 0, hz_nn 1 (mem_univ 1) 1]
        fin_cases i₀
        · have hlt : (3 / 2 : ℝ) * (3 / 2) < z 0 0 * z 0 1 := by
            simpa [cobbDouglasBox, asymAlloc] using hi₀_lt
          nlinarith [sq_nonneg (z 0 0 - z 0 1), hz_nn 0 (mem_univ 0) 0, hz_nn 0 (mem_univ 0) 1]
        · have hlt : (1 / 2 : ℝ) * (1 / 2) < z 1 0 * z 1 1 := by
            simpa [cobbDouglasBox, asymAlloc] using hi₀_lt
          nlinarith [sq_nonneg (z 1 0 - z 1 1), hz_nn 1 (mem_univ 1) 0, hz_nn 1 (mem_univ 1) 1]
      · -- `S = {0}`: coalition has zero endowment of good `1`, so `u_0(z 0) = 0 < 9 / 4`.
        have hS_eq : S = {0} := by
          ext j
          fin_cases j <;> simp [h0, h1]
        subst hS_eq
        have he1 : z 0 1 ≤ 0 := by simpa [cobbDouglasBox] using hz_endow 1
        have hz01 : z 0 1 = 0 := le_antisymm he1 (hz_nn 0 (mem_singleton_self 0) 1)
        have hu0 : (3 / 2 : ℝ) * (3 / 2) ≤ z 0 0 * z 0 1 := by
          simpa [cobbDouglasBox, asymAlloc] using hz_le 0 (mem_singleton_self 0)
        rw [hz01, mul_zero] at hu0
        norm_num at hu0
    · -- `0 ∉ S`, so `S = {1}`: coalition has zero endowment of good `0`, so `u_1(z 1) = 0 < 1 / 4`.
      have h1 : (1 : Fin 2) ∈ S := by
        obtain ⟨j, hj⟩ := hS_ne
        fin_cases j
        · exact (h0 hj).elim
        · exact hj
      have hS_eq : S = {1} := by
        ext j
        fin_cases j <;> simp [h0, h1]
      subst hS_eq
      have he0 : z 1 0 ≤ 0 := by simpa [cobbDouglasBox] using hz_endow 0
      have hz10 : z 1 0 = 0 := le_antisymm he0 (hz_nn 1 (mem_singleton_self 1) 0)
      have hu1 : (1 / 2 : ℝ) * (1 / 2) ≤ z 1 0 * z 1 1 := by
        simpa [cobbDouglasBox, asymAlloc] using hz_le 1 (mem_singleton_self 1)
      rw [hz10, zero_mul] at hu1
      norm_num at hu1

/-- **Debreu–Scarf core shrinking at `r = 2`:** in the `2`-fold replica economy, `asymAlloc` is
**ejected from the core** by the `3`-trader coalition `{(0, 0), (1, 0), (1, 1)}` trading to
`(0, 0) ↦ ![1, 5 / 2]` (`5 / 2 > 9 / 4`) and `(1, c) ↦ ![1 / 2, 3 / 4]` (`3 / 8 > 1 / 4`). -/
theorem cobbDouglasBox_asymAlloc_not_replica_two_isInCore :
    ¬ (cobbDouglasBox.replica 2).IsInCore (fun ic => asymAlloc ic.1) := by
  intro hcore
  let C : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 0), (1, 1)}
  let z : Fin 2 × Fin 2 → Fin 2 → ℝ := fun ic =>
    if ic.1 = 0 then ![1, 5 / 2] else ![1 / 2, 3 / 4]
  refine hcore.2 C z ⟨⟨(0, 0), by simp [C]⟩, ?_, ?_, ?_, ?_⟩
  · intro ic _ g
    dsimp only [z]
    split_ifs <;> fin_cases g <;> simp <;> norm_num
  · intro g
    have hC_sum : ∀ f : Fin 2 × Fin 2 → ℝ,
        ∑ ic ∈ C, f ic = f (0, 0) + f (1, 0) + f (1, 1) := by
      intro f
      dsimp only [C]
      rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, add_assoc]
    rw [hC_sum, hC_sum]
    fin_cases g <;> simp [z, cobbDouglasBox] <;> norm_num
  · intro ic hic
    have hcases : ic = (0, 0) ∨ ic = (1, 0) ∨ ic = (1, 1) := by simpa [C] using hic
    rcases hcases with rfl | rfl | rfl <;>
      simp [z, cobbDouglasBox, asymAlloc] <;> norm_num
  · refine ⟨(0, 0), by simp [C], ?_⟩
    simp [z, cobbDouglasBox, asymAlloc]
    norm_num

/-! ### 4. Fisher market budget-weighted envy-freeness vs. unweighted envy -/

/-- Asymmetric `2 × 2` linear Fisher market (`budgets = ![3, 7]`, utilities `![![4, 1], ![2, 2]]`)
and its unique equilibrium `(![![3 / 5, 0], ![2 / 5, 1]], ![5, 5])`. -/
noncomputable def unequalFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![3, 7] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

noncomputable def unequalAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![3 / 5, 0], ![2 / 5, 1]]

def unequalPrices : Fin 2 → ℝ :=
  ![5, 5]

theorem unequalFisher_isEquilibrium :
    unequalFisher.IsEquilibrium unequalAlloc unequalPrices := by
  have hbns : ∀ i : Fin 2, ∃ g : Fin 2, 0 < unequalFisher.utility i g := by
    simp [unequalFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  have hgd : ∀ g : Fin 2, ∃ i : Fin 2, 0 < unequalFisher.utility i g := by
    simp [unequalFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  rw [LinearFisherMarket.isEquilibrium_iff_bangPerBuck hbns hgd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [unequalPrices, Fin.forall_fin_two]
  · simp [unequalAlloc, Fin.forall_fin_two]; norm_num
  · simp [unequalFisher, unequalAlloc, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [unequalFisher, expenditure_eq_sum, unequalAlloc, unequalPrices,
      Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [unequalFisher, LinearFisherMarket.bangPerBuck_eq, unequalAlloc, unequalPrices,
      Fin.forall_fin_two]; norm_num

/-- **Budget-weighted envy-freeness and proportional share** hold at `unequalFisher`'s
equilibrium. -/
theorem unequalFisher_budget_weighted_envyFree (i j : Fin 2) :
    unequalFisher.budget i * linearUtility (unequalFisher.utility i) (unequalAlloc j) ≤
      unequalFisher.budget j * unequalFisher.buyerUtility unequalAlloc i :=
  unequalFisher_isEquilibrium.budget_mul_utility_le i j

theorem unequalFisher_proportional_share (i : Fin 2) :
    (unequalFisher.budget i / ∑ j : Fin 2, unequalFisher.budget j) *
        linearUtility (unequalFisher.utility i) unequalFisher.supply ≤
      unequalFisher.buyerUtility unequalAlloc i :=
  unequalFisher_isEquilibrium.proportional_share
    (by simp [unequalFisher, Fin.forall_fin_two, Fin.exists_fin_two])
    (by simp [unequalFisher, Fin.sum_univ_two]; norm_num) i

/-- **Sharpness of equal budgets in `envyFree_of_budget_eq`:** when budgets differ (`3 < 7`),
buyer `0` **strictly envies** buyer `1`'s bundle in unweighted utility (`12 / 5 < 13 / 5`). -/
theorem unequalFisher_raw_envy :
    unequalFisher.buyerUtility unequalAlloc 0 <
      linearUtility (unequalFisher.utility 0) (unequalAlloc 1) := by
  simp only [LinearFisherMarket.buyerUtility_eq, linearUtility_eq_sum, unequalFisher,
    LinearFisherMarket.unitSupply_utility, unequalAlloc, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Equal-budget `2 × 2` linear Fisher market (`budgets = ![1, 1]`, utilities `![![2, 1], ![1, 2]]`)
satisfying exact unweighted envy-freeness via `envyFree_of_budget_eq`. -/
noncomputable def equalFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![1, 1] ![![2, 1], ![1, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem equalFisher_isEquilibrium :
    equalFisher.IsEquilibrium ![![1, 0], ![0, 1]] ![1, 1] := by
  have hbns : ∀ i : Fin 2, ∃ g : Fin 2, 0 < equalFisher.utility i g := by
    simp [equalFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  have hgd : ∀ g : Fin 2, ∃ i : Fin 2, 0 < equalFisher.utility i g := by
    simp [equalFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  rw [LinearFisherMarket.isEquilibrium_iff_bangPerBuck hbns hgd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.forall_fin_two]
  · simp [Fin.forall_fin_two]
  · simp [equalFisher, Fin.forall_fin_two, Fin.sum_univ_two]
  · simp [equalFisher, expenditure_eq_sum, Fin.forall_fin_two, Fin.sum_univ_two]
  · simp [equalFisher, LinearFisherMarket.bangPerBuck_eq, Fin.forall_fin_two]

theorem equalFisher_envyFree (i j : Fin 2) :
    linearUtility (equalFisher.utility i) (![![1, 0], ![0, 1]] j) ≤
      equalFisher.buyerUtility ![![1, 0], ![0, 1]] i :=
  equalFisher_isEquilibrium.envyFree_of_budget_eq
    (by fin_cases i <;> fin_cases j <;> simp [equalFisher])

end CslibFrontierTests.GameTheory.CoreWelfare
