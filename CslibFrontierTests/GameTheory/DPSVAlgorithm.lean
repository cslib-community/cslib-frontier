/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.DPSVAlgorithm
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Main DPSV primal-dual algorithm: checked client instances

This ordinary `module` test client imports only the public surface of
`CslibFrontier.GameTheory.Market.DPSVAlgorithm` (no `import all`), certifying concrete witnesses
for every main result of [Vazirani2007], Sections 5.8 and 5.10:

1. **Initialization & price-reduction branch (Section 5.8, p. 115):**
   * On `unbalancedInitFisher` (`e = ![2, 2]`, `u = ![![4, 1], ![4, 1]]`), uniform prices
     `![1/2, 1/2]` leave good `1` without an equality edge, so `dpsvInitPrice` strictly lowers
     `p 1` to `1/8` while keeping `p 0 = 1/2`, giving every good an incident equality edge and
     satisfying `SatisfiesInvariant`.
2. **Lemmas 5.13, 5.15, and 5.16 (Section 5.10, pp. 119–120):**
   * Concrete instantiation of Lemma 5.16 (`sum_sq_drop_of_transfer`), Lemma 5.15
     (`surplusSqNorm_le_sub_sq_of_isBalancedFlow` on `splitFisher` comparing an unbalanced flow
     with surplus `![1, 5]` to the balanced flow with surplus `![3, 3]`), and Lemma 5.13
     (`price_sub_ge_inv_sq_of_isTightSet` on `splitFisher` comparing tight set `{0}` at `![3, 2]`
     with `{0, 1}` at equilibrium `![5, 5]`).
3. **Phase potential drop & zero-spending boundary witness (Section 5.8, p. 116; Lemmas 5.14 &
   5.21, pp. 119, 121):**
   * On `splitFisher` at `![2, 2]`, `dpsvPhaseProgram` executes `1 ≤ iters ≤ 2` iterations using
     at most `4 * iters` max-flow oracle calls and drops `surplusSqNorm` from `18` to at most
     `27 / 2` (`(1 - 1 / 4) * 18`).
   * On the `1 × 2` boundary market `oneGoodTwoBuyers` (`e = ![10, 2]`, `u = ![![1], ![1]]`),
     at initial price `![1]` buyer `1 ∉ H₀ = {0}` spends zero yet retains an equality edge to
     good `0 ∈ J₀` for all `x > 1` (exercising the zero-spending buyer boundary noted in the
     module docstring); `dpsvPhaseProgram` still preserves the Invariant and drops `surplusSqNorm`
     by at least `1 / 2` (`≤ 85 / 2`), and `dpsvProgram` converges to exact equilibrium `![12]`.
4. **End-to-end Theorem 5.22 (`dpsvProgram_spec`, p. 121):**
   * Full execution of `dpsvProgram` with `canonicalMaxFlowOracle` on `oneGoodTwoBuyers`
     (`p = ![12]`), `splitFisher` (`p = ![5, 5]`), and `separatingFisher` (`e = ![10, 4]`,
     `u = ![![4, 1], ![2, 2]]`, unique equilibrium `p = ![10, 4]`), certifying exact
     `IsEquilibrium`, exact unique equilibrium prices, phase bounds, and max-flow oracle query
     bounds.
-/

public section

namespace CslibFrontierTests.GameTheory.DPSVAlgorithm

open Cslib.GameTheory.Market Cslib.GameTheory.Market.LinearFisherMarket

private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by omega

private theorem fin_one_eq (x : Fin 1) : x = 0 := by omega

/-! ### 1. Initialization and price-reduction witness (Section 5.8, p. 115) -/

/-- `2 × 2` unit-supply integer market where uniform prices `![1/2, 1/2]` leave good `1` without an
equality edge, triggering the price reduction `p 1 = 1 / 8 < 1 / 2` of `dpsvInitPrice`. -/
noncomputable def unbalancedInitFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![2, 2] ![![4, 1], ![4, 1]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem unbalancedInitFisher_isNonDegenerate : unbalancedInitFisher.IsNonDegenerate where
  budget_pos := by simp [unbalancedInitFisher, Fin.forall_fin_two]
  supply_pos := by simp [unbalancedInitFisher]
  buyer_nonsatiated := by simp [unbalancedInitFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by simp [unbalancedInitFisher, Fin.forall_fin_two, Fin.exists_fin_two]

/-- **Section 5.8 initialization witness:** `unbalancedInitFisher.dpsvInitPrice` is positive,
bounded by `1 / 2`, gives every good an equality edge, satisfies `SatisfiesInvariant`, and
explicitly lowers good `1` to `1 / 8` while keeping good `0` at `1 / 2`. -/
theorem unbalancedInitFisher_init_spec :
    unbalancedInitFisher.dpsvInitPrice 0 = 1 / 2 ∧
      unbalancedInitFisher.dpsvInitPrice 1 = 1 / 8 ∧
      (∀ g, 0 < unbalancedInitFisher.dpsvInitPrice g) ∧
      (∀ g, ∃ i, unbalancedInitFisher.IsEqualityEdge unbalancedInitFisher.dpsvInitPrice i g) ∧
      unbalancedInitFisher.SatisfiesInvariant unbalancedInitFisher.dpsvInitPrice := by
  obtain ⟨hp_pos, -, hp_eq_edge, hgood_edge, hinv⟩ :=
    dpsvInitPrice_spec unbalancedInitFisher_isNonDegenerate
      (fun _ => by simp [unbalancedInitFisher])
      (by simp [unbalancedInitFisher, Fin.forall_fin_two])
  have hp0_eq : unbalancedInitFisher.dpsvInitPrice 0 = 1 / 2 := by
    have h0 : unbalancedInitFisher.IsEqualityEdge (fun _ => 1 / (Fintype.card (Fin 2) : ℝ)) 0 0 :=
      by
        intro g'; rcases fin_two_cases g' with rfl | rfl
        · exact le_rfl
        · simp [unbalancedInitFisher, bangPerBuck_eq]
    simpa using hp_eq_edge 0 ⟨0, h0⟩
  have hp1_eq : unbalancedInitFisher.dpsvInitPrice 1 = 1 / 8 := by
    obtain ⟨i₁, hE₁⟩ := hgood_edge 1
    obtain ⟨i₀, hE₀⟩ := hgood_edge 0
    have h1 := hE₁ 0
    have h2 := hE₀ 1
    rw [bangPerBuck_eq, bangPerBuck_eq, hp0_eq] at h1 h2
    set p1 := unbalancedInitFisher.dpsvInitPrice 1
    have hp1_pos : 0 < p1 := hp_pos 1
    simp only [unbalancedInitFisher, unitSupply_utility] at h1 h2
    rcases fin_two_cases i₁ with rfl | rfl <;> rcases fin_two_cases i₀ with rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1 h2 <;>
      rw [div_le_div_iff₀ (by norm_num) hp1_pos] at h1 <;>
      rw [div_le_div_iff₀ hp1_pos (by norm_num)] at h2 <;>
      linarith
  exact ⟨hp0_eq, hp1_eq, hp_pos, hgood_edge, hinv⟩

/-! ### 2. Base `2 × 2` markets and Lemmas 5.13, 5.15, 5.16 -/

/-- Asymmetric `2 × 2` integer market (`e = ![3, 7]`, `u = ![![4, 1], ![2, 2]]`) with unique
equilibrium prices `![5, 5]`. -/
noncomputable def splitFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![3, 7] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem splitFisher_isNonDegenerate : splitFisher.IsNonDegenerate where
  budget_pos := by simp [splitFisher, Fin.forall_fin_two]
  supply_pos := by simp [splitFisher]
  buyer_nonsatiated := by simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]

private theorem splitFisher_eq :
    splitFisher.IsEquilibrium ![![(3 : ℝ) / 5, 0], ![2 / 5, 1]] ![5, 5] := by
  rw [isEquilibrium_iff_bangPerBuck
    splitFisher_isNonDegenerate.buyer_nonsatiated splitFisher_isNonDegenerate.good_desired]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.forall_fin_two]
  · simp [Fin.forall_fin_two]; norm_num
  · simp [splitFisher, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [splitFisher, expenditure_eq_sum, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [splitFisher, bangPerBuck_eq, Fin.forall_fin_two]; norm_num

/-- **Lemma 5.16 witness:** concrete instantiation of `sum_sq_drop_of_transfer` with `a = 5`,
`b = ![3, 2]`, `δ = 4`, `δ_vec = ![2, 1]`. -/
theorem lemma5_16_witness :
    (5 : ℝ) ^ 2 + ∑ j : Fin 2, (![(3 : ℝ), 2] j) ^ 2 ≤
      (5 + 4) ^ 2 + ∑ j : Fin 2, (![(3 : ℝ), 2] j - ![(2 : ℝ), 1] j) ^ 2 - 4 ^ 2 :=
  sum_sq_drop_of_transfer (by norm_num)
    (by intro j _; rcases fin_two_cases j with rfl | rfl <;> norm_num)
    (by intro j _; rcases fin_two_cases j with rfl | rfl <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)

/-- **Lemma 5.13 witness** on `splitFisher` (`U = 4`, `Δ = 2 * 4^2 = 32`): good `0` belongs to
tight set `{0}` at `p₁ = ![3, 2]` and tight set `{0, 1}` at equilibrium `p₂ = ![5, 5]`, with
`1 / 32 ^ 2 ≤ 5 - 3`. -/
theorem splitFisher_lemma5_13_witness :
    1 / ((2 * 4 ^ 2 : ℕ) : ℝ) ^ 2 ≤ (![(5 : ℝ), 5] 0) - (![(3 : ℝ), 2] 0) := by
  have hp₁ : ∀ g : Fin 2, (0 : ℝ) < ![3, 2] g := by simp [Fin.forall_fin_two]
  have hp₂ : ∀ g : Fin 2, (0 : ℝ) < ![5, 5] g := by simp [Fin.forall_fin_two]
  have h00_1 : splitFisher.IsEqualityEdge ![3, 2] 0 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitFisher, bangPerBuck_eq]; norm_num
  have h10_1 : ¬ splitFisher.IsEqualityEdge ![3, 2] 1 0 := by
    intro h; have := h 1; simp [splitFisher, bangPerBuck_eq] at this; norm_num at this
  have h01_1 : ¬ splitFisher.IsEqualityEdge ![3, 2] 0 1 := by
    intro h; have := h 0; simp [splitFisher, bangPerBuck_eq] at this; norm_num at this
  have h11_1 : splitFisher.IsEqualityEdge ![3, 2] 1 1 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · simp [splitFisher, bangPerBuck_eq]; norm_num
    · exact le_rfl
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hnbr0_1 : splitFisher.buyerNeighborhood ![3, 2] {0} = {0} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00_1, h10_1]
  have hinv₁ : splitFisher.SatisfiesInvariant ![3, 2] := by
    rw [satisfiesInvariant_iff fun g => (hp₁ g).le]
    intro S
    by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · have hS : S = {0, 1} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      have hnbr : splitFisher.buyerNeighborhood ![3, 2] {0, 1} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00_1, h11_1]
      rw [hS, hnbr]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]; norm_num
    · have hS : S = {0} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      rw [hS, hnbr0_1]; simp [goodValue, budgetSum, splitFisher]
    · have hS : S = {1} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      have hnbr : splitFisher.buyerNeighborhood ![3, 2] {1} = {1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01_1, h11_1]
      rw [hS, hnbr]; simp [goodValue, budgetSum, splitFisher]; norm_num
    · have hS : S = ∅ := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      rw [hS]; simp only [goodValue, budgetSum, Finset.sum_empty]
      exact Finset.sum_nonneg fun i _ => splitFisher.budget_nonneg i
  have hS₁ : splitFisher.IsTightSet ![3, 2] {0} := by
    rw [IsTightSet, hnbr0_1]; simp [goodValue, budgetSum, splitFisher]
  have h00_2 : splitFisher.IsEqualityEdge ![5, 5] 0 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitFisher, bangPerBuck_eq]; norm_num
  have h10_2 : splitFisher.IsEqualityEdge ![5, 5] 1 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl <;> simp [splitFisher, bangPerBuck_eq]
  have h01_2 : ¬ splitFisher.IsEqualityEdge ![5, 5] 0 1 := by
    intro h; have := h 0; simp [splitFisher, bangPerBuck_eq] at this; norm_num at this
  have h11_2 : splitFisher.IsEqualityEdge ![5, 5] 1 1 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl <;> simp [splitFisher, bangPerBuck_eq]
  have hnbr01_2 : splitFisher.buyerNeighborhood ![5, 5] {0, 1} = {0, 1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00_2, h10_2]
  have hinv₂ : splitFisher.SatisfiesInvariant ![5, 5] := by
    rw [satisfiesInvariant_iff fun g => (hp₂ g).le]
    intro S
    by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
    · have hS : S = {0, 1} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      rw [hS, hnbr01_2]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]; norm_num
    · have hS : S = {0} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      have hnbr : splitFisher.buyerNeighborhood ![5, 5] {0} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00_2, h10_2]
      rw [hS, hnbr]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]; norm_num
    · have hS : S = {1} := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      have hnbr : splitFisher.buyerNeighborhood ![5, 5] {1} = {1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01_2, h11_2]
      rw [hS, hnbr]; simp [goodValue, budgetSum, splitFisher]; norm_num
    · have hS : S = ∅ := by ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      rw [hS]; simp only [goodValue, budgetSum, Finset.sum_empty]
      exact Finset.sum_nonneg fun i _ => splitFisher.budget_nonneg i
  have hS₂ : splitFisher.IsTightSet ![5, 5] {0, 1} := by
    rw [IsTightSet, hnbr01_2]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]
    norm_num
  simpa using price_sub_ge_inv_sq_of_isTightSet (M := splitFisher) (fun _ => by simp [splitFisher])
    (u := ![![4, 1], ![2, 2]])
    (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        simp [splitFisher])
    (U := 4)
    (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> decide)
    (e := ![3, 7])
    (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [splitFisher])
    splitFisher_isNonDegenerate.buyer_nonsatiated hp₁ hp₂ hinv₁ hinv₂ hS₁ hS₂
    (g := 0) (by simp) (by simp) (by norm_num)

/-- **Lemma 5.15 & Phase Potential Drop (Lemmas 5.14 & 5.21) witness** on `splitFisher` at
`p = ![2, 2]`: comparing unbalanced flow `![![2, 0], ![0, 2]]` (surplus `![1, 5]`, squared norm
`26`) against balanced flow `![![0, 2], ![0, 2]]` (surplus `![3, 3]`, squared norm `18`), and
running one full DPSV phase (`1 ≤ iters ≤ 2`, squared norm drops from `18` to `≤ 27 / 2`). -/
theorem splitFisher_lemma5_15_and_phase_witness :
    splitFisher.surplusSqNorm ![![(0 : ℝ), 2], ![0, 2]] ≤
        splitFisher.surplusSqNorm ![![(2 : ℝ), 0], ![0, 2]] - (5 - 3) ^ 2 ∧
      (let prog := splitFisher.dpsvPhaseProgram ![2, 2] ![![0, 2], ![0, 2]]
       let res := prog.eval canonicalMaxFlowOracle
       (∀ g, 0 < res.price g) ∧
         splitFisher.SatisfiesInvariant res.price ∧
         1 ≤ res.iters ∧ res.iters ≤ 2 ∧
         prog.countQueries canonicalMaxFlowOracle ≤ 4 * res.iters ∧
         splitFisher.surplusSqNorm res.flow ≤ 27 / 2 ∧
         res.tightSet.Nonempty ∧
         ∀ g ∈ res.tightSet, (![(2 : ℝ), 2] g) < res.price g) := by
  have h00 : splitFisher.IsEqualityEdge ![2, 2] 0 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitFisher, bangPerBuck_eq]; norm_num
  have h01 : ¬ splitFisher.IsEqualityEdge ![2, 2] 0 1 := by
    intro h; have := h 0; simp [splitFisher, bangPerBuck_eq] at this; norm_num at this
  have h10 : splitFisher.IsEqualityEdge ![2, 2] 1 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl <;> simp [splitFisher, bangPerBuck_eq]
  have h11 : splitFisher.IsEqualityEdge ![2, 2] 1 1 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl <;> simp [splitFisher, bangPerBuck_eq]
  have hnaive : splitFisher.IsEqualityFlow ![2, 2] ![![2, 0], ![0, 2]] := by
    refine ⟨by simp [Fin.forall_fin_two], fun g i hpos => ?_,
      by simp [splitFisher, Fin.forall_fin_two, Fin.sum_univ_two],
      by simp [splitFisher, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num⟩
    rcases fin_two_cases g with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
      simp at hpos
    · exact h00
    · exact h11
  have hbal_feas : splitFisher.IsEqualityFlow ![2, 2] ![![0, 2], ![0, 2]] := by
    refine ⟨by simp [Fin.forall_fin_two], fun g i hpos => ?_,
      by simp [splitFisher, Fin.forall_fin_two, Fin.sum_univ_two],
      by simp [splitFisher, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num⟩
    rcases fin_two_cases g with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
      simp at hpos
    · exact h10
    · exact h11
  have hbal_max : splitFisher.IsMaxEqualityFlow ![2, 2] ![![0, 2], ![0, 2]] := by
    refine ⟨hbal_feas, fun f' hf' => ?_⟩
    have hle : flowValue f' ≤ ∑ g : Fin 2, (![(2 : ℝ), 2] g) * splitFisher.supply g :=
      Finset.sum_le_sum fun g _ => hf'.2.2.1 g
    have hval : flowValue ![![(0 : ℝ), 2], ![0, 2]] = 4 := by
      simp [flowValue, Fin.sum_univ_two]; norm_num
    have hsum : ∑ g : Fin 2, (![(2 : ℝ), 2] g) * splitFisher.supply g = 4 := by
      simp [splitFisher, Fin.sum_univ_two]; norm_num
    linarith
  have hsurp_bal : splitFisher.surplus ![![0, 2], ![0, 2]] = ![3, 3] := by
    funext i; rcases fin_two_cases i with rfl | rfl <;>
      norm_num [surplus, splitFisher, Fin.sum_univ_two]
  have hbal : splitFisher.IsBalancedFlow ![2, 2] ![![0, 2], ![0, 2]] := by
    rw [isBalancedFlow_iff_satisfiesPropertyOne hbal_max]
    intro j i hlt
    rw [hsurp_bal] at hlt
    rcases fin_two_cases j with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
      simp at hlt
  have h515 := surplusSqNorm_le_sub_sq_of_isBalancedFlow hnaive hbal 1
  have hsurp_n1 : splitFisher.surplus ![![2, 0], ![0, 2]] 1 = 5 := by
    simp [surplus, splitFisher, Fin.sum_univ_two]; norm_num
  have hsurp_b1 : splitFisher.surplus ![![0, 2], ![0, 2]] 1 = 3 := by
    rw [hsurp_bal]; rfl
  rw [hsurp_n1, hsurp_b1] at h515
  have hinv : splitFisher.SatisfiesInvariant ![2, 2] := by
    rw [satisfiesInvariant_iff (by simp [Fin.forall_fin_two])]
    intro S
    have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; right; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
    have hne01 : (0 : Fin 2) ≠ 1 := by decide
    rcases hcases with rfl | rfl | rfl | rfl
    · simp only [goodValue, budgetSum, Finset.sum_empty]
      exact Finset.sum_nonneg fun i _ => splitFisher.budget_nonneg i
    · have hnbr : splitFisher.buyerNeighborhood ![2, 2] {0} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]; norm_num
    · have hnbr : splitFisher.buyerNeighborhood ![2, 2] {1} = {1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01, h11]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher]; norm_num
    · have hnbr : splitFisher.buyerNeighborhood ![2, 2] {0, 1} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher, Finset.sum_pair hne01]; norm_num
  obtain ⟨hp', -, hinv', -, hit1, hit2, hq, hdrop, hSne, hSstr, -⟩ :=
    dpsvPhaseProgram_spec splitFisher_isNonDegenerate.supply_pos
      splitFisher_isNonDegenerate.budget_pos splitFisher_isNonDegenerate.buyer_nonsatiated
      (by simp [Fin.forall_fin_two]) hinv hbal ⟨0, by rw [hsurp_bal]; norm_num⟩
      isValidMaxFlowOracle_canonical
  have hsq18 : splitFisher.surplusSqNorm ![![0, 2], ![0, 2]] = 18 := by
    simp [surplusSqNorm, hsurp_bal, Fin.sum_univ_two]; norm_num
  have hdrop' :
      splitFisher.surplusSqNorm
        ((splitFisher.dpsvPhaseProgram ![2, 2] ![![0, 2], ![0, 2]]).eval
          canonicalMaxFlowOracle).flow ≤ 27 / 2 := by
    simp only [Fintype.card_fin, hsq18] at hdrop
    linarith
  exact ⟨h515, hp', hinv', hit1, by simpa using hit2, by simpa using hq, hdrop', hSne, hSstr⟩

/-! ### 3. Zero-spending buyer boundary witness (`Z_t ≠ ∅`) and Theorem 5.22 -/

/-- `1 × 2` boundary market (`1` good, `2` buyers with budgets `![10, 2]` and utilities
`![![1], ![1]]`): at initial price `p = ![1]`, buyer `1 ∉ H₀ = {0}` has zero spending yet retains
an equality edge to good `0 ∈ J₀` for all `x > 1`, exercising the boundary condition documented in
`DPSVAlgorithm.lean`. Unique equilibrium price is `![12]`. -/
noncomputable def oneGoodTwoBuyers : LinearFisherMarket (Fin 2) (Fin 1) :=
  LinearFisherMarket.unitSupply ![10, 2] ![![1], ![1]]
    (by simp [Fin.forall_fin_two])
    (by intro i g; rcases fin_two_cases i with rfl | rfl <;> rw [fin_one_eq g] <;> simp)

theorem oneGoodTwoBuyers_isNonDegenerate : oneGoodTwoBuyers.IsNonDegenerate where
  budget_pos := by simp [oneGoodTwoBuyers, Fin.forall_fin_two]
  supply_pos := by intro g; rw [fin_one_eq g]; simp [oneGoodTwoBuyers]
  buyer_nonsatiated := by
    intro i; refine ⟨0, ?_⟩
    rcases fin_two_cases i with rfl | rfl <;> simp [oneGoodTwoBuyers]
  good_desired := by intro g; rw [fin_one_eq g]; exact ⟨0, by simp [oneGoodTwoBuyers]⟩

/-- **Boundary witness & Theorem 5.22** on `oneGoodTwoBuyers`: even though buyer `1 ∉ H₀` stays
incident to good `0` for all `x > 1`, `dpsvProgram` terminates at exact equilibrium with unique
price `![12]` within the Theorem 5.22 phase and max-flow query bounds. -/
theorem oneGoodTwoBuyers_dpsv_spec :
    let res := oneGoodTwoBuyers.dpsvProgram.eval canonicalMaxFlowOracle
    oneGoodTwoBuyers.IsEquilibrium res.alloc res.price ∧
      res.price = ![12] ∧
      res.phases ≤ dpsvPhaseBound 2 1 1 12 ∧
      oneGoodTwoBuyers.dpsvProgram.countQueries canonicalMaxFlowOracle ≤ 1 + 2 * res.phases := by
  have heq_ref : oneGoodTwoBuyers.IsEquilibrium ![![(10 : ℝ) / 12], ![2 / 12]] ![12] := by
    rw [isEquilibrium_iff_bangPerBuck
      oneGoodTwoBuyers_isNonDegenerate.buyer_nonsatiated
      oneGoodTwoBuyers_isNonDegenerate.good_desired]
    refine ⟨fun g => by rw [fin_one_eq g]; norm_num, ?_, ?_, ?_, ?_⟩
    · intro i g; rw [fin_one_eq g]; rcases fin_two_cases i with rfl | rfl <;> norm_num
    · intro g; rw [fin_one_eq g]; simp [oneGoodTwoBuyers, Fin.sum_univ_two]; norm_num
    · intro i; rcases fin_two_cases i with rfl | rfl <;>
        (simp [oneGoodTwoBuyers, expenditure_eq_sum]; norm_num)
    · intro i g _ g'; rw [fin_one_eq g, fin_one_eq g']
  obtain ⟨hEq, hph, hq⟩ := dpsvProgram_spec (M := oneGoodTwoBuyers)
    oneGoodTwoBuyers_isNonDegenerate (fun _ => by simp [oneGoodTwoBuyers])
    (u := ![![1], ![1]]) (fun i g => by
      rw [fin_one_eq g]; rcases fin_two_cases i with rfl | rfl <;> simp [oneGoodTwoBuyers])
    (U := 1) (fun i g => by
      rw [fin_one_eq g]; rcases fin_two_cases i with rfl | rfl <;> decide)
    (e := ![10, 2]) (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [oneGoodTwoBuyers])
    isValidMaxFlowOracle_canonical
  have hp_eq := price_eq_of_isEquilibrium oneGoodTwoBuyers_isNonDegenerate hEq heq_ref
  exact ⟨hEq, hp_eq, by simpa [Fin.sum_univ_two] using hph, by simpa using hq⟩

/-! ### 4. End-to-end Theorem 5.22 witnesses on `2 × 2` markets -/

/-- **Theorem 5.22 witness on `splitFisher`:** `dpsvProgram` computes an exact equilibrium with
unique prices `![5, 5]` within the Theorem 5.22 phase and max-flow query bounds. -/
theorem splitFisher_dpsv_spec :
    let res := splitFisher.dpsvProgram.eval canonicalMaxFlowOracle
    splitFisher.IsEquilibrium res.alloc res.price ∧
      res.price = ![5, 5] ∧
      res.phases ≤ dpsvPhaseBound 2 2 4 10 ∧
      splitFisher.dpsvProgram.countQueries canonicalMaxFlowOracle ≤ 2 + 8 * res.phases := by
  obtain ⟨hEq, hph, hq⟩ := dpsvProgram_spec (M := splitFisher)
    splitFisher_isNonDegenerate (fun _ => by simp [splitFisher])
    (u := ![![4, 1], ![2, 2]]) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        simp [splitFisher])
    (U := 4) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> decide)
    (e := ![3, 7]) (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [splitFisher])
    isValidMaxFlowOracle_canonical
  have hp_eq := price_eq_of_isEquilibrium splitFisher_isNonDegenerate hEq splitFisher_eq
  exact ⟨hEq, hp_eq, by simpa [Fin.sum_univ_two] using hph, by simpa using hq⟩

/-- Multi-phase separating `2 × 2` market (`e = ![10, 4]`, `u = ![![4, 1], ![2, 2]]`) whose
equilibrium prices `![10, 4]` separate buyers onto disjoint goods (`x = ![![1, 0], ![0, 1]]`). -/
noncomputable def separatingFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![10, 4] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem separatingFisher_isNonDegenerate : separatingFisher.IsNonDegenerate where
  budget_pos := by simp [separatingFisher, Fin.forall_fin_two]
  supply_pos := by simp [separatingFisher]
  buyer_nonsatiated := by simp [separatingFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by simp [separatingFisher, Fin.forall_fin_two, Fin.exists_fin_two]

/-- **Theorem 5.22 witness on `separatingFisher`:** `dpsvProgram` computes an exact equilibrium
with unique separating prices `![10, 4]` within the Theorem 5.22 phase and query bounds. -/
theorem separatingFisher_dpsv_spec :
    let res := separatingFisher.dpsvProgram.eval canonicalMaxFlowOracle
    separatingFisher.IsEquilibrium res.alloc res.price ∧
      res.price = ![10, 4] ∧
      res.phases ≤ dpsvPhaseBound 2 2 4 14 ∧
      separatingFisher.dpsvProgram.countQueries canonicalMaxFlowOracle ≤ 2 + 8 * res.phases := by
  have heq_ref : separatingFisher.IsEquilibrium ![![(1 : ℝ), 0], ![0, 1]] ![10, 4] := by
    rw [isEquilibrium_iff_bangPerBuck
      separatingFisher_isNonDegenerate.buyer_nonsatiated
      separatingFisher_isNonDegenerate.good_desired]
    refine ⟨by simp [Fin.forall_fin_two], by simp [Fin.forall_fin_two],
      by simp [separatingFisher, Fin.forall_fin_two, Fin.sum_univ_two],
      by simp [separatingFisher, expenditure_eq_sum, Fin.forall_fin_two, Fin.sum_univ_two], ?_⟩
    intro i g hpos g'
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
      rcases fin_two_cases g' with rfl | rfl <;>
      simp [separatingFisher, bangPerBuck_eq] at hpos ⊢ <;> norm_num
  obtain ⟨hEq, hph, hq⟩ := dpsvProgram_spec (M := separatingFisher)
    separatingFisher_isNonDegenerate (fun _ => by simp [separatingFisher])
    (u := ![![4, 1], ![2, 2]]) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        simp [separatingFisher])
    (U := 4) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> decide)
    (e := ![10, 4]) (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [separatingFisher])
    isValidMaxFlowOracle_canonical
  have hp_eq := price_eq_of_isEquilibrium separatingFisher_isNonDegenerate hEq heq_ref
  exact ⟨hEq, hp_eq, by simpa [Fin.sum_univ_two] using hph, by simpa using hq⟩

end CslibFrontierTests.GameTheory.DPSVAlgorithm
