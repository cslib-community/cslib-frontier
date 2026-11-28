/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Market.BalancedFlow
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Equality networks, tight sets, balanced flows, and rational equilibria: checked instances

This ordinary `module` test client imports only the public surface of
`CslibFrontier.GameTheory.Market.BalancedFlow` (no `import all`), certifying positive, negative,
and splitting instances across all sections of [Vazirani2007], Chapter 5 formalized in
`BalancedFlow.lean`:

1. **Lemma 5.2 (equality network equilibrium test):** on the asymmetric `2 × 2` market `splitFisher`
   (budgets `![3, 7]`, utilities `![![4, 1], ![2, 2]]`), equilibrium prices `![5, 5]` satisfy both
   min-cut conditions in `N(p)` (`exists_isEquilibrium_iff_minCut`), whereas `![2, 2]` fails.
2. **Lemma 5.3 & maximal tight set:** on `splitFisher`, `![2, 2]` satisfies the Invariant with empty
   maximal tight set, `![3, 2]` satisfies the Invariant with `maximalTightSet = {0}`, and `![6, 6]`
   violates the Invariant.
3. **Lemma 5.4, Theorem 5.5, and Theorem 5.8 (balanced flows & divide-and-conquer):**
   * On `splitFisher` at `![2, 2]`, a naive max-flow `fNaive` with surpluses `![1, 5]` violates
     Property 1 (`¬ IsBalancedFlow`), whereas `fBal` with equal surpluses `![3, 3]` is balanced,
     and `balancedFlowProgram` with `canonicalMaxFlowOracle` matches `surplus = ![3, 3]` in at most
     `2` max-flow oracle calls.
   * On a connected Case-2 splitting market `splitCase2` (budgets `![10, 4]`, same utilities) at
     `![2, 2]`, the balanced flow has strictly unequal surpluses `![8, 2]` and satisfies Property 1.
4. **Lemmas 5.9–5.11 (finding tight sets):** on `splitCase2` at `![2, 2]`, `minTightRatio = 2` and
   `tightSetAtMinRatio = {1} ⊂ Finset.univ` strictly (exercising `x = avgRatio = 7/2 > 2`), and
   `findTightSetProgram` recovers `(2, {1})` in at most `2` max-flow oracle calls.
5. **Lemma 5.12 & Theorem 5.1 part 4 (rationality & polynomial bit-length bounds):** tight-set price
   denominator bound on `{0}` at `![3, 2]`, integer-input rational equilibrium on `splitFisher`
   (matching unique price `![5, 5]`), and general rational-input equilibrium on a fractional
   `2 × 2` market `ratFisher`.
-/

public section

namespace CslibFrontierTests.GameTheory.BalancedFlow

open Cslib.GameTheory.Market Cslib.GameTheory.Market.LinearFisherMarket
open Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut

private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by omega

private theorem rat_num_den_le {a b B : ℕ} (hb : 0 < b) (haB : a ≤ B) (hbB : b ≤ B) :
    ((a : ℚ) / (b : ℚ)).num.natAbs ≤ B ∧ ((a : ℚ) / (b : ℚ)).den ≤ B := by
  let q : ℚ := (a : ℚ) / (b : ℚ)
  have hcross : q.num.natAbs * b = a * q.den := by
    have hq : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) :=
      (div_eq_div_iff (Nat.cast_ne_zero.2 q.den_nz) (Nat.cast_ne_zero.2 hb.ne')).1
        (Rat.num_div_den q)
    have hz : q.num * (b : ℤ) = (a : ℤ) * (q.den : ℤ) := by exact_mod_cast hq
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hz
  have hden : q.den ≤ b := Nat.le_of_dvd hb (q.reduced.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩)
  have hnum : q.num.natAbs ≤ a :=
    Nat.le_of_mul_le_mul_right (hcross.le.trans (Nat.mul_le_mul_left a hden)) hb
  exact ⟨hnum.trans haB, hden.trans hbB⟩

/-! ### 1. Base `2 × 2` market and Lemma 5.2 -/

/-- Asymmetric unit-supply `2 × 2` linear Fisher market: buyer `0` has budget `3` and utilities
`![4, 1]`; buyer `1` has budget `7` and utilities `![2, 2]`. -/
noncomputable def splitFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![3, 7] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem splitFisher_isNonDegenerate : splitFisher.IsNonDegenerate where
  budget_pos := by simp [splitFisher, Fin.forall_fin_two]
  supply_pos := by simp [splitFisher]
  buyer_nonsatiated := by simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]
  good_desired := by simp [splitFisher, Fin.forall_fin_two, Fin.exists_fin_two]

/-- Unique equilibrium prices `![5, 5]` of `splitFisher`. -/
def eqPrices : Fin 2 → ℝ := ![5, 5]

/-- Equilibrium allocation `![![3/5, 0], ![2/5, 1]]` of `splitFisher`. -/
noncomputable def eqAlloc : Fin 2 → Fin 2 → ℝ := ![![3 / 5, 0], ![2 / 5, 1]]

theorem splitFisher_isEquilibrium : splitFisher.IsEquilibrium eqAlloc eqPrices := by
  rw [isEquilibrium_iff_bangPerBuck
    splitFisher_isNonDegenerate.buyer_nonsatiated splitFisher_isNonDegenerate.good_desired]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [eqPrices, Fin.forall_fin_two]
  · simp [eqAlloc, Fin.forall_fin_two]; norm_num
  · simp [splitFisher, eqAlloc, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [splitFisher, expenditure_eq_sum, eqAlloc, eqPrices,
      Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  · simp [splitFisher, bangPerBuck_eq, eqAlloc, eqPrices, Fin.forall_fin_two]; norm_num

/-- **Lemma 5.2 (positive witness):** at `eqPrices = ![5, 5]`, both the source cut and the sink cut
are minimum cuts in `N(eqPrices)`. -/
theorem splitFisher_eqPrices_minCuts :
    cutWeight (splitFisher.equalityNetwork eqPrices)
        ({.source} : Finset (FlowVertex (Fin 2) (Fin 2))) =
        minRealCutBetween (splitFisher.equalityNetwork eqPrices) .source .sink ∧
      cutWeight (splitFisher.equalityNetwork eqPrices)
          (Finset.univ \ ({.sink} : Finset (FlowVertex (Fin 2) (Fin 2)))) =
        minRealCutBetween (splitFisher.equalityNetwork eqPrices) .source .sink :=
  (exists_isEquilibrium_iff_minCut (by simp [eqPrices, Fin.forall_fin_two])
    splitFisher_isNonDegenerate.buyer_nonsatiated splitFisher_isNonDegenerate.good_desired).1
    ⟨eqAlloc, splitFisher_isEquilibrium⟩

/-- **Lemma 5.2 (negative witness):** non-equilibrium prices `![2, 2]` admit no equilibrium. -/
theorem splitFisher_lowPrices_not_equilibrium :
    ¬ ∃ x, splitFisher.IsEquilibrium x ![2, 2] := by
  rintro ⟨x, hx⟩
  have hp := price_eq_of_isEquilibrium splitFisher_isNonDegenerate hx splitFisher_isEquilibrium
  have h0 := congrFun hp 0
  simp [eqPrices] at h0

/-! ### 2. Lemma 5.3, Invariant, and maximal tight set -/

/-- Sub-equilibrium prices `pLow = ![2, 2]` where equality edges are `(0, 0), (1, 0), (1, 1)`. -/
def lowPrices : Fin 2 → ℝ := ![2, 2]

theorem splitFisher_lowPrices_equalityEdge :
    splitFisher.IsEqualityEdge lowPrices 0 0 ∧
      ¬ splitFisher.IsEqualityEdge lowPrices 0 1 ∧
      splitFisher.IsEqualityEdge lowPrices 1 0 ∧
      splitFisher.IsEqualityEdge lowPrices 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitFisher, bangPerBuck_eq, lowPrices]; norm_num
  · intro h; have := h 0; simp [splitFisher, bangPerBuck_eq, lowPrices] at this; norm_num at this
  · intro g'; rcases fin_two_cases g' with rfl | rfl <;>
      simp [splitFisher, bangPerBuck_eq, lowPrices]
  · intro g'; rcases fin_two_cases g' with rfl | rfl <;>
      simp [splitFisher, bangPerBuck_eq, lowPrices]

/-- **Lemma 5.3 (positive witness):** `splitFisher` satisfies the Invariant at `![2, 2]` with empty
maximal tight set. -/
theorem splitFisher_lowPrices_invariant_and_no_tight :
    splitFisher.SatisfiesInvariant lowPrices ∧ splitFisher.maximalTightSet lowPrices = ∅ := by
  obtain ⟨h00, h01, h10, h11⟩ := splitFisher_lowPrices_equalityEdge
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hcheck : ∀ S : Finset (Fin 2),
      splitFisher.goodValue lowPrices S ≤
        splitFisher.budgetSum (splitFisher.buyerNeighborhood lowPrices S) ∧
      (S.Nonempty → splitFisher.goodValue lowPrices S <
        splitFisher.budgetSum (splitFisher.buyerNeighborhood lowPrices S)) := by
    intro S
    have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; right; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
    rcases hcases with rfl | rfl | rfl | rfl
    · have hnbr : splitFisher.buyerNeighborhood lowPrices ∅ = ∅ := by
        ext i; simp [mem_buyerNeighborhood]
      rw [hnbr]; simp [goodValue, budgetSum]
    · have hnbr : splitFisher.buyerNeighborhood lowPrices {0} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher, lowPrices, Finset.sum_pair hne01]
      norm_num
    · have hnbr : splitFisher.buyerNeighborhood lowPrices {1} = {1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01, h11]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher, lowPrices]; norm_num
    · have hnbr : splitFisher.buyerNeighborhood lowPrices {0, 1} = {0, 1} := by
        ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
      rw [hnbr]; simp [goodValue, budgetSum, splitFisher, lowPrices, Finset.sum_pair hne01]
      norm_num
  have hinv : splitFisher.SatisfiesInvariant lowPrices :=
    (satisfiesInvariant_iff (by simp [lowPrices, Fin.forall_fin_two])).2 fun S => (hcheck S).1
  refine ⟨hinv, ?_⟩
  by_contra hne
  have hpos : (splitFisher.maximalTightSet lowPrices).Nonempty :=
    Finset.ne_empty_iff_nonempty.1 hne
  have htight := isTightSet_maximalTightSet (by simp [lowPrices, Fin.forall_fin_two]) hinv
  have hlt := (hcheck _).2 hpos
  unfold IsTightSet at htight
  linarith

/-- Prices `pTight = ![3, 2]` where `{0}` is tight (`p 0 = 3 = budget 0`) and `{1}` is slack. -/
def tightPrices : Fin 2 → ℝ := ![3, 2]

theorem splitFisher_tightPrices_invariant_and_maximalTightSet :
    splitFisher.SatisfiesInvariant tightPrices ∧
      splitFisher.IsTightSet tightPrices {0} ∧
      splitFisher.maximalTightSet tightPrices = {0} := by
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have h00 : splitFisher.IsEqualityEdge tightPrices 0 0 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitFisher, bangPerBuck_eq, tightPrices]; norm_num
  have h01 : ¬ splitFisher.IsEqualityEdge tightPrices 0 1 := by
    intro h; have := h 0; simp [splitFisher, bangPerBuck_eq, tightPrices] at this; norm_num at this
  have h10 : ¬ splitFisher.IsEqualityEdge tightPrices 1 0 := by
    intro h; have := h 1; simp [splitFisher, bangPerBuck_eq, tightPrices] at this; norm_num at this
  have h11 : splitFisher.IsEqualityEdge tightPrices 1 1 := by
    intro g'; rcases fin_two_cases g' with rfl | rfl
    · simp [splitFisher, bangPerBuck_eq, tightPrices]; norm_num
    · exact le_rfl
  have hnbr0 : splitFisher.buyerNeighborhood tightPrices {0} = {0} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
  have hnbr1 : splitFisher.buyerNeighborhood tightPrices {1} = {1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01, h11]
  have hnbr01 : splitFisher.buyerNeighborhood tightPrices {0, 1} = {0, 1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h11]
  have htight0 : splitFisher.IsTightSet tightPrices {0} := by
    rw [IsTightSet, hnbr0]; simp [goodValue, budgetSum, splitFisher, tightPrices]
  have hinv : splitFisher.SatisfiesInvariant tightPrices := by
    rw [satisfiesInvariant_iff (by simp [tightPrices, Fin.forall_fin_two])]
    intro S
    have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; right; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
    rcases hcases with rfl | rfl | rfl | rfl
    · have hnbr : splitFisher.buyerNeighborhood tightPrices ∅ = ∅ := by
        ext i; simp [mem_buyerNeighborhood]
      rw [hnbr]; simp [goodValue, budgetSum]
    · exact htight0.le
    · rw [hnbr1]; simp [goodValue, budgetSum, splitFisher, tightPrices]; norm_num
    · rw [hnbr01]; simp [goodValue, budgetSum, splitFisher, tightPrices, Finset.sum_pair hne01]
      norm_num
  refine ⟨hinv, htight0, Finset.Subset.antisymm ?_ (subset_maximalTightSet htight0)⟩
  have hmt := isTightSet_maximalTightSet (by simp [tightPrices, Fin.forall_fin_two]) hinv
  intro g hg
  rcases fin_two_cases g with rfl | rfl
  · exact Finset.mem_singleton_self 0
  · exfalso
    have hcases : splitFisher.maximalTightSet tightPrices = {1} ∨
        splitFisher.maximalTightSet tightPrices = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ splitFisher.maximalTightSet tightPrices
      · right; ext x; rcases fin_two_cases x with rfl | rfl <;> simp [h0, hg]
      · left; ext x; rcases fin_two_cases x with rfl | rfl <;> simp [h0, hg]
    rcases hcases with h | h <;> rw [h] at hmt
    · rw [IsTightSet, hnbr1] at hmt
      simp [goodValue, budgetSum, splitFisher, tightPrices] at hmt
    · rw [IsTightSet, hnbr01] at hmt
      simp [goodValue, budgetSum, splitFisher, tightPrices, Finset.sum_pair hne01] at hmt

/-- **Lemma 5.3 (negative witness):** overpriced `![6, 6]` violates the Invariant. -/
theorem splitFisher_highPrices_not_invariant :
    ¬ splitFisher.SatisfiesInvariant ![6, 6] := by
  rw [satisfiesInvariant_iff (by simp [Fin.forall_fin_two])]
  intro h
  have hall := h Finset.univ
  have hle : splitFisher.budgetSum (splitFisher.buyerNeighborhood ![6, 6] Finset.univ) ≤
      splitFisher.budgetSum Finset.univ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      splitFisher.budget_nonneg i
  have hgv : splitFisher.goodValue ![6, 6] Finset.univ = 12 := by
    simp [goodValue, splitFisher, Fin.sum_univ_two]; norm_num
  have hbud : splitFisher.budgetSum Finset.univ = 10 := by
    simp [budgetSum, splitFisher, Fin.sum_univ_two]; norm_num
  linarith

/-! ### 3. Lemma 5.4, Theorem 5.5, and Theorem 5.8 (balanced flows & divide-and-conquer) -/

/-- Unbalanced max-flow on `splitFisher` at `![2, 2]`: sends `2` from good `0` to buyer `0` and
`2` from good `1` to buyer `1`, giving unequal surpluses `![1, 5]`. -/
def naiveFlow : Fin 2 → Fin 2 → ℝ := ![![2, 0], ![0, 2]]

/-- Balanced max-flow on `splitFisher` at `![2, 2]`: sends both goods' money (`2 + 2 = 4`) to
buyer `1`, equalizing surpluses to `![3, 3]`. -/
def balFlow : Fin 2 → Fin 2 → ℝ := ![![0, 2], ![0, 2]]

/-- **Theorem 5.5 (negative witness):** `naiveFlow` is a maximum equality flow in `N(![2, 2])`
that violates Property 1 (`0 → g0 → 1` from surplus `1` to `5`), hence is NOT balanced. -/
theorem naiveFlow_not_balanced :
    splitFisher.IsMaxEqualityFlow lowPrices naiveFlow ∧
      ¬ splitFisher.IsBalancedFlow lowPrices naiveFlow := by
  obtain ⟨h00, _, h10, h11⟩ := splitFisher_lowPrices_equalityEdge
  have hfeas : splitFisher.IsEqualityFlow lowPrices naiveFlow := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [naiveFlow, Fin.forall_fin_two]
    · intro g i hpos
      rcases fin_two_cases g with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
        simp [naiveFlow] at hpos
      · exact h00
      · exact h11
    · simp [naiveFlow, splitFisher, lowPrices, Fin.forall_fin_two, Fin.sum_univ_two]
    · simp [naiveFlow, splitFisher, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  have hmax : splitFisher.IsMaxEqualityFlow lowPrices naiveFlow := by
    refine ⟨hfeas, fun f' hf' => ?_⟩
    have hle : flowValue f' ≤ ∑ g : Fin 2, lowPrices g * splitFisher.supply g :=
      Finset.sum_le_sum fun g _ => hf'.2.2.1 g
    have hval : flowValue naiveFlow = 4 := by
      simp [flowValue, naiveFlow, Fin.sum_univ_two]; norm_num
    have hsum : ∑ g : Fin 2, lowPrices g * splitFisher.supply g = 4 := by
      simp [lowPrices, splitFisher, Fin.sum_univ_two]; norm_num
    linarith
  refine ⟨hmax, ?_⟩
  rw [isBalancedFlow_iff_satisfiesPropertyOne hmax]
  intro hprop
  have hsurp : splitFisher.surplus naiveFlow 0 < splitFisher.surplus naiveFlow 1 := by
    simp [surplus, splitFisher, naiveFlow, Fin.sum_univ_two]; norm_num
  have hreach : splitFisher.ResidualReachable lowPrices naiveFlow 0 1 :=
    Relation.ReflTransGen.single ⟨0, by simp [naiveFlow], h10⟩
  exact hprop 0 1 hsurp hreach

/-- **Theorem 5.5 + Lemma 5.4 + Theorem 5.8 (positive witness):** `balFlow` is balanced with equal
surpluses `![3, 3]`, and `balancedFlowProgram` computes a balanced max-flow with the exact same
surplus vector `![3, 3]` in at most `2` max-flow oracle calls. -/
theorem balFlow_and_program_spec :
    splitFisher.IsBalancedFlow lowPrices balFlow ∧
      (let prog := balancedFlowProgram splitFisher lowPrices
       let f := prog.eval canonicalMaxFlowOracle
       splitFisher.IsBalancedFlow lowPrices f ∧
         splitFisher.surplus f = ![3, 3] ∧
         prog.countQueries canonicalMaxFlowOracle ≤ 2) := by
  obtain ⟨_, _, h10, h11⟩ := splitFisher_lowPrices_equalityEdge
  have hfeas : splitFisher.IsEqualityFlow lowPrices balFlow := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [balFlow, Fin.forall_fin_two]
    · intro g i hpos
      rcases fin_two_cases g with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
        simp [balFlow] at hpos
      · exact h10
      · exact h11
    · simp [balFlow, splitFisher, lowPrices, Fin.forall_fin_two, Fin.sum_univ_two]
    · simp [balFlow, splitFisher, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  have hmax : splitFisher.IsMaxEqualityFlow lowPrices balFlow := by
    refine ⟨hfeas, fun f' hf' => ?_⟩
    have hle : flowValue f' ≤ ∑ g : Fin 2, lowPrices g * splitFisher.supply g :=
      Finset.sum_le_sum fun g _ => hf'.2.2.1 g
    have hval : flowValue balFlow = 4 := by
      simp [flowValue, balFlow, Fin.sum_univ_two]; norm_num
    have hsum : ∑ g : Fin 2, lowPrices g * splitFisher.supply g = 4 := by
      simp [lowPrices, splitFisher, Fin.sum_univ_two]; norm_num
    linarith
  have hsurp_bal : splitFisher.surplus balFlow = ![3, 3] := by
    funext i; rcases fin_two_cases i with rfl | rfl
    · simp [surplus, splitFisher, balFlow, Fin.sum_univ_two]
    · simp [surplus, splitFisher, balFlow, Fin.sum_univ_two]; norm_num
  have hbal : splitFisher.IsBalancedFlow lowPrices balFlow := by
    rw [isBalancedFlow_iff_satisfiesPropertyOne hmax]
    intro j i hlt
    rw [hsurp_bal] at hlt
    rcases fin_two_cases j with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
      simp at hlt
  have hinv := splitFisher_lowPrices_invariant_and_no_tight.1
  obtain ⟨_, hprog_bal, hprog_q⟩ := balancedFlowProgram_spec (M := splitFisher) (p := lowPrices)
    (by simp [lowPrices, Fin.forall_fin_two]) hinv isValidMaxFlowOracle_canonical
  have hprog_surp : splitFisher.surplus
      ((balancedFlowProgram splitFisher lowPrices).eval canonicalMaxFlowOracle) = ![3, 3] := by
    rw [surplus_eq_of_isBalancedFlow hprog_bal hbal, hsurp_bal]
  exact ⟨hbal, hprog_bal, hprog_surp, by simpa using hprog_q⟩

/-! ### 4. Connected Case-2 split and Lemmas 5.9–5.11 (finding tight sets) -/

/-- Connected `2 × 2` market with budgets `![10, 4]` and utilities `![![4, 1], ![2, 2]]`.
At `lowPrices = ![2, 2]`, the balanced flow splits into unequal surpluses `![8, 2]` (Case 2) and
the tight-set search yields strict proper subset `S* = {1}` at scale `x* = 2`. -/
noncomputable def splitCase2 : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply ![10, 4] ![![4, 1], ![2, 2]]
    (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two])

theorem splitCase2_equalityEdge :
    splitCase2.IsEqualityEdge lowPrices 0 0 ∧
      ¬ splitCase2.IsEqualityEdge lowPrices 0 1 ∧
      splitCase2.IsEqualityEdge lowPrices 1 0 ∧
      splitCase2.IsEqualityEdge lowPrices 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g'; rcases fin_two_cases g' with rfl | rfl
    · exact le_rfl
    · simp [splitCase2, bangPerBuck_eq, lowPrices]; norm_num
  · intro h; have := h 0; simp [splitCase2, bangPerBuck_eq, lowPrices] at this; norm_num at this
  · intro g'; rcases fin_two_cases g' with rfl | rfl <;>
      simp [splitCase2, bangPerBuck_eq, lowPrices]
  · intro g'; rcases fin_two_cases g' with rfl | rfl <;>
      simp [splitCase2, bangPerBuck_eq, lowPrices]

/-- **Connected Case-2 balanced-flow witness:** on `splitCase2` at `![2, 2]`, `naiveFlow` is
actually the **balanced** flow, with strictly unequal surpluses `![8, 2]`! -/
theorem splitCase2_unequal_balanced_flow :
    splitCase2.IsBalancedFlow lowPrices naiveFlow ∧
      splitCase2.surplus naiveFlow = ![8, 2] := by
  obtain ⟨h00, h01, _, h11⟩ := splitCase2_equalityEdge
  have hfeas : splitCase2.IsEqualityFlow lowPrices naiveFlow := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [naiveFlow, Fin.forall_fin_two]
    · intro g i hpos
      rcases fin_two_cases g with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl <;>
        simp [naiveFlow] at hpos
      · exact h00
      · exact h11
    · simp [naiveFlow, splitCase2, lowPrices, Fin.forall_fin_two, Fin.sum_univ_two]
    · simp [naiveFlow, splitCase2, Fin.forall_fin_two, Fin.sum_univ_two]; norm_num
  have hmax : splitCase2.IsMaxEqualityFlow lowPrices naiveFlow := by
    refine ⟨hfeas, fun f' hf' => ?_⟩
    have hle : flowValue f' ≤ ∑ g : Fin 2, lowPrices g * splitCase2.supply g :=
      Finset.sum_le_sum fun g _ => hf'.2.2.1 g
    have hval : flowValue naiveFlow = 4 := by
      simp [flowValue, naiveFlow, Fin.sum_univ_two]; norm_num
    have hsum : ∑ g : Fin 2, lowPrices g * splitCase2.supply g = 4 := by
      simp [lowPrices, splitCase2, Fin.sum_univ_two]; norm_num
    linarith
  have hsurp : splitCase2.surplus naiveFlow = ![8, 2] := by
    funext i; rcases fin_two_cases i with rfl | rfl <;>
      (simp [surplus, splitCase2, naiveFlow, Fin.sum_univ_two]; norm_num)
  refine ⟨(isBalancedFlow_iff_satisfiesPropertyOne hmax).2 ?_, hsurp⟩
  intro j i hlt hreach
  rw [hsurp] at hlt
  have hj1 : j = 1 ∧ i = 0 := by
    rcases fin_two_cases j with rfl | rfl <;> rcases fin_two_cases i with rfl | rfl
    · simp at hlt
    · simp at hlt; norm_num at hlt
    · exact ⟨rfl, rfl⟩
    · simp at hlt
  rcases hj1 with ⟨rfl, rfl⟩
  -- Every step from `1` uses `0 < naiveFlow g 1` (forcing `g = 1`) and `IsEqualityEdge v 1`
  -- (forcing `v = 1`), so `1` can never reach `0`.
  have hstay : ∀ u v, splitCase2.ResidualReachable lowPrices naiveFlow u v → u = 1 → v = 1 := by
    intro u v huv
    induction huv with
    | refl => exact id
    | @tail a b _ hab ih =>
      intro hu
      have ha1 := ih hu
      subst ha1
      obtain ⟨g, hpos, hE⟩ := hab
      have hg1 : g = 1 := by
        rcases fin_two_cases g with rfl | rfl
        · simp [naiveFlow] at hpos
        · rfl
      subst hg1
      rcases fin_two_cases b with rfl | rfl
      · exact absurd hE h01
      · rfl
  exact absurd (hstay 1 0 hreach rfl) (by decide)

/-- **Lemmas 5.9–5.11 (strict-subset tight-set search witness):** on `splitCase2` at `![2, 2]`,
`minTightRatio = 2`, `tightSetAtMinRatio = {1}` (strict subset of `Finset.univ`), and
`findTightSetProgram` recovers `(2, {1})` in at most `2` max-flow oracle calls. -/
theorem splitCase2_findTightSet_spec :
    let hA : (Finset.univ : Finset (Fin 2)).Nonempty := Finset.univ_nonempty
    splitCase2.minTightRatio lowPrices Finset.univ hA = 2 ∧
      splitCase2.tightSetAtMinRatio lowPrices Finset.univ hA = {1} ∧
      (let prog := findTightSetProgram splitCase2 lowPrices Finset.univ
       prog.eval canonicalMaxFlowOracle = (2, {1}) ∧
         prog.countQueries canonicalMaxFlowOracle ≤ 2) := by
  obtain ⟨h00, h01, h10, h11⟩ := splitCase2_equalityEdge
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hA : (Finset.univ : Finset (Fin 2)).Nonempty := Finset.univ_nonempty
  have hp : ∀ g ∈ (Finset.univ : Finset (Fin 2)), 0 < lowPrices g * splitCase2.supply g := by
    simp [lowPrices, splitCase2, Fin.forall_fin_two]
  have hnbr0 : splitCase2.buyerNeighborhood lowPrices {0} = {0, 1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
  have hnbr1 : splitCase2.buyerNeighborhood lowPrices {1} = {1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h01, h11]
  have hnbr01 : splitCase2.buyerNeighborhood lowPrices {0, 1} = {0, 1} := by
    ext i; rcases fin_two_cases i with rfl | rfl <;> simp [mem_buyerNeighborhood, h00, h10]
  set x := splitCase2.minTightRatio lowPrices Finset.univ hA
  set S := splitCase2.tightSetAtMinRatio lowPrices Finset.univ hA
  have hx_le : x ≤ 2 := by
    have h1 := minTightRatio_mul_goodValue_le hA hp (Finset.subset_univ {1})
    change x * splitCase2.goodValue lowPrices {1} ≤
      splitCase2.budgetSum (splitCase2.buyerNeighborhood lowPrices {1}) at h1
    have hgv : splitCase2.goodValue lowPrices {1} = 2 := by
      simp [goodValue, splitCase2, lowPrices]
    have hbud : splitCase2.budgetSum (splitCase2.buyerNeighborhood lowPrices {1}) = 4 := by
      rw [hnbr1]; simp [budgetSum, splitCase2]
    rw [hgv, hbud] at h1
    linarith
  obtain ⟨hS_sub, hS_ne, hS_tight, hS_max⟩ := tightSetAtMinRatio_spec hA hp
  change x * splitCase2.goodValue lowPrices S =
    splitCase2.budgetSum (splitCase2.buyerNeighborhood lowPrices S) at hS_tight
  have hx_ge : 2 ≤ x := by
    have hcases : S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · right; right; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · right; left; ext g; rcases fin_two_cases g with rfl | rfl <;> simp [h0, h1]
      · exfalso; obtain ⟨g, hg⟩ := hS_ne
        rcases fin_two_cases g with rfl | rfl <;> contradiction
    rcases hcases with hS | hS | hS <;> rw [hS] at hS_tight
    · rw [hnbr0] at hS_tight
      simp [goodValue, budgetSum, splitCase2, lowPrices, Finset.sum_pair hne01] at hS_tight
      linarith
    · rw [hnbr1] at hS_tight
      simp [goodValue, budgetSum, splitCase2, lowPrices] at hS_tight
      linarith
    · rw [hnbr01] at hS_tight
      simp [goodValue, budgetSum, splitCase2, lowPrices, Finset.sum_pair hne01] at hS_tight
      linarith
  have hx_eq : x = 2 := le_antisymm hx_le hx_ge
  have h1_sub : {1} ⊆ S :=
    hS_max {1} (Finset.subset_univ _) (by
      change x * splitCase2.goodValue lowPrices {1} =
        splitCase2.budgetSum (splitCase2.buyerNeighborhood lowPrices {1})
      rw [hx_eq, hnbr1]; simp [goodValue, budgetSum, splitCase2, lowPrices]; norm_num)
  have hS_eq : S = {1} := by
    apply Finset.Subset.antisymm _ h1_sub
    intro g hg
    rcases fin_two_cases g with rfl | rfl
    · exfalso
      have h01_eq : S = {0, 1} := by
        ext y; rcases fin_two_cases y with rfl | rfl
        · simp [hg]
        · simp [h1_sub (Finset.mem_singleton_self 1)]
      rw [hx_eq, h01_eq, hnbr01] at hS_tight
      simp [goodValue, budgetSum, splitCase2, lowPrices, Finset.sum_pair hne01] at hS_tight
      norm_num at hS_tight
    · exact Finset.mem_singleton_self 1
  obtain ⟨hprog_eval, hprog_q⟩ :=
    findTightSetProgram_spec hA hp isValidMaxFlowOracle_canonical
  change (findTightSetProgram splitCase2 lowPrices Finset.univ).eval canonicalMaxFlowOracle =
    (x, S) at hprog_eval
  rw [hx_eq, hS_eq] at hprog_eval
  exact ⟨hx_eq, hS_eq, hprog_eval, by simpa using hprog_q⟩

/-! ### 5. Lemma 5.12 & Theorem 5.1 part 4 (rationality & polynomial bit-length bounds) -/

/-- **Lemma 5.12 witness:** at `tightPrices = ![3, 2]` on tight set `{0}`, good `0`'s price is
rational with denominator `≤ 1 * 4 ^ 0 = 1`. -/
theorem splitFisher_lemma5_12_witness :
    ∃ q : ℚ, (q : ℝ) = tightPrices 0 ∧ q.den ≤ 1 := by
  obtain ⟨hinv, htight0, -⟩ := splitFisher_tightPrices_invariant_and_maximalTightSet
  obtain ⟨q, hq_eq, hq_den, -⟩ := exists_rat_price_of_isTightSet (M := splitFisher)
    (fun _ => by simp [splitFisher]) (u := ![![4, 1], ![2, 2]])
    (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        simp [splitFisher])
    (U := 4) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> decide)
    (e := ![3, 7]) (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [splitFisher])
    splitFisher_isNonDegenerate.buyer_nonsatiated
    (by simp [tightPrices, Fin.forall_fin_two]) hinv htight0 (Finset.mem_singleton_self 0)
  exact ⟨q, hq_eq, by simpa using hq_den⟩

/-- **Theorem 5.1 part 4 (integer-input witness):** `splitFisher` admits a rational equilibrium
`(xQ, pQ)` with `pQ = ![5, 5]` and explicit denominator/numerator bounds (`≤ 32` and `≤ 160`). -/
theorem splitFisher_rational_equilibrium_nat :
    ∃ (xQ : Fin 2 → Fin 2 → ℚ) (pQ : Fin 2 → ℚ),
      splitFisher.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) ∧
      pQ = ![5, 5] ∧
      (∀ g, (pQ g).den ≤ 32 ∧ (pQ g).num.natAbs ≤ 160) ∧
      (∀ i g, (xQ i g).den ≤ 160 ∧ (xQ i g).num.natAbs ≤ 160) := by
  obtain ⟨xQ, pQ, hEq, hpB, hxB⟩ := exists_rational_equilibrium_of_nat (M := splitFisher)
    splitFisher_isNonDegenerate (fun _ => by simp [splitFisher])
    (u := ![![4, 1], ![2, 2]]) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        simp [splitFisher])
    (U := 4) (fun i g => by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> decide)
    (e := ![3, 7]) (fun i => by rcases fin_two_cases i with rfl | rfl <;> simp [splitFisher])
  have hp_eq : pQ = ![5, 5] := by
    have hr := price_eq_of_isEquilibrium splitFisher_isNonDegenerate hEq splitFisher_isEquilibrium
    funext g
    have hg := congrFun hr g
    rcases fin_two_cases g with rfl | rfl
    · have h0 : (pQ 0 : ℝ) = ((5 : ℚ) : ℝ) := by
        simpa only [eqPrices, Matrix.cons_val_zero, Rat.cast_ofNat] using hg
      exact Rat.cast_injective h0
    · have h1 : (pQ 1 : ℝ) = ((5 : ℚ) : ℝ) := by
        simpa only [eqPrices, Matrix.cons_val_one, Matrix.cons_val_fin_one, Rat.cast_ofNat] using hg
      exact Rat.cast_injective h1
  refine ⟨xQ, pQ, hEq, hp_eq, fun g => ?_, fun i g => ?_⟩
  · simpa [Fin.sum_univ_two] using hpB g
  · simpa [Fin.sum_univ_two] using hxB i g

/-- Fractional unit-supply `2 × 2` linear Fisher market with rational budgets `![1/2, 3/2]` and
rational utilities `![![3/2, 1/3], ![1/2, 1/2]]`. -/
noncomputable def ratFisher : LinearFisherMarket (Fin 2) (Fin 2) :=
  LinearFisherMarket.unitSupply
    (fun i => ((![(1 : ℚ) / 2, (3 : ℚ) / 2] i : ℚ) : ℝ))
    (fun i g => ((![![(3 : ℚ) / 2, (1 : ℚ) / 3], ![(1 : ℚ) / 2, (1 : ℚ) / 2]] i g : ℚ) : ℝ))
    (by intro i; rcases fin_two_cases i with rfl | rfl <;> norm_num)
    (by
      intro i g
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;> norm_num)

/-- **Theorem 5.1 part 4 (general rational-input witness):** `ratFisher` satisfies `IsNonDegenerate`
and admits a rational equilibrium `(xQ, pQ)` with explicit polynomial-bit numerator and denominator
bounds via `exists_rational_equilibrium_of_rat`. -/
theorem ratFisher_rational_equilibrium :
    ∃ (xQ : Fin 2 → Fin 2 → ℚ) (pQ : Fin 2 → ℚ),
      ratFisher.IsEquilibrium (fun i g => (xQ i g : ℝ)) (fun g => (pQ g : ℝ)) ∧
      (∀ g, (pQ g).den ≤ 2 * (3 * 3 ^ 2) ^ 2 * 3 ^ 2 ∧
        (pQ g).num.natAbs ≤ 2 * 3 * 3 ^ 2 * (3 * 3 ^ 2) ^ 2) ∧
      (∀ i g, (xQ i g).den ≤ 2 * 3 * 3 ^ 2 * (3 * 3 ^ 2) ^ 2 ∧
        (xQ i g).num.natAbs ≤ 2 * 3 * 3 ^ 2 * (3 * 3 ^ 2) ^ 2) := by
  have hnd : ratFisher.IsNonDegenerate := {
    budget_pos := by intro i; rcases fin_two_cases i with rfl | rfl <;> simp [ratFisher]
    supply_pos := by simp [ratFisher]
    buyer_nonsatiated := by
      intro i; rcases fin_two_cases i with rfl | rfl
      · exact ⟨0, by simp [ratFisher]⟩
      · exact ⟨0, by simp [ratFisher]⟩
    good_desired := by
      intro g; rcases fin_two_cases g with rfl | rfl
      · exact ⟨0, by simp [ratFisher]⟩
      · exact ⟨0, by simp [ratFisher]⟩
  }
  simpa using exists_rational_equilibrium_of_rat (M := ratFisher) hnd
    (fun _ => by simp [ratFisher])
    (uQ := ![![(3 : ℚ) / 2, (1 : ℚ) / 3], ![(1 : ℚ) / 2, (1 : ℚ) / 2]])
    (fun _ _ => by simp [ratFisher])
    (eQ := ![(1 : ℚ) / 2, (3 : ℚ) / 2]) (fun _ => by simp [ratFisher])
    (B_num := 3) (B_den := 3)
    (by
      intro i g
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
         first
         | exact (rat_num_den_le (a := 3) (b := 2) (B := 3) (by decide) (by decide) (by decide)).1
         | exact (rat_num_den_le (a := 1) (b := 3) (B := 3) (by decide) (by decide) (by decide)).1
         | exact (rat_num_den_le (a := 1) (b := 2) (B := 3) (by decide) (by decide) (by decide)).1))
    (by
      intro i g
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases g with rfl | rfl <;>
        (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
         first
         | exact (rat_num_den_le (a := 3) (b := 2) (B := 3) (by decide) (by decide) (by decide)).2
         | exact (rat_num_den_le (a := 1) (b := 3) (B := 3) (by decide) (by decide) (by decide)).2
         | exact (rat_num_den_le (a := 1) (b := 2) (B := 3) (by decide) (by decide) (by decide)).2))
    (by
      intro i
      rcases fin_two_cases i with rfl | rfl <;>
        (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
         first
         | exact (rat_num_den_le (a := 1) (b := 2) (B := 3) (by decide) (by decide) (by decide)).1
         | exact (rat_num_den_le (a := 3) (b := 2) (B := 3) (by decide) (by decide) (by decide)).1))
    (by
      intro i
      rcases fin_two_cases i with rfl | rfl <;>
        (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
         first
         | exact (rat_num_den_le (a := 1) (b := 2) (B := 3) (by decide) (by decide) (by decide)).2
         | exact (rat_num_den_le (a := 3) (b := 2) (B := 3) (by decide) (by decide) (by decide)).2))

end CslibFrontierTests.GameTheory.BalancedFlow
