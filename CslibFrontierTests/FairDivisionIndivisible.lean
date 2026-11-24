/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.FairDivision.Indivisible.EnvyCycle
public import CslibFrontier.GameTheory.FairDivision.Indivisible.NashWelfare
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.FinCases

/-!
# Checked tests for indivisible-goods fair division (`EF1`, LMMS envy cycles, and `MNW`)

Kernel-checked (`decide`, zero `native_decide`) witnesses and boundary separations exercising
`Indivisible.Basic`, `Indivisible.EnvyCycle`, and `Indivisible.NashWelfare`:

1. **Boundary cases (`m = 0` and single indivisible good `n = 2, m = 1`)**: agreement on empty
   markets, and impossibility of exact `IsEnvyFree` for two agents contesting one positively valued
   good while `IsEFX`, `IsEF1`, and `IsParetoOptimal` hold.
2. **Strict fairness hierarchy separations (`IsEnvyFree ⊂ IsEFX ⊂ IsEF1`)**: concrete allocations
   witnessing `IsEFX ∧ ¬ IsEnvyFree` and `IsEF1 ∧ ¬ IsEFX` under strictly positive additive weights.
3. **Non-additive supermodular `MonotoneValuation` with active LMMS cycle elimination**: a 2-agent,
   3-good complementary valuation (`v_0({0, 1}) = 12 > 1 + 3 = v_0({0}) + v_0({1})`) on which
   `lmmsRun` encounters a directed 2-cycle `0 ↔ 1`, executes `totalCycleSwaps = 1`, and returns a
   complete `EF1` allocation satisfying `lmmsAllocate_val_le_add_maxMarginal`.
4. **Pareto suboptimality of Round-Robin vs. `EF1 + PO` of Maximum Nash Welfare (`n = 2, m = 4`)**:
   an additive market where `roundRobin` yields utilities `(9, 3)` (`EF1` but Pareto-dominated),
   whereas `maxNashWelfareAllocation` yields `(10, 8)` (Nash product `80 > 27`, strictly improving
   both agents while satisfying `IsMaxNashWelfare`, `IsEF1`, and `IsParetoOptimal`).
5. **Degenerate zero-full-product `MNW` boundary (`n = 3, m = 2`)**: every complete allocation has
   full 3-agent product `0`, hoarding `![0, 0]` fails both `IsEF1` and `IsMaxNashWelfare`, and
   two-stage `maxNashWelfareAllocation` maximizes `|posAgents| = 2` with `nashProduct = 40`,
   `IsEF1`, and `IsParetoOptimal`.
-/

@[expose] public section

namespace CslibFrontierTests.FairDivisionIndivisible

open Cslib.GameTheory.FairDivision.Indivisible

/-- Helper building an integer `AdditiveValuation` from a weight matrix with decidable
nonnegativity. -/
def mkAddVal {n m : ℕ} (w : Fin n → Fin m → ℤ)
    (hw : ∀ i g, 0 ≤ w i g := by decide) : AdditiveValuation n m ℤ :=
  ⟨w, hw⟩

/-! ### 1. Boundary cases (`m = 0` and `n = 2, m = 1`) -/

def emptyGoodsVal : AdditiveValuation 2 0 ℤ :=
  mkAddVal fun _ => Fin.elim0

example :
    emptyGoodsVal.roundRobin (by decide) = BundleAllocation.empty ∧
      emptyGoodsVal.toMonotoneValuation.lmmsAllocate (by decide) = BundleAllocation.empty ∧
      emptyGoodsVal.maxNashWelfareAllocation (by decide) = BundleAllocation.empty ∧
      emptyGoodsVal.IsMaxNashWelfare BundleAllocation.empty := by
  decide

def singleGoodContest : AdditiveValuation 2 1 ℤ :=
  mkAddVal ![![10], ![10]]

/-- With one contested indivisible good, no complete allocation is envy-free, while MNW achieves
both `IsEFX` (hence `IsEF1`) and `IsParetoOptimal`. -/
theorem singleGoodContest_no_ef_but_efx_po :
    (∀ A ∈ BundleAllocation.completeAllocations 2 1,
        ¬ singleGoodContest.toMonotoneValuation.IsEnvyFree A) ∧
      singleGoodContest.toMonotoneValuation.IsEFX
        (singleGoodContest.maxNashWelfareAllocation (by decide)) ∧
      singleGoodContest.toMonotoneValuation.IsParetoOptimal
        (singleGoodContest.maxNashWelfareAllocation (by decide)) := by
  decide

/-! ### 2. Strict separation `IsEF1 ∧ ¬ IsEFX` under strictly positive weights -/

def posThreeGoods : AdditiveValuation 2 3 ℤ :=
  mkAddVal ![![4, 1, 1], ![4, 1, 1]]

def allocEF1NotEFX : BundleAllocation 2 3 :=
  BundleAllocation.ofAssignment ![0, 0, 1]

/-- Agent `1` holds `{2}` (value `1`) while agent `0` holds `{0, 1}` (values `4` and `1`): removing
good `0` eliminates envy (`1 ≤ 1`), so `IsEF1` holds, whereas removing good `1` leaves `{0}`
(`4 > 1`), so `IsEFX` fails. -/
theorem allocEF1NotEFX_sep :
    posThreeGoods.toMonotoneValuation.IsEF1 allocEF1NotEFX ∧
      ¬ posThreeGoods.toMonotoneValuation.IsEFX allocEF1NotEFX := by
  decide

/-! ### 3. Non-additive supermodular `MonotoneValuation` triggering LMMS cycle elimination -/

/-- Supermodular valuation where goods `{0, 1}` have a complementarity bonus of `+8` for agent `0`.
-/
def supermodValFun : Fin 2 → Finset (Fin 3) → ℤ
  | 0, S =>
    (if (0 : Fin 3) ∈ S ∧ (1 : Fin 3) ∈ S then 8 else 0) +
      ∑ g ∈ S, (![1, 3, 4] : Fin 3 → ℤ) g
  | 1, S =>
    ∑ g ∈ S, (![5, 1, 6] : Fin 3 → ℤ) g

def supermodValuation : MonotoneValuation 2 3 ℤ where
  val := supermodValFun
  mono i {S T} hST := by
    fin_cases i
    · dsimp only [supermodValFun]
      have hbonus : (if (0 : Fin 3) ∈ S ∧ (1 : Fin 3) ∈ S then (8 : ℤ) else 0) ≤
          if (0 : Fin 3) ∈ T ∧ (1 : Fin 3) ∈ T then 8 else 0 := by
        split_ifs with hS hT
        · exact le_rfl
        · exact absurd ⟨hST hS.1, hST hS.2⟩ hT
        · decide
        · exact le_rfl
      have hsum : ∑ g ∈ S, (![1, 3, 4] : Fin 3 → ℤ) g ≤
          ∑ g ∈ T, (![1, 3, 4] : Fin 3 → ℤ) g :=
        Finset.sum_le_sum_of_subset_of_nonneg hST fun g _ _ => by fin_cases g <;> decide
      exact add_le_add hbonus hsum
    · dsimp only [supermodValFun]
      exact Finset.sum_le_sum_of_subset_of_nonneg hST fun g _ _ => by fin_cases g <;> decide

/-- `supermodValuation` is genuinely non-additive (`v_0({0, 1}) = 12 > 1 + 3`), triggers an
envy-cycle rotation during `lmmsRun` (`totalCycleSwaps = 1`), and yields a complete `EF1` allocation
`{1, 2}` for agent `0` and `{0}` for agent `1`. -/
theorem supermodValuation_lmms_witness :
    supermodValuation.val 0 {0, 1} ≠
        supermodValuation.val 0 {0} + supermodValuation.val 0 {1} ∧
      (supermodValuation.lmmsRun (by decide)).totalCycleSwaps = 1 ∧
      (supermodValuation.lmmsAllocate (by decide)).bundle 0 = {1, 2} ∧
      (supermodValuation.lmmsAllocate (by decide)).bundle 1 = {0} ∧
      supermodValuation.IsEF1 (supermodValuation.lmmsAllocate (by decide)) ∧
      (∀ i j : Fin 2,
        supermodValuation.val i ((supermodValuation.lmmsAllocate (by decide)).bundle j) ≤
          supermodValuation.val i ((supermodValuation.lmmsAllocate (by decide)).bundle i) +
            supermodValuation.maxMarginal i) := by
  refine ⟨by decide, by decide, by decide, by decide,
    supermodValuation.isEF1_lmmsAllocate (by decide),
    supermodValuation.lmmsAllocate_val_le_add_maxMarginal (by decide)⟩

/-! ### 4. Round-Robin (`EF1`, not `PO`) vs. Maximum Nash Welfare (`EF1` and `PO`) -/

def rrSuboptMarket : AdditiveValuation 2 4 ℤ :=
  mkAddVal ![![5, 4, 4, 2], ![8, 2, 2, 1]]

/-- On `rrSuboptMarket`, Round-Robin gives utilities `(9, 3)` (`EF1`, not `PO`), whereas
`maxNashWelfareAllocation` equals `ofAssignment ![1, 0, 0, 0]` with utilities `(10, 8)`
(`nashProduct = 80`), strictly improving both agents and achieving `IsMaxNashWelfare`, `IsEF1`, and
`IsParetoOptimal`. -/
theorem rrSuboptMarket_mnw_dominates_roundRobin :
    let rr := rrSuboptMarket.roundRobin (by decide)
    let mnw := rrSuboptMarket.maxNashWelfareAllocation (by decide)
    mnw = BundleAllocation.ofAssignment ![1, 0, 0, 0] ∧
      rrSuboptMarket.toMonotoneValuation.IsEF1 rr ∧
      ¬ rrSuboptMarket.toMonotoneValuation.IsParetoOptimal rr ∧
      rrSuboptMarket.bundleVal 0 (rr.bundle 0) = 9 ∧
      rrSuboptMarket.bundleVal 1 (rr.bundle 1) = 3 ∧
      rrSuboptMarket.bundleVal 0 (mnw.bundle 0) = 10 ∧
      rrSuboptMarket.bundleVal 1 (mnw.bundle 1) = 8 ∧
      rrSuboptMarket.nashProduct mnw = 80 ∧
      rrSuboptMarket.IsMaxNashWelfare (BundleAllocation.ofAssignment ![1, 0, 0, 0]) ∧
      rrSuboptMarket.toMonotoneValuation.IsEF1 mnw ∧
      rrSuboptMarket.toMonotoneValuation.IsParetoOptimal mnw := by
  have hmnw := rrSuboptMarket.isEF1_and_isParetoOptimal_maxNashWelfareAllocation (by decide)
  exact ⟨by decide, rrSuboptMarket.isEF1_roundRobin (by decide), by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, hmnw.2.1, hmnw.2.2⟩

/-! ### 5. Degenerate zero-full-product MNW witness (`n = 3, m = 2`) -/

def degenMarket : AdditiveValuation 3 2 ℤ :=
  mkAddVal ![![10, 10], ![4, 4], ![0, 0]]

/-- Every complete allocation on `degenMarket` has full 3-agent utility product `0`, hoarding both
items at agent `0` (`ofAssignment ![0, 0]`) fails `IsEF1` and `IsMaxNashWelfare`, and two-stage
`maxNashWelfareAllocation` achieves `|posAgents| = 2`, `nashProduct = 40`, `IsEF1`, and
`IsParetoOptimal`. -/
theorem degenMarket_two_stage_mnw :
    (∀ B ∈ BundleAllocation.completeAllocationList 3 2,
        (∏ i : Fin 3, degenMarket.bundleVal i (B.bundle i)) = 0) ∧
      ¬ degenMarket.toMonotoneValuation.IsEF1 (BundleAllocation.ofAssignment ![0, 0]) ∧
      ¬ degenMarket.IsMaxNashWelfare (BundleAllocation.ofAssignment ![0, 0]) ∧
      let mnw := degenMarket.maxNashWelfareAllocation (by decide)
      (degenMarket.posAgents mnw).card = 2 ∧
        degenMarket.nashProduct mnw = 40 ∧
        degenMarket.toMonotoneValuation.IsEF1 mnw ∧
        degenMarket.toMonotoneValuation.IsParetoOptimal mnw := by
  have hmnw := degenMarket.isEF1_and_isParetoOptimal_maxNashWelfareAllocation (by decide)
  exact ⟨by decide, by decide, by decide, by decide, by decide, hmnw.2.1, hmnw.2.2⟩

end CslibFrontierTests.FairDivisionIndivisible
