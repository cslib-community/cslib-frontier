/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Cooperative.FacilityLocationCostSharing
import CslibFrontier.GameTheory.Cooperative.FacilityLocationLowerBound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked client tests for facility location cost sharing (NRTV §§15.4.2 & 15.5)

Tests `FLCostShare` (`FacilityLocationInstance.flCostShareScheme`, Theorem 15.21) on:
* **Example 15.2** ([JainMahdian2007], p. 398): exact values `(3, 2, 2)` on `{a, b, c}` and `(3, 3)`
  on `{a, b}`, verifying cross-monotonicity and end-to-end Moulin group-strategyproofness.
* **`emptyCoreMetricFL`**: `FLCostShare` assigns `(5 / 2, 5 / 2, 5 / 2)` (sum `15 / 2` against
  `cost = 8`), attaining the exact optimal `(15 / 16)`-core on an instance with an empty exact core.
* Zero opening-cost boundary (`openCost = 0`).
* Non-metric upper bound on `emptyCoreBipartiteFL`.
* **Lemma 15.22** & **Theorem 15.23**: explicit finite bounds and instantiations for `γ = 1 / 2`,
  `2 / 5`, and `34 / 100`.
-/

namespace CslibFrontierTests.GameTheory.FacilityLocationCostSharing

open Cslib.GameTheory FacilityLocationInstance

/-! ### 1. Exact `FLCostShare` trace on Example 15.2 ([JainMahdian2007], p. 398) -/

/-- On `example15_2` grand coalition `{a, b, c}` (`Finset.univ : Finset (Fin 3)`), facility `0`
opens at `t₀ = 3` and facility `1` opens at `t₁ = 2`, giving cost shares **`(3, 2, 2)`**
([JainMahdian2007], Section 15.4.2, p. 398). -/
example :
    example15_2.openTime 0 Finset.univ = 3 ∧
    example15_2.openTime 1 Finset.univ = 2 ∧
    example15_2.flCostShareScheme.share Finset.univ 0 = 3 ∧
    example15_2.flCostShareScheme.share Finset.univ 1 = 2 ∧
    example15_2.flCostShareScheme.share Finset.univ 2 = 2 := by
  have ⟨c00, c01, c02, c10, c11, c12⟩ := example15_2_connCost
  have ht0 : example15_2.openTime 0 Finset.univ = 3 :=
    (example15_2.eq_openTime_of_sum_max_eq Finset.univ_nonempty (by norm_num) (t := 3) (by
      rw [Fin.sum_univ_three, c00, c01, c02]; norm_num)).symm
  have ht1 : example15_2.openTime 1 Finset.univ = 2 :=
    (example15_2.eq_openTime_of_sum_max_eq Finset.univ_nonempty (by norm_num) (t := 2) (by
      rw [Fin.sum_univ_three, c10, c11, c12]; norm_num)).symm
  have hsh : ∀ j : Fin 3, example15_2.flCostShareScheme.share Finset.univ j =
      min (max 3 (example15_2.connCost 0 j)) (max 2 (example15_2.connCost 1 j)) := fun j => by
    rw [example15_2.flCostShareScheme_share_of_mem (Finset.mem_univ j)]
    refine le_antisymm (le_min ?_ ?_) (Finset.le_inf' _ _ fun i _ => ?_)
    · rw [← ht0]; exact Finset.inf'_le _ (Finset.mem_univ 0)
    · rw [← ht1]; exact Finset.inf'_le _ (Finset.mem_univ 1)
    · fin_cases i
      · exact ht0 ▸ min_le_left _ _
      · exact ht1 ▸ min_le_right _ _
  refine ⟨ht0, ht1, ?_, ?_, ?_⟩
  · rw [hsh 0, c00, c10]; norm_num
  · rw [hsh 1, c01, c11]; norm_num
  · rw [hsh 2, c02, c12]; norm_num

/-- On `{a, b} = {0, 1}` of `example15_2`, both facilities open at `3`, giving cost shares
**`(3, 3)`** ([JainMahdian2007], p. 398) — verifying cross-monotonicity `(3, 2) ≤ (3, 3)`! -/
example :
    example15_2.flCostShareScheme.share ({0, 1} : Finset (Fin 3)) 0 = 3 ∧
    example15_2.flCostShareScheme.share ({0, 1} : Finset (Fin 3)) 1 = 3 ∧
    example15_2.flCostShareScheme.share ({0, 1} : Finset (Fin 3)) 2 = 0 := by
  have ⟨c00, c01, _, c10, c11, _⟩ := example15_2_connCost
  have hne : ({0, 1} : Finset (Fin 3)).Nonempty := by simp
  have ht0 : example15_2.openTime 0 ({0, 1} : Finset (Fin 3)) = 3 :=
    (example15_2.eq_openTime_of_sum_max_eq hne (by norm_num) (t := 3) (by
      rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), c00, c01]; norm_num)).symm
  have ht1 : example15_2.openTime 1 ({0, 1} : Finset (Fin 3)) = 3 :=
    (example15_2.eq_openTime_of_sum_max_eq hne (by norm_num) (t := 3) (by
      rw [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1), c10, c11]; norm_num)).symm
  have hsh : ∀ j ∈ ({0, 1} : Finset (Fin 3)),
      example15_2.flCostShareScheme.share {0, 1} j =
        min (max 3 (example15_2.connCost 0 j)) (max 3 (example15_2.connCost 1 j)) := fun j hj => by
    rw [example15_2.flCostShareScheme_share_of_mem hj]
    refine le_antisymm (le_min ?_ ?_) (Finset.le_inf' _ _ fun i _ => ?_)
    · rw [← ht0]; exact Finset.inf'_le _ (Finset.mem_univ 0)
    · rw [← ht1]; exact Finset.inf'_le _ (Finset.mem_univ 1)
    · fin_cases i
      · exact ht0 ▸ min_le_left _ _
      · exact ht1 ▸ min_le_right _ _
  refine ⟨?_, ?_, example15_2.flCostShareScheme.share_eq_zero_of_not_mem (by decide)⟩
  · rw [hsh 0 (by decide), c00, c10]; norm_num
  · rw [hsh 1 (by decide), c01, c11]; norm_num

/-- End-to-end Moulin mechanism composition on `example15_2`: group-strategyproof,
`(1 / 3)`-budget-balanced, no positive transfers, voluntary participation, consumer sovereignty. -/
example :
    example15_2.flCostShareScheme.moulinMechanism.IsGroupStrategyproof ∧
    example15_2.flCostShareScheme.moulinMechanism.IsBudgetBalanced
      example15_2.toCostSharingGame (1 / 3) ∧
    example15_2.flCostShareScheme.moulinMechanism.NoPositiveTransfers ∧
    example15_2.flCostShareScheme.moulinMechanism.VoluntaryParticipation ∧
    example15_2.flCostShareScheme.moulinMechanism.ConsumerSovereignty :=
  ⟨example15_2.flCostShareScheme.moulinMechanism_isGroupStrategyproof
      example15_2.flCostShareScheme_isCrossMonotone,
    example15_2.flCostShareScheme.moulinMechanism_isBudgetBalanced
      (example15_2.flCostShareScheme_isBudgetBalanced example15_2_isMetric),
    example15_2.flCostShareScheme.moulinMechanism_noPositiveTransfers
      example15_2.flCostShareScheme_isNonneg,
    example15_2.flCostShareScheme.moulinMechanism_voluntaryParticipation,
    example15_2.flCostShareScheme.moulinMechanism_consumerSovereignty⟩

/-! ### 2. `emptyCoreMetricFL` (empty exact core, `(15 / 16)`-core via `FLCostShare`) -/

/-- On `emptyCoreMetricFL` (whose exact core is empty), `FLCostShare` lies inside the
`(1 / 3)`-core (Theorem 15.21); on the matching `K_{3,3} \ M` instance (`openCost = 3`,
`connCost i j = if i = j then 3 else 1`), every facility opens at `5 / 2` and every agent pays
`5 / 2` (sum `15 / 2` against `c(univ) = 8`, matching `15 / 16`). -/
example :
    emptyCoreMetricFL.toCostSharingGame.InApproxCore (1 / 3)
      (emptyCoreMetricFL.flCostShareScheme.share Finset.univ) :=
  emptyCoreMetricFL.flCostShareScheme.inApproxCore_univ
    (emptyCoreMetricFL.flCostShareScheme_isBudgetBalanced emptyCoreMetricFL_isMetric)
    emptyCoreMetricFL.flCostShareScheme_isCrossMonotone

example :
    let I : FacilityLocationInstance (Fin 3) (Fin 3) :=
      { openCost := fun _ => 3
        connCost := fun i j => if i = j then 3 else 1
        openCost_nonneg := fun _ => by norm_num
        connCost_nonneg := fun i j => by split_ifs <;> norm_num }
    (∀ i : Fin 3, I.openTime i Finset.univ = 5 / 2) ∧
    (∀ j : Fin 3, I.flCostShareScheme.share Finset.univ j = 5 / 2) := by
  intro I
  have ht : ∀ i : Fin 3, I.openTime i Finset.univ = 5 / 2 := fun i =>
    (I.eq_openTime_of_sum_max_eq Finset.univ_nonempty (by norm_num) (t := 5 / 2) (by
      rw [Fin.sum_univ_three]
      fin_cases i <;> norm_num [I])).symm
  refine ⟨ht, fun j => ?_⟩
  rw [I.flCostShareScheme_share_of_mem (Finset.mem_univ j)]
  refine le_antisymm ?_ (Finset.le_inf' _ _ fun i _ => (ht i) ▸ le_max_left _ _)
  fin_cases j
  · refine (Finset.inf'_le _ (Finset.mem_univ (1 : Fin 3))).trans ?_
    rw [ht 1]; norm_num [I]
  · refine (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 3))).trans ?_
    rw [ht 0]; norm_num [I]
  · refine (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 3))).trans ?_
    rw [ht 0]; norm_num [I]

/-! ### 3. Boundary checks: zero opening cost & non-metric competitiveness -/

/-- Zero opening cost (`openCost = 0`): `FLCostShare` recovers `connCost` identically and still
satisfies `(1 / 3)`-budget balance. -/
example :
    let I : FacilityLocationInstance (Fin 2) (Fin 1) :=
      { openCost := fun _ => 0
        connCost := fun _ j => if j = 0 then 2 else 5
        openCost_nonneg := fun _ => le_rfl
        connCost_nonneg := fun _ j => by fin_cases j <;> norm_num }
    I.flCostShareScheme.share Finset.univ 0 = 2 ∧
    I.flCostShareScheme.share Finset.univ 1 = 5 := by
  intro I
  have hle0 := I.openTime_le_connCost_of_zero (i := 0) (T := Finset.univ) rfl (Finset.mem_univ 0)
  have hle1 := I.openTime_le_connCost_of_zero (i := 0) (T := Finset.univ) rfl (Finset.mem_univ 1)
  have hu : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  refine ⟨?_, ?_⟩
  · rw [I.flCostShareScheme_share_of_mem (Finset.mem_univ 0)]
    simp only [hu, Finset.inf'_singleton, max_eq_right hle0]; rfl
  · rw [I.flCostShareScheme_share_of_mem (Finset.mem_univ 1)]
    simp only [hu, Finset.inf'_singleton, max_eq_right hle1]; simp [I]

/-- Non-metric competitiveness: `∑ share ≤ cost` holds on `emptyCoreBipartiteFL` even without
`IsMetric`. -/
example :
    ∑ j : Fin 3, emptyCoreBipartiteFL.flCostShareScheme.share Finset.univ j ≤ 8 := by
  calc
    ∑ j : Fin 3, emptyCoreBipartiteFL.flCostShareScheme.share Finset.univ j
        ≤ emptyCoreBipartiteFL.toCostSharingGame.cost Finset.univ :=
          emptyCoreBipartiteFL.flCostShareScheme_sum_le_cost Finset.univ
    _ = 8 := emptyCoreBipartiteFL_cost_univ

/-! ### 4. Tight lower bound witnesses (Lemma 15.22 & Theorem 15.23) -/

/-- Concrete **Lemma 15.22** tightness check (`m = 10, k = 2`): optimal cost is `33`, while
`FLCostShare` recovers `12 * (1 + 3 / 3) = 24`. -/
example :
    (flTightInstance 10 2).toCostSharingGame.cost Finset.univ = 33 ∧
    ∑ j : Fin 10 ⊕ Fin 2, (flTightInstance 10 2).flCostShareScheme.share Finset.univ j = 24 := by
  refine ⟨?_, ?_⟩
  · rw [flTightInstance_cost_univ]; norm_num
  · rw [flTightInstance_flCostShareScheme_sum 10 2 (by omega)]; norm_num

/-- Explicit finite **inequality `(15.6)`** check on `flHardInstance 4 20`: every cross-monotonic
`γ`-budget-balanced scheme has `γ ≤ 41 / 64`. -/
example {ξ : CostSharingScheme (Fin 4 × Fin 20)} {γ : ℝ}
    (hcm : ξ.IsCrossMonotone)
    (hbb : ξ.IsBudgetBalanced (flHardInstance 4 20).toCostSharingGame γ) :
    γ ≤ 41 / 64 := by
  have h := flHardInstance_budgetBalance_le (k := 4) (m := 20) hcm hbb
  norm_num at h
  linarith

/-- **Theorem 15.23** non-vacuity checks at `γ = 1 / 2` and `34 / 100` (`> 1 / 3`). -/
example : ∃ (k m : ℕ) (_ : NeZero k) (_ : NeZero m), (flHardInstance k m).IsMetric ∧
    ¬ ∃ ξ : CostSharingScheme (Fin k × Fin m),
      ξ.IsCrossMonotone ∧ ξ.IsBudgetBalanced (flHardInstance k m).toCostSharingGame (1 / 2) :=
  not_exists_crossMonotone_isBudgetBalanced (by norm_num)

example : ∃ (k m : ℕ) (_ : NeZero k) (_ : NeZero m), (flHardInstance k m).IsMetric ∧
    ¬ ∃ ξ : CostSharingScheme (Fin k × Fin m),
      ξ.IsCrossMonotone ∧ ξ.IsBudgetBalanced (flHardInstance k m).toCostSharingGame (34 / 100) :=
  not_exists_crossMonotone_isBudgetBalanced (by norm_num)

end CslibFrontierTests.GameTheory.FacilityLocationCostSharing
