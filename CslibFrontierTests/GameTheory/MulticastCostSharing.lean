/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Cooperative.MulticastCostSharing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Multicast cost sharing: concrete witnesses, boundary cases, and mechanism separations

Checked examples and non-vacuity witnesses for
`CslibFrontier.GameTheory.Cooperative.MulticastCostSharing`:

1. **Concrete 4-node Y-shaped multicast tree (`yMulticast`)**:
   - Root `0`, trunk `(0, 1)` of cost `6`, left leaf `(1, 2)` of cost `2` housing receivers `0, 1`,
     and right leaf `(1, 3)` of cost `2` housing receiver `2`.
   - Exact Shapley (`SH`) shares `(3, 3, 4)` on the grand coalition (`3 + 3 + 4 = 10 = cost univ`)
     and core membership via `shScheme_inCore_univ`.
   - Direct behavioral separation on `b = ![4, 4, 3]`:
     - **`MC` (`mcMechanism` / `twoPassReceivers` / `twoPassPayment`)** serves all three receivers
       `{0, 1, 2}` (achieving `maxNetWelfare = 1`) and charges VCG payments `![3, 3, 2]` computed
       by the `2`-pass distributed algorithm (`3 + 3 + 2 = 8 < 10`, strict budget deficit).
     - **`SH` (`shMechanism`)** prunes receiver `2` (`3 < 4`) and serves `{0, 1}` with exact
       budget-balanced payments `![4, 4, 0]` (`4 + 4 = 8 = cost {0, 1}`, net welfare `0`).
2. **Single-link separations, impossibility, `(H_n - 1) C` tightness, and boundaries**:
   - Group-strategyproofness failure of `mcMechanism` vs. group-strategyproofness of `shMechanism`.
   - Green–Laffont / Moulin–Shenker impossibility of `IsDSIC` + `VoluntaryParticipation` +
     `NoPositiveTransfers` + `1`-budget balance + welfare maximization for `|A| ≥ 2`, `C > 0`.
   - Concrete `Fin 3` harmonic bound `(H_3 - 1) * 6 = 5` (both upper bound and tight lower bound).
   - Boundary witnesses: `|A| = 1` (`Fin 1`, `H_1 - 1 = 0`, zero welfare loss for `SH`) and `C = 0`.
3. **Path cut communication lower bound (`pathMulticast 3`)**:
   - Injectivity of `pathBottomShare 3`, bottom-service characterization, and concrete `(4 : ℕ∞)`
     communication complexity lower bound.
-/

namespace CslibFrontierTests.GameTheory.MulticastCostSharing

open Cslib.GameTheory

/-! ## 1. Concrete 4-node Y-shaped multicast tree -/

/-- Rooted Y-shaped tree on `Fin 4`: root `0`, trunk `1` (`parent 1 = 0`), leaves `2, 3`
(`parent 2 = parent 3 = 1`). -/
def yTree : RootedTree (Fin 4) where
  root := 0
  parent
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | 3 => 1
  parent_root := rfl
  reaches_root v := ⟨2, by fin_cases v <;> rfl⟩

/-- Concrete 4-node, 3-receiver Y-shaped multicast instance: trunk `(0, 1)` costs `6`, leaves
`(1, 2)` and `(1, 3)` cost `2` each; receivers `0, 1` reside at leaf `2` and receiver `2` resides at
leaf `3`. -/
def yMulticast : MulticastInstance (Fin 4) (Fin 3) where
  tree := yTree
  edgeCost
    | 0 => 0
    | 1 => 6
    | 2 => 2
    | 3 => 2
  edgeCost_root := rfl
  edgeCost_nonneg v := by fin_cases v <;> norm_num
  loc
    | 0 => 2
    | 1 => 2
    | 2 => 3

@[simp]
private theorem yMulticast_tree : yMulticast.tree = yTree := rfl

@[simp]
private theorem yTree_root : yTree.root = 0 := rfl

private theorem yTree_parent_parent (x : Fin 4) : yTree.parent (yTree.parent x) = 0 := by
  fin_cases x <;> rfl

private theorem yTree_not_anc (u w : Fin 4) (h0 : u ≠ 0) (hw : u ≠ w) (hp : u ≠ yTree.parent w) :
    ¬ yTree.IsAncestor u w := by
  rintro ⟨k, hk⟩
  rcases k with _ | _ | k
  · exact hw hk.symm
  · exact hp hk.symm
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', yTree_parent_parent] at hk
    exact h0 hk.symm

@[simp]
private theorem yMulticast_loc_0 : yMulticast.loc 0 = 2 := rfl

@[simp]
private theorem yMulticast_loc_1 : yMulticast.loc 1 = 2 := rfl

@[simp]
private theorem yMulticast_loc_2 : yMulticast.loc 2 = 3 := rfl

@[simp]
private theorem yTree_anc_zero (w : Fin 4) : yTree.IsAncestor 0 w :=
  yTree.isAncestor_root w

@[simp]
private theorem yTree_anc_one_loc (j : Fin 3) : yTree.IsAncestor 1 (yMulticast.loc j) := by
  fin_cases j <;> exact ⟨1, rfl⟩

@[simp]
private theorem yTree_anc_two_loc (j : Fin 3) :
    yTree.IsAncestor 2 (yMulticast.loc j) ↔ j = 0 ∨ j = 1 := by
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · simp [yTree.isAncestor_refl]
  · simp [yTree.isAncestor_refl]
  · simp [yTree_not_anc 2 3 (by decide) (by decide) (by decide)]

@[simp]
private theorem yTree_anc_three_loc (j : Fin 3) :
    yTree.IsAncestor 3 (yMulticast.loc j) ↔ j = 2 := by
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · simp [yTree_not_anc 3 2 (by decide) (by decide) (by decide)]
  · simp [yTree_not_anc 3 2 (by decide) (by decide) (by decide)]
  · simp [yTree.isAncestor_refl]

example :
    yMulticast.toCostSharingGame.IsNonneg ∧
    yMulticast.toCostSharingGame.IsSubmodular ∧
    yMulticast.toCostSharingGame =
      ∑ v : Fin 4,
        orGame (Finset.univ.filter fun i : Fin 3 => yTree.IsAncestor v (yMulticast.loc i))
          (yMulticast.edgeCost v) :=
  ⟨yMulticast.toCostSharingGame_isNonneg,
   yMulticast.toCostSharingGame_isSubmodular,
   yMulticast.toCostSharingGame_eq_sum_orGame⟩

theorem yMulticast_cost_univ :
    yMulticast.toCostSharingGame.cost Finset.univ = 10 := by
  rw [yMulticast.toCostSharingGame_cost_eq_sum, Fin.sum_univ_four]
  simp only [yMulticast_tree, Finset.mem_univ, true_and, yTree_anc_zero, yTree_anc_one_loc,
    yTree_anc_two_loc, yTree_anc_three_loc]
  have h2 : ∃ i : Fin 3, i = 0 ∨ i = 1 := ⟨0, Or.inl rfl⟩
  simp [h2, yMulticast]
  norm_num

/-- Grand-coalition Shapley shares on `yMulticast` are `![3, 3, 4]` (`6/3 + 2/2 = 3` for receivers
`0, 1` and `6/3 + 2/1 = 4` for receiver `2`), and lie in the exact core. -/
theorem yMulticast_shShare_univ :
    yMulticast.shShare Finset.univ = ![3, 3, 4] := by
  funext i
  rw [yMulticast.shShare_apply]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_filter, Fin.sum_univ_four]
  simp only [yMulticast_tree, yTree_anc_zero, yTree_anc_one_loc, yTree_anc_two_loc,
    yTree_anc_three_loc]
  have hc1 : (Finset.univ.filter fun _ : Fin 3 => True).card = 3 := by decide
  have hc2 : (Finset.univ.filter fun j : Fin 3 => j = 0 ∨ j = 1).card = 2 := by decide
  have hc3 : (Finset.univ.filter fun j : Fin 3 => j = 2).card = 1 := by decide
  rw [hc1, hc2, hc3]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    simp [yMulticast] <;> norm_num

example :
    yMulticast.toCostSharingGame.shapleyScheme.share Finset.univ = ![3, 3, 4] ∧
    yMulticast.toCostSharingGame.InCore ![3, 3, 4] ∧
    yMulticast.shMechanism.IsGroupStrategyproof ∧
    yMulticast.shMechanism.IsBudgetBalanced yMulticast.toCostSharingGame 1 ∧
    yMulticast.shMechanism.NoPositiveTransfers ∧
    yMulticast.shMechanism.VoluntaryParticipation ∧
    yMulticast.shMechanism.ConsumerSovereignty := by
  have hsh : yMulticast.shScheme.share Finset.univ = ![3, 3, 4] := by
    ext i
    rw [yMulticast.shScheme_share, yMulticast_shShare_univ]
  refine ⟨?_, hsh ▸ yMulticast.shScheme_inCore_univ,
    yMulticast.shMechanism_isGroupStrategyproof,
    yMulticast.shMechanism_isBudgetBalanced,
    yMulticast.shMechanism_noPositiveTransfers,
    yMulticast.shMechanism_voluntaryParticipation,
    yMulticast.shMechanism_consumerSovereignty⟩
  ext i
  rw [yMulticast.shapleyScheme_share_eq_shShare, yMulticast_shShare_univ]

/-- Concrete behavioral separation on `yMulticast` under bid profile `b = ![4, 4, 3]`:
- `2`-pass `MC` (`twoPassReceivers`, `twoPassPayment`, `mcMechanism`) serves `{0, 1, 2}` and
  charges `![3, 3, 2]` (total `8 < 10`, strict deficit, net welfare `1`);
- `SH` (`shMechanism`) prunes receiver `2` and serves `{0, 1}` with payments `![4, 4, 0]`. -/
example :
    let b : Fin 3 → ℝ := ![4, 4, 3]
    yMulticast.nodeWelfare b 0 = 1 ∧
    yMulticast.maxNetWelfare b = 1 ∧
    yMulticast.twoPassReceivers b = Finset.univ ∧
    yMulticast.mcMechanism.serviced b = Finset.univ ∧
    yMulticast.twoPassPayment b = ![3, 3, 2] ∧
    yMulticast.mcMechanism.payment b = ![3, 3, 2] ∧
    ∑ i ∈ yMulticast.mcMechanism.serviced b, yMulticast.mcMechanism.payment b i <
      yMulticast.toCostSharingGame.cost (yMulticast.mcMechanism.serviced b) ∧
    yMulticast.shMechanism.serviced b = {0, 1} ∧
    yMulticast.shMechanism.payment b = ![4, 4, 0] := by
  intro b
  have hb : ∀ i, 0 ≤ b i := fun i => by fin_cases i <;> norm_num [b]
  have hchildren0 : yMulticast.tree.children 0 = {1} := by
    ext c; fin_cases c <;> simp [yTree]
  have hchildren1 : yMulticast.tree.children 1 = {2, 3} := by
    ext c; fin_cases c <;> simp [yTree]
  have hchildren2 : yMulticast.tree.children 2 = ∅ := by
    ext c; fin_cases c <;> simp [yTree]
  have hchildren3 : yMulticast.tree.children 3 = ∅ := by
    ext c; fin_cases c <;> simp [yTree]
  have hloc0 : (Finset.univ.filter fun i : Fin 3 => yMulticast.loc i = 0) = ∅ := by decide
  have hloc1 : (Finset.univ.filter fun i : Fin 3 => yMulticast.loc i = 1) = ∅ := by decide
  have hloc2 : (Finset.univ.filter fun i : Fin 3 => yMulticast.loc i = 2) = {0, 1} := by decide
  have hloc3 : (Finset.univ.filter fun i : Fin 3 => yMulticast.loc i = 3) = {2} := by decide
  have hnw2 : yMulticast.nodeWelfare b 2 = 8 := by
    rw [yMulticast.nodeWelfare_eq, hloc2, hchildren2]
    norm_num [b]
  have hnw3 : yMulticast.nodeWelfare b 3 = 3 := by
    rw [yMulticast.nodeWelfare_eq, hloc3, hchildren3]
    norm_num [b]
  have hsurp2 : yMulticast.subtreeSurplus b 2 = 6 := by
    rw [yMulticast.subtreeSurplus_eq, hnw2]
    norm_num [yMulticast]
  have hsurp3 : yMulticast.subtreeSurplus b 3 = 1 := by
    rw [yMulticast.subtreeSurplus_eq, hnw3]
    norm_num [yMulticast]
  have hnw1 : yMulticast.nodeWelfare b 1 = 7 := by
    rw [yMulticast.nodeWelfare_eq, hloc1, hchildren1]
    simp only [Finset.sum_empty, zero_add,
      Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3),
      yMulticast.upMsg_eq, hsurp2, hsurp3]
    norm_num
  have hsurp1 : yMulticast.subtreeSurplus b 1 = 1 := by
    rw [yMulticast.subtreeSurplus_eq, hnw1]
    norm_num [yMulticast]
  have hnw0 : yMulticast.nodeWelfare b 0 = 1 := by
    rw [yMulticast.nodeWelfare_eq, hloc0, hchildren0]
    simp only [Finset.sum_empty, zero_add, Finset.sum_singleton, yMulticast.upMsg_eq, hsurp1]
    norm_num
  have hmax : yMulticast.maxNetWelfare b = 1 := by
    rw [← yMulticast.nodeWelfare_root_eq_maxNetWelfare hb]
    exact hnw0
  have hroot_act : yMulticast.topDownActive b 0 = true := yMulticast.topDownActive_root b
  have hact1 : yMulticast.topDownActive b 1 = true := by
    rw [yMulticast.topDownActive_of_ne_root b (by decide)]
    change (yMulticast.topDownActive b 0 && decide (0 ≤ yMulticast.subtreeSurplus b 1)) = true
    rw [hroot_act, hsurp1]
    norm_num
  have hact2 : yMulticast.topDownActive b 2 = true := by
    rw [yMulticast.topDownActive_of_ne_root b (by decide)]
    change (yMulticast.topDownActive b 1 && decide (0 ≤ yMulticast.subtreeSurplus b 2)) = true
    rw [hact1, hsurp2]
    norm_num
  have hact3 : yMulticast.topDownActive b 3 = true := by
    rw [yMulticast.topDownActive_of_ne_root b (by decide)]
    change (yMulticast.topDownActive b 1 && decide (0 ≤ yMulticast.subtreeSurplus b 3)) = true
    rw [hact1, hsurp3]
    norm_num
  have htwo_rec : yMulticast.twoPassReceivers b = Finset.univ := by
    ext i
    simp only [MulticastInstance.mem_twoPassReceivers, Finset.mem_univ, iff_true]
    fin_cases i
    · exact hact2
    · exact hact2
    · exact hact3
  have hmc_rec : yMulticast.mcMechanism.serviced b = Finset.univ := by
    rw [yMulticast.mcMechanism_serviced, ← yMulticast.twoPassReceivers_eq_mcReceivers hb, htwo_rec]
  have hroot_th : yMulticast.topDownThreshold b 0 = none := yMulticast.topDownThreshold_root b
  have hth1 : yMulticast.topDownThreshold b 1 = some 1 := by
    rw [yMulticast.topDownThreshold_of_ne_root b (by decide)]
    change (match yMulticast.topDownThreshold b 0 with
      | none => some (yMulticast.subtreeSurplus b 1)
      | some m => some (min m (yMulticast.subtreeSurplus b 1))) = some 1
    rw [hroot_th, hsurp1]
  have hth2 : yMulticast.topDownThreshold b 2 = some 1 := by
    rw [yMulticast.topDownThreshold_of_ne_root b (by decide)]
    change (match yMulticast.topDownThreshold b 1 with
      | none => some (yMulticast.subtreeSurplus b 2)
      | some m => some (min m (yMulticast.subtreeSurplus b 2))) = some 1
    rw [hth1, hsurp2]
    norm_num
  have hth3 : yMulticast.topDownThreshold b 3 = some 1 := by
    rw [yMulticast.topDownThreshold_of_ne_root b (by decide)]
    change (match yMulticast.topDownThreshold b 1 with
      | none => some (yMulticast.subtreeSurplus b 3)
      | some m => some (min m (yMulticast.subtreeSurplus b 3))) = some 1
    rw [hth1, hsurp3]
    norm_num
  have htwo_pay : yMulticast.twoPassPayment b = ![3, 3, 2] := by
    funext i
    rw [yMulticast.twoPassPayment_eq]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · rw [yMulticast_loc_0, hact2, hth2]; norm_num [b]
    · rw [yMulticast_loc_1, hact2, hth2]; norm_num [b]
    · rw [yMulticast_loc_2, hact3, hth3]; norm_num [b]
  have hmc_pay : yMulticast.mcMechanism.payment b = ![3, 3, 2] := by
    funext i
    rw [← yMulticast.twoPassPayment_eq_mcMechanism_payment hb i, htwo_pay]
  have hdeficit : ∑ i ∈ yMulticast.mcMechanism.serviced b, yMulticast.mcMechanism.payment b i <
      yMulticast.toCostSharingGame.cost (yMulticast.mcMechanism.serviced b) := by
    rw [hmc_rec, hmc_pay, yMulticast_cost_univ, Fin.sum_univ_three]
    norm_num
  -- Now verify `SH` (`shMechanism`) on the same bid profile `b = ![4, 4, 3]`:
  have hc_p1 : (({0, 1} : Finset (Fin 3)).filter fun _ => True).card = 2 := by decide
  have hc_p2 : (({0, 1} : Finset (Fin 3)).filter fun j => j = 0 ∨ j = 1).card = 2 := by decide
  have hsh_pair : yMulticast.shShare ({0, 1} : Finset (Fin 3)) = ![4, 4, 0] := by
    funext i
    rw [yMulticast.shShare_apply]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · have hmem : (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
      simp only [hmem, ↓reduceIte]
      rw [Finset.sum_filter, Fin.sum_univ_four]
      simp only [yMulticast_tree, yTree_anc_zero, yTree_anc_one_loc, yTree_anc_two_loc,
        yTree_anc_three_loc]
      rw [hc_p1, hc_p2]
      simp [yMulticast]
      norm_num
    · have hmem : (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
      simp only [hmem, ↓reduceIte]
      rw [Finset.sum_filter, Fin.sum_univ_four]
      simp only [yMulticast_tree, yTree_anc_zero, yTree_anc_one_loc, yTree_anc_two_loc,
        yTree_anc_three_loc]
      rw [hc_p1, hc_p2]
      simp [yMulticast]
      norm_num
    · have hnot : (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) := by decide
      simp [hnot]
  have hsh_serv : yMulticast.shMechanism.serviced b = {0, 1} := by
    rw [yMulticast.shMechanism_serviced]
    have hgreat := yMulticast.shScheme.isGreatest_isWilling_moulinServiced
      yMulticast.shScheme_isCrossMonotone b
    have hw_pair : yMulticast.shScheme.IsWilling b ({0, 1} : Finset (Fin 3)) := by
      intro i hi
      rw [yMulticast.shScheme_share, hsh_pair]
      fin_cases i <;> simp at hi <;> norm_num [b]
    have hsub_pair : ({0, 1} : Finset (Fin 3)) ⊆ yMulticast.shScheme.moulinServiced b :=
      hgreat.2 hw_pair
    refine le_antisymm ?_ hsub_pair
    intro i hi
    by_contra hnot
    have hi2 : i = 2 := by fin_cases i <;> simp_all
    subst hi2
    have huniv : yMulticast.shScheme.moulinServiced b = Finset.univ := by
      ext j
      simp only [Finset.mem_univ, iff_true]
      fin_cases j
      · exact hsub_pair (by decide)
      · exact hsub_pair (by decide)
      · exact hi
    have hw2 := hgreat.1 2 hi
    rw [huniv, yMulticast.shScheme_share, yMulticast_shShare_univ] at hw2
    norm_num [b] at hw2
  have hsh_pay : yMulticast.shMechanism.payment b = ![4, 4, 0] := by
    funext i
    rw [yMulticast.shMechanism_payment, ← yMulticast.shMechanism_serviced, hsh_serv, hsh_pair]
  exact ⟨hnw0, hmax, htwo_rec, hmc_rec, htwo_pay, hmc_pay, hdeficit, hsh_serv, hsh_pay⟩

example :
    yMulticast.mcMechanism.toSingleParameterMechanism.IsDSIC ∧
    yMulticast.mcMechanism.VoluntaryParticipation ∧
    yMulticast.mcMechanism.NoPositiveTransfers ∧
    ∀ b : Fin 3 → ℝ,
      ∑ i ∈ yMulticast.mcMechanism.serviced b, yMulticast.mcMechanism.payment b i ≤
        yMulticast.toCostSharingGame.cost (yMulticast.mcMechanism.serviced b) :=
  ⟨yMulticast.mcMechanism_isDSIC,
   yMulticast.mcMechanism_voluntaryParticipation,
   yMulticast.mcMechanism_noPositiveTransfers,
   yMulticast.mcMechanism_payment_sum_le_cost⟩

/-! ## 2. Single-link separations, impossibility, `(H_n - 1) C` tightness, and boundaries -/

/-- On `singleLinkMulticast (Fin 2) 6`, `shMechanism` is group-strategyproof while `mcMechanism`
is NOT group-strategyproof. -/
example :
    (singleLinkMulticast (Fin 2) 6 (by norm_num)).shMechanism.IsGroupStrategyproof ∧
    ¬ (singleLinkMulticast (Fin 2) 6 (by norm_num)).mcMechanism.IsGroupStrategyproof :=
  ⟨(singleLinkMulticast (Fin 2) 6 (by norm_num)).shMechanism_isGroupStrategyproof,
   not_mcMechanism_isGroupStrategyproof_singleLink (by decide) (by norm_num)⟩

/-- Concrete impossibility instance on `Fin 2` with link cost `C = 12`. -/
example :
    ¬ ∃ M : CostSharingMechanism (Fin 2),
      M.toSingleParameterMechanism.IsDSIC ∧
      M.VoluntaryParticipation ∧
      M.NoPositiveTransfers ∧
      M.IsBudgetBalanced (singleLinkMulticast (Fin 2) 12 (by norm_num)).toCostSharingGame 1 ∧
      ∀ b : Fin 2 → ℝ, (∀ k, 0 ≤ b k) →
        (singleLinkMulticast (Fin 2) 12 (by norm_num)).IsWelfareMaximizingSet b (M.serviced b) :=
  not_exists_dsic_budgetBalanced_welfareMaximizing_singleLink (by decide) (by norm_num)

/-- Concrete `Fin 3` (`n = 3`, `H_3 = 11 / 6`, `(H_3 - 1) * 6 = 5`) upper and lower welfare-loss
witnesses for `singleLinkMulticast (Fin 3) 6`. -/
example :
    let I := singleLinkMulticast (Fin 3) 6 (by norm_num)
    (∀ (b : Fin 3 → ℝ), (∀ i, 0 ≤ b i) → ∀ R : Finset (Fin 3),
      I.netWelfare b R - I.netWelfare b (I.shMechanism.serviced b) ≤ 5) ∧
    (∃ b : Fin 3 → ℝ, (∀ i, 0 ≤ b i) ∧
      49 / 10 < I.netWelfare b Finset.univ - I.netWelfare b (I.shMechanism.serviced b)) := by
  intro I
  have hh3 : ((harmonic (Fintype.card (Fin 3)) : ℝ) - 1) * 6 = 5 := by
    rw [Fintype.card_fin]
    norm_num [harmonic, Finset.sum_range_succ]
  refine ⟨fun b hb R => ?_, ?_⟩
  · have h := netWelfare_sub_shMechanism_le_harmonic_sub_one (A := Fin 3)
      (by norm_num : (0 : ℝ) ≤ 6) hb R
    dsimp only at h
    rwa [hh3] at h
  · obtain ⟨b, hb, hgt⟩ := exists_welfareLoss_gt_harmonic_sub_one (A := Fin 3)
      (by norm_num : (0 : ℝ) < 6) I.shScheme_isBudgetBalanced I.shScheme_isCrossMonotone
      (ε := 1 / 10) (by norm_num)
    refine ⟨b, hb, ?_⟩
    rw [hh3] at hgt
    rw [I.shMechanism_serviced, ← I.shScheme.moulinMechanism_serviced]
    linarith

/-- **Boundary case `|A| = 1` (`Fin 1`)**: `H_1 - 1 = 0`, so `shMechanism` incurs **zero** welfare
loss on every nonnegative bid profile (it is fully welfare-maximizing!). -/
example (C : ℝ) (hC : 0 ≤ C) (b : Fin 1 → ℝ) (hb : ∀ i, 0 ≤ b i) (R : Finset (Fin 1)) :
    let I := singleLinkMulticast (Fin 1) C hC
    I.netWelfare b R ≤ I.netWelfare b (I.shMechanism.serviced b) := by
  intro I
  have h := netWelfare_sub_shMechanism_le_harmonic_sub_one (A := Fin 1) hC hb R
  have hh1 : ((harmonic (Fintype.card (Fin 1)) : ℝ) - 1) * C = 0 := by
    rw [Fintype.card_fin]
    norm_num [harmonic]
  dsimp only at h
  linarith

/-- **Boundary case `C = 0`**: on a zero-cost link, `shMechanism` incurs zero welfare loss for
arbitrary finite nonempty `A`. -/
example (b : Fin 4 → ℝ) (hb : ∀ i, 0 ≤ b i) (R : Finset (Fin 4)) :
    let I := singleLinkMulticast (Fin 4) 0 le_rfl
    I.netWelfare b R ≤ I.netWelfare b (I.shMechanism.serviced b) := by
  intro I
  have h := netWelfare_sub_shMechanism_le_harmonic_sub_one (A := Fin 4) le_rfl hb R
  dsimp only at h
  linarith

/-! ## 3. Path cut communication lower bound witnesses (`pathMulticast 3`) -/

/-- Concrete witnesses on the `5`-node path multicast tree `pathMulticast 3`:
- distinct active spine patterns `x₀ ≠ x₁` induce distinct bottom Shapley shares;
- Bob's bottom receiver is served on `(x, x)` and excluded on one of `(x₀, x₁)`, `(x₁, x₀)`;
- every deterministic two-party protocol across the bottom cut link uses at least `4` bits. -/
example :
    let x₀ : Cslib.BitString 3 := fun _ => false
    let x₁ : Cslib.BitString 3 := fun _ => true
    pathBottomShare 3 x₀ ≠ pathBottomShare 3 x₁ ∧
    Sum.inr () ∈ (pathMulticast 3).shMechanism.serviced (pathBidProfile 3 x₁ x₁) ∧
    (4 : ℕ∞) ≤ Cslib.Communication.Protocol.ecomplexityFun
      (fun x y : Cslib.BitString 3 =>
        decide (Sum.inr () ∈ (pathMulticast 3).shMechanism.serviced (pathBidProfile 3 x y))) := by
  intro x₀ x₁
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have hfun := pathBottomShare_injective 3 h
    have h0 := congrFun hfun 0
    simp [x₀, x₁] at h0
  · rw [mem_pathMulticast_shMechanism_serviced_iff]
  · have h := le_ecomplexityFun_pathMulticast_shServiced (k := 3) (by omega)
    norm_num at h
    exact h

end CslibFrontierTests.GameTheory.MulticastCostSharing
