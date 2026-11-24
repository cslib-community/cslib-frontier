/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.UtilityGame.Basic
public import CslibFrontier.GameTheory.UtilityGame.CompetitiveFacilityLocation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked instances and boundary witnesses for utility games and facility location

Module-isolated client tests exercising `CslibFrontier.GameTheory.UtilityGame.Basic` and
`CslibFrontier.GameTheory.UtilityGame.CompetitiveFacilityLocation` without unfolding unexposed
definitions:

1. **Bertrand competition / co-location boundary (`bertrandTieGame`):** two providers open at the
   same shared zero-cost location (`s = fun _ => ()`), driving `secondPrice` and both providers'
   profits to `0` while keeping social welfare at `10`, and confirming that `profileWithout` drops
   only one provider (`socialWelfare (profileWithout s 0) = 10`).
2. **Competitive facility location `PoA = 2` tightness (`twoClientFL`):** concrete 2-provider,
   2-client game checked via public API (`secondPrice_eq_inf'`, `socialWelfare_eq_sum_sub_inf'`,
   `isExactPotential`, `isBasic_toUtilityGame`, pure and mixed `PoA ≤ 2`, and random best-response
   `expectedWalkValue` at `t = 1`).
3. **Non-basic monotone valid utility game (`neighborhoodGame` on `⊤`):** 2 players co-located on
   `K_2` satisfy `IsValid` and `Monotone` while refuting `IsBasic` (`utility = 1 ≠ 0` marginal
   gain).
4. **Negative monotonicity witness (`nonMonotoneBase`):** competitive facility location with opening
   cost `f(0, false) = 9` on client value `10` satisfies `IsBasic` (and `IsValid`) while refuting
   `Monotone` and refuting `PoA ≤ 2` (`V_f(![false, false]) = 1` at a pure Nash equilibrium vs.
   `V_f(![true, true]) = 10 > 2 * 1`), while still satisfying Exercise 19.17(b)'s
   `V_f(o) ≤ 2 * V_f(s) + F` (`10 ≤ 2 * 1 + 9 = 11`).
-/

public section

namespace CslibFrontierTests.GameTheory.UtilityGame

open Cslib.GameTheory
open Cslib.GameTheory.UtilityGame

/-! ### 1. Co-location / Bertrand tie boundary -/

/-- Two providers sharing an identical zero-cost facility serving one client of value `10`. -/
def bertrandTieGame : CompetitiveFacilityLocation (Fin 2) (fun _ => Unit) Unit where
  value _ := 10
  serviceCost _ _ _ := 0

/-- At co-location, `secondPrice` equals `0` (not `value = 10`), so both providers earn `0` profit
while social welfare is `10`. -/
example :
    bertrandTieGame.secondPrice () (fun _ => ()) 0 = 0 ∧
    bertrandTieGame.profit 0 (fun _ => ()) = 0 ∧
    bertrandTieGame.socialWelfare (profileSet (fun _ : Fin 2 => ())) = 10 := by
  have hsec : bertrandTieGame.secondPrice () (fun _ => ()) 0 = 0 := by
    have hne : (Finset.univ.erase (0 : Fin 2)).Nonempty := ⟨1, by decide⟩
    rw [bertrandTieGame.secondPrice_eq_inf' () _ 0 hne (fun _ _ => by norm_num [bertrandTieGame])]
    have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
    simp only [herase, Finset.inf'_singleton, bertrandTieGame]
  refine ⟨hsec, ?_, ?_⟩
  · rw [bertrandTieGame.profit_def, Fintype.sum_unique, bertrandTieGame.clientProfit_def, hsec]
    norm_num [bertrandTieGame]
  · rw [bertrandTieGame.socialWelfare_eq_sum_sub_inf' _
      (fun _ _ _ => by norm_num [bertrandTieGame]), Fintype.sum_unique]
    have hinf : (Finset.univ.inf' Finset.univ_nonempty fun i : Fin 2 =>
        bertrandTieGame.serviceCost () i ()) = 0 := by
      simp only [bertrandTieGame, Finset.inf'_const]
    rw [hinf]
    norm_num [bertrandTieGame]

/-- Dropping provider `0` from the co-located profile leaves provider `1` active, keeping social
welfare at `10` (demonstrating why `profileWithout` operates on `Σ i, S i`). -/
example :
    bertrandTieGame.socialWelfare (profileWithout (fun _ : Fin 2 => ()) 0) = 10 := by
  have hp := bertrandTieGame.isBasic_toUtilityGame.utility_eq_marginal 0 (fun _ => ())
  simp only [CompetitiveFacilityLocation.toUtilityGame_utility,
    CompetitiveFacilityLocation.toUtilityGame_profileValue,
    CompetitiveFacilityLocation.toUtilityGame_socialValue] at hp
  have hprof : bertrandTieGame.profit 0 (fun _ => ()) = 0 := by
    rw [bertrandTieGame.profit_def, Fintype.sum_unique, bertrandTieGame.clientProfit_def]
    have hne : (Finset.univ.erase (0 : Fin 2)).Nonempty := ⟨1, by decide⟩
    rw [bertrandTieGame.secondPrice_eq_inf' () _ 0 hne (fun _ _ => by norm_num [bertrandTieGame])]
    have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
    simp only [herase, Finset.inf'_singleton, bertrandTieGame, sub_self, max_self]
  have hsw : bertrandTieGame.socialWelfare (profileSet (fun _ : Fin 2 => ())) = 10 := by
    rw [bertrandTieGame.socialWelfare_eq_sum_sub_inf' _
      (fun _ _ _ => by norm_num [bertrandTieGame]), Fintype.sum_unique]
    simp only [bertrandTieGame, Finset.inf'_const, sub_zero]
  linarith

/-! ### 2. Concrete 2-provider, 2-client instance attaining `PoA = 2` -/

/-- Two-provider, two-client facility location game with pure Nash equilibrium `![false, false]`
(welfare `1`) and social optimum `![true, true]` (welfare `2`). -/
def twoClientFL : CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) (Fin 2) where
  value _ := 1
  serviceCost j i b :=
    match j, i, b with
    | 0, 0, false => 0
    | 0, 1, true => 0
    | 1, 0, true => 0
    | _, _, _ => 1

private theorem twoClientFL_cost_le :
    ∀ j i b, twoClientFL.serviceCost j i b ≤ twoClientFL.value j := by
  intro j i b
  fin_cases j <;> fin_cases i <;> cases b <;> norm_num [twoClientFL]

private theorem inf'_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_univ 0)) (Finset.inf'_le _ (Finset.mem_univ 1))
  · refine Finset.le_inf' Finset.univ_nonempty _ fun i _ => ?_
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _

private theorem twoClientFL_welfare (b₀ b₁ : Bool) :
    twoClientFL.socialWelfare (profileSet ![b₀, b₁]) =
      (if !b₀ || b₁ then 1 else 0) + (if b₀ then 1 else 0) := by
  rw [twoClientFL.socialWelfare_eq_sum_sub_inf' _ twoClientFL_cost_le, Fin.sum_univ_two,
    inf'_fin_two, inf'_fin_two]
  cases b₀ <;> cases b₁ <;> norm_num [twoClientFL]

theorem twoClientFL_false_isPureNash : twoClientFL.toCostGame.IsPureNash ![false, false] := by
  intro i b
  have hpot := twoClientFL.isExactPotential ![false, false] i b
  have h0 : twoClientFL.socialWelfare (profileSet ![false, false]) = 1 := by
    rw [twoClientFL_welfare]; norm_num
  have hupd :
      twoClientFL.socialWelfare (profileSet (Function.update ![false, false] i b)) ≤ 1 := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> cases b
    · have heq : Function.update ![false, false] 0 false = ![false, false] := by
        ext k; fin_cases k <;> rfl
      rw [heq, h0]
    · have heq : Function.update ![false, false] 0 true = ![true, false] := by
        ext k; fin_cases k <;> rfl
      rw [heq, twoClientFL_welfare]; norm_num
    · have heq : Function.update ![false, false] 1 false = ![false, false] := by
        ext k; fin_cases k <;> rfl
      rw [heq, h0]
    · have heq : Function.update ![false, false] 1 true = ![false, true] := by
        ext k; fin_cases k <;> rfl
      rw [heq, twoClientFL_welfare]; norm_num
  linarith

/-- Check exact `PoA = 2` (`V(o) = 2 * V(s)`), exact potential, and mixed Nash `PoA ≤ 2` via point
masses. -/
example :
    twoClientFL.toCostGame.IsExactPotential (fun s => -twoClientFL.socialWelfare (profileSet s)) ∧
    twoClientFL.socialWelfare (profileSet ![true, true]) =
      2 * twoClientFL.socialWelfare (profileSet ![false, false]) ∧
    twoClientFL.socialWelfare (profileSet ![true, true]) ≤
      2 * ∑ s, productWeight (fun i : Fin 2 => Pi.single (![false, false] i) (1 : ℝ)) s *
        twoClientFL.socialWelfare (profileSet s) := by
  refine ⟨twoClientFL.isExactPotential, ?_, ?_⟩
  · rw [twoClientFL_welfare, twoClientFL_welfare]; norm_num
  · exact twoClientFL.socialWelfare_le_two_mul_expected_of_isMixedNash
      twoClientFL_false_isPureNash.isMixedNash ![true, true]

/-- Check `exists_isBestResponse`, `expectedWalkValue`, and `profileValue_le_expected_step_gain`
through the module-isolated `toUtilityGame` interface. -/
example :
    ∃ br, twoClientFL.toUtilityGame.IsBestResponse br ∧
      (twoClientFL.toUtilityGame.profileValue ![true, true] -
        2 * twoClientFL.toUtilityGame.profileValue ![false, false]) / 2 ≤
        twoClientFL.toUtilityGame.expectedWalkValue br ![false, false] 1 -
          twoClientFL.toUtilityGame.profileValue ![false, false] := by
  obtain ⟨br, hbr⟩ := twoClientFL.toUtilityGame.exists_isBestResponse
  refine ⟨br, hbr, ?_⟩
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    twoClientFL.isBasic_toUtilityGame.profileValue_le_expected_step_gain
      twoClientFL.monotone_toUtilityGame_socialValue hbr ![false, false] ![true, true]

/-! ### 3. Non-basic monotone valid utility game (`neighborhoodGame` on `K_2`) -/

/-- On `K_2` (`⊤ : SimpleGraph (Fin 2)`), `neighborhoodGame` is `IsValid` and `Monotone`, but NOT
`IsBasic`: when both players locate at `0`, player `0` receives wealth `1/2 + 1/2 = 1`, whereas
dropping player `0` leaves both vertices covered by player `1` (`marginal = 2 - 2 = 0`). -/
example :
    (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).IsValid ∧
    Monotone (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).socialValue ∧
    ¬ (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).IsBasic := by
  refine ⟨isValid_neighborhoodGame (Fin 2) ⊤, monotone_neighborhoodGame_socialValue (Fin 2) ⊤, ?_⟩
  intro hbasic
  have hmarg := hbasic.utility_eq_marginal 0 (fun _ => 0)
  have hnhd : ∀ u : Fin 2, closedNeighborhood (⊤ : SimpleGraph (Fin 2)) u = Finset.univ := by
    intro u
    ext v
    simp only [mem_closedNeighborhood, SimpleGraph.top_adj, Finset.mem_univ, iff_true]
    by_cases h : v = u
    · exact Or.inl h
    · exact Or.inr (Ne.symm h)
  have hutil : (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).utility 0 (fun _ => 0) = 1 := by
    rw [neighborhoodGame_utility_apply, hnhd 0, Fin.sum_univ_two, hnhd 0, hnhd 1]
    norm_num
  have hfull : (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).profileValue (fun _ => 0) =
      2 := by
    rw [profileValue_def, neighborhoodGame_socialValue_apply]
    have hbi : (profileSet (S := fun _ : Fin 2 => Fin 2) (fun _ => 0)).biUnion
        (fun x => closedNeighborhood (⊤ : SimpleGraph (Fin 2)) x.2) = Finset.univ := by
      ext v
      simp only [Finset.mem_biUnion, mem_profileSet, Finset.mem_univ, iff_true]
      exact ⟨⟨0, 0⟩, rfl, by rw [hnhd 0]; exact Finset.mem_univ v⟩
    rw [hbi]
    norm_num
  have hwithout :
      (neighborhoodGame (Fin 2) (⊤ : SimpleGraph (Fin 2))).socialValue
        (profileWithout (S := fun _ : Fin 2 => Fin 2) (fun _ => 0) 0) = 2 := by
    rw [neighborhoodGame_socialValue_apply]
    have hbi : (profileWithout (S := fun _ : Fin 2 => Fin 2) (fun _ => 0) 0).biUnion
        (fun x => closedNeighborhood (⊤ : SimpleGraph (Fin 2)) x.2) = Finset.univ := by
      ext v
      simp only [Finset.mem_biUnion, mem_profileWithout, Finset.mem_univ, iff_true]
      exact ⟨⟨1, 0⟩, ⟨by decide, rfl⟩, by rw [hnhd 0]; exact Finset.mem_univ v⟩
    rw [hbi]
    norm_num
  linarith

/-! ### 4. Negative witness: non-monotone basic utility game violating `PoA ≤ 2` -/

/-- Facility location instance with opening costs (`f(0, false) = 9`) that is `IsBasic` (hence
`IsValid`) but NOT `Monotone`, and whose pure Nash equilibrium `![false, false]` has net welfare `1`
against optimal net welfare `10 > 2 * 1`. -/
def nonMonotoneBase : CompetitiveFacilityLocation (Fin 2) (fun _ => Bool) Unit where
  value _ := 10
  serviceCost _ i b :=
    match i, b with
    | 0, false => 0
    | 1, true => 0
    | _, _ => 10

def nonMonotoneFee (i : Fin 2) (b : Bool) : ℝ :=
  match i, b with
  | 0, false => 9
  | _, _ => 0

example :
    (nonMonotoneBase.withOpeningCost nonMonotoneFee).IsBasic ∧
    ¬ Monotone (nonMonotoneBase.withOpeningCost nonMonotoneFee).socialValue ∧
    (∃ s o : Fin 2 → Bool,
      (nonMonotoneBase.withOpeningCost nonMonotoneFee).toCostGame.IsPureNash s ∧
      0 < (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue s ∧
      2 * (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue s <
        (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue o ∧
      (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue o ≤
        2 * (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue s +
          ∑ i, nonMonotoneFee i (s i)) := by
  refine ⟨nonMonotoneBase.isBasic_withOpeningCost nonMonotoneFee, ?_, ?_⟩
  · intro hmono
    have hsub : ({⟨(1 : Fin 2), true⟩} : Finset (Σ _ : Fin 2, Bool)) ⊆
        profileSet ![false, true] := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [mem_profileSet]
      rfl
    have hle' := hmono hsub
    have h1 : (nonMonotoneBase.withOpeningCost nonMonotoneFee).socialValue
        {⟨(1 : Fin 2), true⟩} = 10 := by
      rw [CompetitiveFacilityLocation.withOpeningCost_socialValue,
        nonMonotoneBase.socialWelfare_def, Fintype.sum_unique,
        nonMonotoneBase.clientSurplus_singleton, Finset.sum_singleton]
      norm_num [nonMonotoneBase, nonMonotoneFee]
    have h2 : (nonMonotoneBase.withOpeningCost nonMonotoneFee).socialValue
        (profileSet ![false, true]) = 1 := by
      rw [← profileValue_def, CompetitiveFacilityLocation.withOpeningCost_profileValue,
        nonMonotoneBase.socialWelfare_eq_sum_sub_inf' _
          (fun _ i b => by fin_cases i <;> cases b <;> norm_num [nonMonotoneBase]),
        Fintype.sum_unique, Fin.sum_univ_two, inf'_fin_two]
      norm_num [nonMonotoneBase, nonMonotoneFee]
    linarith
  · have hval : ∀ b₀ b₁ : Bool,
        (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue ![b₀, b₁] =
          (if !b₀ || b₁ then 10 else 0) - (if !b₀ then 9 else 0) := by
      intro b₀ b₁
      rw [CompetitiveFacilityLocation.withOpeningCost_profileValue,
        nonMonotoneBase.socialWelfare_eq_sum_sub_inf' _
          (fun _ i b => by fin_cases i <;> cases b <;> norm_num [nonMonotoneBase]),
        Fintype.sum_unique, Fin.sum_univ_two, inf'_fin_two]
      cases b₀ <;> cases b₁ <;> norm_num [nonMonotoneBase, nonMonotoneFee]
    have hs_ne : (nonMonotoneBase.withOpeningCost nonMonotoneFee).toCostGame.IsPureNash
        ![false, false] := by
      intro i b
      have hpot := (nonMonotoneBase.isBasic_withOpeningCost nonMonotoneFee).isExactPotential
        ![false, false] i b
      have h0 : (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue ![false, false] =
          1 := by
        rw [hval]; norm_num
      have hupd : (nonMonotoneBase.withOpeningCost nonMonotoneFee).profileValue
          (Function.update ![false, false] i b) ≤ 1 := by
        fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> cases b
        · have heq : Function.update ![false, false] 0 false = ![false, false] := by
            ext k; fin_cases k <;> rfl
          rw [heq, h0]
        · have heq : Function.update ![false, false] 0 true = ![true, false] := by
            ext k; fin_cases k <;> rfl
          rw [heq, hval]; norm_num
        · have heq : Function.update ![false, false] 1 false = ![false, false] := by
            ext k; fin_cases k <;> rfl
          rw [heq, h0]
        · have heq : Function.update ![false, false] 1 true = ![false, true] := by
            ext k; fin_cases k <;> rfl
          rw [heq, hval]; norm_num
      linarith
    refine ⟨![false, false], ![true, true], hs_ne, ?_, ?_,
      nonMonotoneBase.netWelfare_le_two_mul_add_openingCost_of_isPureNash nonMonotoneFee hs_ne
        ![true, true]⟩
    · rw [hval]; norm_num
    · rw [hval, hval]; norm_num

end CslibFrontierTests.GameTheory.UtilityGame
