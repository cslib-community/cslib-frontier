/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.GameTheory.Contract.CombinatorialAgency
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Combinatorial agency tests and witnesses

Checked finite examples for `CslibFrontier.GameTheory.Contract.CombinatorialAgency`:

* Two-agent and three-agent noisy AND technologies (`γ = 1 / 4`, `c = 1`): explicit optimal
  contracts, coalition strong-Nash stability (`isStrongNash_optContract`), coexistence of the
  all-shirking Nash equilibrium, interior cardinality skipping (`andTech_skips_interior`), and
  exact POU values `11 / 3` and `29 / 3` (`andTech_pou_eq`).
* Zero-cost boundary witness (`Exercise 23.6`): with `c = ![1, 0]` on two agents under
  `andTech 2 (1 / 4)`, `optContract` still induces a strong equilibrium (`IsStrongEquilibrium`) for
  `![true, false]`, but NOT a strong Nash equilibrium (`IsStrongNash`).
* Two-agent and three-agent noisy OR technologies (`γ = 1 / 4`, `c = 1`): all team sizes attained
  (`orTech_transitions`, concrete thresholds `v = 5, 50, 500, 3000`), uniform constant bound
  `POU ≤ 2` (`orTech_pou_le_two`), and explicit `19 / 13` lower bound at `n = 2`.
* Anonymous non-convex/non-concave example (`Exercise 23.5`): first-best welfare skips `k = 1`
  everywhere while hidden-action agency strictly prefers `k = 1` at `v = 5`.
-/

namespace CslibFrontierTests.GameTheory.CombinatorialAgency

open Cslib.GameTheory Cslib.GameTheory.Contract

/-! ### Noisy AND witnesses (`γ = 1 / 4`, `c = 1`) -/

/-- Optimal contract, payment, coalition stability, and bad shirking equilibrium for 2-agent AND. -/
example :
    let allTrue : Fin 2 → Bool := fun _ => true
    let allFalse : Fin 2 → Bool := fun _ => false
    (∀ i : Fin 2, optContract (andTech 2 (1 / 4)) (fun _ => 1) allTrue i = 8 / 3) ∧
      optPayment (andTech 2 (1 / 4)) (fun _ => 1) allTrue = 3 ∧
      (contractCostGame (andTech 2 (1 / 4)) (fun _ => 1)
        (optContract (andTech 2 (1 / 4)) (fun _ => 1) allTrue)).IsStrongNash allTrue ∧
      (contractCostGame (andTech 2 (1 / 4)) (fun _ => 1)
        (optContract (andTech 2 (1 / 4)) (fun _ => 1) allTrue)).IsPureNash allFalse := by
  intro allTrue allFalse
  have hmc1 : ∀ i : Fin 2, marginalContrib (andTech 2 (1 / 4)) i allTrue = 3 / 8 := by
    intro i
    have ht : allTrue i = true := rfl
    rw [anon_marginalContrib (t := andTech 2 (1 / 4)) (f := andProb 2 (1 / 4))
      (andTech_eq 2 (1 / 4)) ht]
    have hc : countTrue allTrue = 2 := countTrue_true
    rw [hc]
    norm_num [andProb_eq]
  have hmc0 : ∀ i : Fin 2, marginalContrib (andTech 2 (1 / 4)) i allFalse = 1 / 8 := by
    intro i
    rw [← marginalContrib_update (andTech 2 (1 / 4)) i allFalse true]
    have hupd : Function.update allFalse i true i = true := Function.update_self i true allFalse
    rw [anon_marginalContrib (t := andTech 2 (1 / 4)) (f := andProb 2 (1 / 4))
      (andTech_eq 2 (1 / 4)) hupd]
    have hc1 : countTrue (Function.update allFalse i true) = 1 := by
      have himg :
          Finset.univ.filter
              (fun j : Fin 2 => Function.update allFalse i true j = true) =
            {i} := by
        ext j
        fin_cases i <;> fin_cases j <;> simp [allFalse]
      simp [countTrue_eq, himg]
    rw [hc1]
    norm_num [andProb_eq]
  have hct : countTrue allTrue = 2 := countTrue_true
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have ht : allTrue i = true := rfl
    rw [optContract_of_true _ _ ht, hmc1 i]
    norm_num
  · rw [anon_optPayment (t := andTech 2 (1 / 4)) (f := andProb 2 (1 / 4))
      (andTech_eq 2 (1 / 4)) 1 allTrue,
      hct, and_anonOptPayment (by norm_num) (by norm_num) 1 le_rfl]
    norm_num
  · exact isStrongNash_optContract (andTech 2 (1 / 4)) (fun _ => 1) allTrue
      (isStrictlyMonotone_andTech 2 (by norm_num) (by norm_num)) (fun _ => zero_lt_one)
  · rw [isPureNash_iff_marginalContrib _ _ _ _ fun i => by rw [hmc0 i]; norm_num]
    intro i
    refine ⟨fun h => absurd h (by simp [allFalse]), fun _ => ?_⟩
    have ht : allTrue i = true := rfl
    rw [optContract_of_true _ _ ht, hmc1 i, hmc0 i]
    norm_num

/-- Exact Price of Unaccountability values for `n = 2` and `n = 3` at `γ = 1 / 4`. -/
example :
    priceOfUnaccountability (andTech 2 (1 / 4)) (fun _ => 1) = 11 / 3 ∧
      priceOfUnaccountability (andTech 3 (1 / 4)) (fun _ => 1) = 29 / 3 := by
  rw [andTech_pou_eq (by omega) (by norm_num) (by norm_num) zero_lt_one,
    andTech_pou_eq (by omega) (by norm_num) (by norm_num) zero_lt_one]
  norm_num

/-- Three-agent AND skips interior team sizes `1` and `2` at `v = 5`. -/
example :
    andProb 3 (1 / 4) 1 * 5 - 1 <
        max (andProb 3 (1 / 4) 0 * 5 - 0) (andProb 3 (1 / 4) 2 * 5 - 2) ∧
      andProb 3 (1 / 4) 2 * 5 - anonOptPayment (andProb 3 (1 / 4)) 1 2 <
        max (andProb 3 (1 / 4) 1 * 5 - anonOptPayment (andProb 3 (1 / 4)) 1 1)
          (andProb 3 (1 / 4) 3 * 5 - anonOptPayment (andProb 3 (1 / 4)) 1 3) := by
  have h1 := (andTech_skips_interior (n := 3) (γ := 1 / 4) (c := 1)
    (by omega) (by norm_num) (by norm_num) zero_lt_one 5 1 zero_lt_one (by omega)).1
  have h2 := (andTech_skips_interior (n := 3) (γ := 1 / 4) (c := 1)
    (by omega) (by norm_num) (by norm_num) zero_lt_one 5 2 (by omega) (by omega)).2
  exact ⟨by simpa using h1, h2⟩

/-! ### Exercise 23.6 boundary: `IsStrongEquilibrium` without `IsStrongNash` when `c_1 = 0` -/

/-- With zero cost for agent `1`, `![true, false]` is a strong equilibrium but not strong Nash. -/
example :
    let tfProfile : Fin 2 → Bool := fun i => if i = 0 then true else false
    let zeroSecondCost : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    (contractCostGame (andTech 2 (1 / 4)) zeroSecondCost
      (optContract (andTech 2 (1 / 4)) zeroSecondCost tfProfile)).IsStrongEquilibrium tfProfile ∧
      ¬ (contractCostGame (andTech 2 (1 / 4)) zeroSecondCost
        (optContract (andTech 2 (1 / 4)) zeroSecondCost tfProfile)).IsStrongNash tfProfile := by
  intro tfProfile zeroSecondCost
  let allTrue : Fin 2 → Bool := fun _ => true
  have ht := isStrictlyMonotone_andTech 2 (γ := 1 / 4) (by norm_num) (by norm_num)
  have hcn : ∀ i : Fin 2, 0 ≤ zeroSecondCost i := by
    intro i; fin_cases i <;> norm_num [zeroSecondCost]
  refine ⟨isStrongEquilibrium_optContract _ _ tfProfile ht hcn, fun hsn => ?_⟩
  have hc_tf : countTrue tfProfile = 1 := by
    have hf : Finset.univ.filter (fun i : Fin 2 => tfProfile i = true) = {0} := by
      ext i; fin_cases i <;> simp [tfProfile]
    simp [countTrue_eq, hf]
  have hmc0 : marginalContrib (andTech 2 (1 / 4)) 0 tfProfile = 1 / 8 := by
    have ht0 : tfProfile 0 = true := rfl
    rw [anon_marginalContrib (t := andTech 2 (1 / 4)) (f := andProb 2 (1 / 4))
      (andTech_eq 2 (1 / 4)) ht0, hc_tf]
    norm_num [andProb_eq]
  have hopt0 : optContract (andTech 2 (1 / 4)) zeroSecondCost tfProfile 0 = 8 := by
    have ht0 : tfProfile 0 = true := rfl
    have hc0 : zeroSecondCost 0 = 1 := by simp [zeroSecondCost]
    rw [optContract_of_true _ _ ht0, hc0, hmc0]
    norm_num
  have hopt1 : optContract (andTech 2 (1 / 4)) zeroSecondCost tfProfile 1 = 0 := by
    have hf1 : tfProfile 1 = false := rfl
    exact optContract_of_false _ _ hf1
  have hp : (Finset.univ : Finset (Fin 2)).piecewise allTrue tfProfile = allTrue := by
    ext i; fin_cases i <;> simp [allTrue, tfProfile]
  have ht_tf : andTech 2 (1 / 4) tfProfile = 3 / 16 := by
    rw [andTech_eq, hc_tf]; norm_num [andProb_eq]
  have ht_all : andTech 2 (1 / 4) allTrue = 9 / 16 := by
    have hca : countTrue allTrue = 2 := countTrue_true
    rw [andTech_eq, hca]; norm_num [andProb_eq]
  refine hsn Finset.univ allTrue ⟨fun i _ => ?_, 0, Finset.mem_univ 0, ?_⟩
  · fin_cases i
    · simp only [Fin.zero_eta]
      rw [hp, contractCostGame_cost, contractCostGame_cost, hopt0, ht_all, ht_tf]
      norm_num [zeroSecondCost, tfProfile, allTrue]
    · simp only [Fin.mk_one]
      rw [hp, contractCostGame_cost, contractCostGame_cost, hopt1]
      norm_num [zeroSecondCost, tfProfile, allTrue]
  · rw [hp, contractCostGame_cost, contractCostGame_cost, hopt0, ht_all, ht_tf]
    norm_num [zeroSecondCost, tfProfile, allTrue]

/-! ### Noisy OR witnesses (`γ = 1 / 4`, `c = 1`) -/

/-- Two-agent OR (`γ = 1 / 4`) satisfies `19 / 13 ≤ POU ≤ 2`. -/
example :
    19 / 13 ≤ priceOfUnaccountability (orTech 2 (1 / 4)) (fun _ => 1) ∧
      priceOfUnaccountability (orTech 2 (1 / 4)) (fun _ => 1) ≤ 2 := by
  have htpos : ∀ s, 0 < orTech 2 (1 / 4) s := fun s =>
    orTech_pos (by omega) (by norm_num) (by norm_num) s
  have hc_nn : ∀ _ : Fin 2, (0 : ℝ) ≤ 1 := fun _ => by norm_num
  have hle := le_priceOfUnaccountability (orTech 2 (1 / 4)) (fun _ => 1) htpos hc_nn
    (v := 52 / 9) (by norm_num)
  have hsw : (133 : ℝ) / 36 ≤ firstBestWelfare (orTech 2 (1 / 4)) (fun _ => 1) (52 / 9) := by
    rw [firstBestWelfare_anon (t := orTech 2 (1 / 4)) (f := orProb 2 (1 / 4)) (orTech_eq 2 (1 / 4))]
    calc
      (133 : ℝ) / 36 = orProb 2 (1 / 4) 1 * (52 / 9) - ((1 : ℕ) : ℝ) * 1 := by
        norm_num [orProb_eq]
      _ ≤ _ := Finset.le_sup'
        (fun k => orProb 2 (1 / 4) k * (52 / 9) - (k : ℝ) * 1)
        (Finset.mem_range.mpr (by decide : 1 < 2 + 1))
  have hu : agencyPrincipalUtility (orTech 2 (1 / 4)) (fun _ => 1) (52 / 9) = 91 / 36 := by
    rw [agencyPrincipalUtility_anon (t := orTech 2 (1 / 4)) (f := orProb 2 (1 / 4))
      (orTech_eq 2 (1 / 4))]
    apply le_antisymm
    · refine Finset.sup'_le ⟨0, Finset.mem_range.mpr (by omega)⟩ _ fun k hk => ?_
      have hkle : k ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      interval_cases k <;> norm_num [orProb_eq, anonOptPayment_eq]
    · calc
        (91 : ℝ) / 36 = orProb 2 (1 / 4) 0 * (52 / 9) - anonOptPayment (orProb 2 (1 / 4)) 1 0 := by
          norm_num [orProb_eq, anonOptPayment_eq]
        _ ≤ _ := Finset.le_sup'
          (fun k => orProb 2 (1 / 4) k * (52 / 9) - anonOptPayment (orProb 2 (1 / 4)) 1 k)
          (Finset.mem_range.mpr (by decide : 0 < 2 + 1))
  refine ⟨?_,
    orTech_pou_le_two (n := 2) (γ := 1 / 4) (by omega) (by norm_num) (by norm_num) zero_lt_one⟩
  calc
    (19 : ℝ) / 13 = (133 / 36) / (91 / 36) := by norm_num
    _ ≤ firstBestWelfare (orTech 2 (1 / 4)) (fun _ => 1) (52 / 9) /
        agencyPrincipalUtility (orTech 2 (1 / 4)) (fun _ => 1) (52 / 9) := by
      rw [hu]
      exact div_le_div_of_nonneg_right hsw (by norm_num)
    _ ≤ priceOfUnaccountability (orTech 2 (1 / 4)) (fun _ => 1) := hle

/-- Three-agent OR (`γ = 1 / 4`) uniquely optimizes each cardinality `0..3` at `v = 5..3000`. -/
example :
    (∀ j ≤ 3, j ≠ 0 → orProb 3 (1 / 4) j * 5 - anonOptPayment (orProb 3 (1 / 4)) 1 j <
      orProb 3 (1 / 4) 0 * 5 - anonOptPayment (orProb 3 (1 / 4)) 1 0) ∧
    (∀ j ≤ 3, j ≠ 1 → orProb 3 (1 / 4) j * 50 - anonOptPayment (orProb 3 (1 / 4)) 1 j <
      orProb 3 (1 / 4) 1 * 50 - anonOptPayment (orProb 3 (1 / 4)) 1 1) ∧
    (∀ j ≤ 3, j ≠ 2 → orProb 3 (1 / 4) j * 500 - anonOptPayment (orProb 3 (1 / 4)) 1 j <
      orProb 3 (1 / 4) 2 * 500 - anonOptPayment (orProb 3 (1 / 4)) 1 2) ∧
    (∀ j ≤ 3, j ≠ 3 → orProb 3 (1 / 4) j * 3000 - anonOptPayment (orProb 3 (1 / 4)) 1 j <
      orProb 3 (1 / 4) 3 * 3000 - anonOptPayment (orProb 3 (1 / 4)) 1 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro j hj hne <;> interval_cases j <;>
    first | exact absurd rfl hne | norm_num [orProb_eq, anonOptPayment_eq]

/-! ### Exercise 23.5: First-best vs hidden-action transition divergence -/

/-- First-best welfare always skips `k = 1`, whereas agency strictly selects `k = 1` at `v = 5`. -/
example :
    let mismatchProb : ℕ → ℝ := fun k => match k with | 0 => 1 / 10 | 1 => 1 / 2 | _ => 19 / 20
    let mismatchTech : (Fin 2 → Bool) → ℝ := fun a => mismatchProb (countTrue a)
    (∀ v : ℝ, mismatchProb 1 * v - 1 <
        max (mismatchProb 0 * v - 0) (mismatchProb 2 * v - 2)) ∧
      (∀ v : ℝ, firstBestWelfare mismatchTech (fun _ => 1) v =
        max (mismatchProb 0 * v - 0) (mismatchProb 2 * v - 2)) ∧
      (∀ j ≤ 2, j ≠ 1 →
        mismatchProb j * 5 - anonOptPayment mismatchProb 1 j <
          mismatchProb 1 * 5 - anonOptPayment mismatchProb 1 1) := by
  intro mismatchProb mismatchTech
  have hdec : (1 - 0 : ℝ) / (mismatchProb 1 - mismatchProb 0) >
      (2 - 1 : ℝ) / (mismatchProb 2 - mismatchProb 1) := by
    norm_num [mismatchProb]
  have hs_all := fun v => strictly_decreasing_slope_skips (n := 2) (by omega) mismatchProb
    (fun k => (k : ℝ) * 1)
    (fun k hk => by interval_cases k <;> norm_num [mismatchProb])
    (fun k hk0 hkn => by
      have hk1 : k = 1 := by omega
      subst hk1; simpa [mismatchProb] using hdec) v
  refine ⟨fun v => by simpa using (hs_all v).2 1 zero_lt_one (by omega), fun v => ?_, ?_⟩
  · rw [firstBestWelfare_anon (t := mismatchTech) (f := mismatchProb) (fun _ => rfl)]
    simpa using (hs_all v).1
  · intro j hj hne
    interval_cases j
    · norm_num [mismatchProb, anonOptPayment_eq]
    · exact absurd rfl hne
    · norm_num [mismatchProb, anonOptPayment_eq]

end CslibFrontierTests.GameTheory.CombinatorialAgency
