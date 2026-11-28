/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.PredictionMarket.BooleanAggregation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked witnesses for Shapley–Shubik Boolean prediction markets

Ordinary `module` client exercising `Cslib.GameTheory.PredictionMarket` across the export boundary:

* **Example 26.8** (`orMarket_bids_and_eqPrice`): 2-agent OR market under the uniform prior at
  `(false, true)` (`b₁ = 1/2`, `b₂ = 1`, `p¹ = 3/4`, `p^∞ = 1`).
* **Example 26.10** (`xorMarket_bids_and_eqPrice`, `not_isWeightedThreshold_xor`): 2-agent XOR
  market stuck at `p¹ = p^∞ = 1/2 ≠ f x`, certifying `¬ IsWeightedThreshold`.
* **Theorem 26.9** (`equilibrium_commonKnowledge_of_aggregates`): common knowledge of aggregates
  on OR, XOR, and a zero-mass boundary prior where `priorSupport P ≠ Finset.univ`.
* **Theorem 26.12 & Theorem 26.14** on 3-agent majority (`IsWeightedThreshold`, equilibrium price
  equals `maj3 x`, convergence within `3` rounds under a non-uniform prior).
* **Theorem 26.13** (`exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold`,
  `isWeightedThreshold_iff_forall_eqPrice_eq`) on 2-agent XOR.
* **Theorem 26.15** concrete `C₂` (`4`-input) witness via `carryChain_convergence_rounds` and
  `exists_n_round_lower_bound`, verifying exact round-by-round prices `p¹ = 1/2`,
  `p² = 5/12` vs `7/12`, and `p³ = 0` vs `1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.BooleanAggregation

open Finset Cslib.GameTheory Cslib.GameTheory.PredictionMarket

/-! ### Examples 26.8 (OR) and 26.10 (XOR) -/

/-- Example 26.8: 2-agent OR market under the uniform prior at `(false, true)`. -/
example :
    let f : (Fin 2 → Bool) → Bool := fun y => y 0 || y 1
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    let x : Fin 2 → Bool := ![false, true]
    agentBid f P (priorSupport P) 0 x = 1 / 2 ∧
      agentBid f P (priorSupport P) 1 x = 1 ∧
      roundPrice f P (priorSupport P) x = 3 / 4 ∧
      eqPrice f P x = 1 :=
  orMarket_bids_and_eqPrice

/-- Example 26.10: 2-agent XOR market under the uniform prior stays at `1/2` and never reveals
`f x`, and XOR is not a weighted threshold function. -/
example :
    let f : (Fin 2 → Bool) → Bool := fun y => xor (y 0) (y 1)
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    (∀ x i, agentBid f P (priorSupport P) i x = 1 / 2) ∧
      (∀ x, roundPrice f P (priorSupport P) x = 1 / 2) ∧
      (∀ x, eqPrice f P x = 1 / 2 ∧ eqPrice f P x ≠ if f x then 1 else 0) ∧
      ¬ IsWeightedThreshold f :=
  ⟨xorMarket_bids_and_eqPrice.1, xorMarket_bids_and_eqPrice.2.1,
    xorMarket_bids_and_eqPrice.2.2, not_isWeightedThreshold_xor⟩

/-! ### Theorem 26.9 on OR, XOR, and a zero-mass boundary prior -/

/-- Theorem 26.9 on the 2-agent OR market: at equilibrium, common-knowledge expectation and every
agent's equilibrium bid equal `1`. -/
example :
    let f : (Fin 2 → Bool) → Bool := fun y => y 0 || y 1
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    let x : Fin 2 → Bool := ![false, true]
    condExpect f P (eqSet f P x) = 1 ∧
      ∀ i : Fin 2, ∀ y ∈ eqSet f P x, agentBid f P (eqSet f P x) i y = 1 := by
  intro f P x
  have h := equilibrium_commonKnowledge_of_aggregates (n := 2) (by decide) (f := f) (P := P)
    (x := x) (by norm_num [P])
  have hp : eqPrice f P x = 1 := orMarket_bids_and_eqPrice.2.2.2
  simpa only [hp] using h

/-- Theorem 26.9 on the 2-agent XOR market: at equilibrium, common-knowledge expectation and every
agent's equilibrium bid agree at `1/2`. -/
example :
    let f : (Fin 2 → Bool) → Bool := fun y => xor (y 0) (y 1)
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    let x : Fin 2 → Bool := ![false, false]
    condExpect f P (eqSet f P x) = 1 / 2 ∧
      ∀ i : Fin 2, ∀ y ∈ eqSet f P x, agentBid f P (eqSet f P x) i y = 1 / 2 := by
  intro f P x
  have h := equilibrium_commonKnowledge_of_aggregates (n := 2) (by decide) (f := f) (P := P)
    (x := x) (by norm_num [P])
  have hp : eqPrice f P x = 1 / 2 := (xorMarket_bids_and_eqPrice.2.2 x).1
  simpa only [hp] using h

/-- Boundary witness for zero-mass states: under a prior assigning `0` to `(false, false)` and
`1/3` to the remaining three states, `(false, false) ∉ priorSupport P`, every remaining state has
`OR = true`, and Theorem 26.9 gives equilibrium price `1` with zero-mass states excluded. -/
example :
    let f : (Fin 2 → Bool) → Bool := fun y => y 0 || y 1
    let P : (Fin 2 → Bool) → ℝ := fun y => if y = ![false, false] then 0 else 1 / 3
    (![false, false] : Fin 2 → Bool) ∉ priorSupport P ∧
      eqPrice f P ![false, true] = 1 ∧
      condExpect f P (eqSet f P ![false, true]) = 1 := by
  intro f P
  have hne : (![false, true] : Fin 2 → Bool) ≠ ![false, false] := fun h => by
    have := congrFun h 1; simp at this
  have hxpos : 0 < P ![false, true] := by simp [P, hne]
  have hf_wt : IsWeightedThreshold f := by
    refine isWeightedThreshold_iff.mpr ⟨0, fun _ => 1, fun y => ?_⟩
    simp only [f, Fin.sum_univ_two, zero_add, one_mul]
    cases y 0 <;> cases y 1 <;> norm_num
  have hp : eqPrice f P ![false, true] = 1 := by
    simpa [f] using eqPrice_eq_of_isWeightedThreshold (by decide) hf_wt hxpos
  have hce := (equilibrium_commonKnowledge_of_aggregates (by decide) (f := f) hxpos).1
  refine ⟨by simp [P], hp, hce.trans hp⟩

/-! ### Theorem 26.12 and Theorem 26.14 on 3-agent majority -/

/-- Three-agent majority function `maj3(x₀, x₁, x₂) = true` iff at least two bits are `true`. -/
def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

theorem isWeightedThreshold_maj3 : IsWeightedThreshold maj3 := by
  refine isWeightedThreshold_iff.mpr ⟨-1, fun _ => 1, fun x => ?_⟩
  simp only [maj3, Fin.sum_univ_three, one_mul]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- Under any prior with positive mass at `x` (witnessed by a non-uniform prior on `{0, 1}³`),
3-agent majority converges to `maj3 x` within `3` rounds (Theorems 26.12 & 26.14). -/
example :
    let P : (Fin 3 → Bool) → ℝ := fun y => if y 0 then 1 / 6 else 1 / 12
    let x₁ : Fin 3 → Bool := ![true, false, true]
    let x₀ : Fin 3 → Bool := ![false, false, true]
    IsMixedStrategy P ∧
      eqPrice maj3 P x₁ = 1 ∧
      roundPrice maj3 P (commonKnowledge maj3 P x₁ 3) x₁ = 1 ∧
      eqPrice maj3 P x₀ = 0 ∧
      roundPrice maj3 P (commonKnowledge maj3 P x₀ 3) x₀ = 0 := by
  intro P x₁ x₀
  have hP : IsMixedStrategy P := by
    refine isMixedStrategy_iff.mpr ⟨fun y => by simp only [P]; split_ifs <;> norm_num, ?_⟩
    have hcard_t : (Finset.univ.filter fun y : Fin 3 → Bool => y 0 = true).card = 4 := by decide
    have hcard_f : (Finset.univ.filter fun y : Fin 3 → Bool => ¬ y 0 = true).card = 4 := by decide
    rw [← sum_filter_add_sum_filter_not Finset.univ (fun y : Fin 3 → Bool => y 0 = true)]
    have ht : ∑ y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => y 0 = true), P y = 4 * (1 / 6) := by
      have heq : ∑ y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => y 0 = true), P y =
          ∑ _y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => y 0 = true), (1 / 6 : ℝ) :=
        sum_congr rfl fun y hy => by simp [P, (mem_filter.mp hy).2]
      rw [heq, sum_const, hcard_t, nsmul_eq_mul]; norm_num
    have hf : ∑ y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => ¬ y 0 = true), P y =
        4 * (1 / 12) := by
      have heq : ∑ y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => ¬ y 0 = true), P y =
          ∑ _y ∈ Finset.univ.filter (fun y : Fin 3 → Bool => ¬ y 0 = true), (1 / 12 : ℝ) :=
        sum_congr rfl fun y hy => by simp [P, (mem_filter.mp hy).2]
      rw [heq, sum_const, hcard_f, nsmul_eq_mul]; norm_num
    rw [ht, hf]; norm_num
  have hx₁_pos : 0 < P x₁ := by norm_num [P, x₁]
  have hx₀_pos : 0 < P x₀ := by norm_num [P, x₀]
  have h1 := convergence_in_n_rounds_of_isWeightedThreshold (by decide) isWeightedThreshold_maj3
    hx₁_pos (r := 3) le_rfl
  have h0 := convergence_in_n_rounds_of_isWeightedThreshold (by decide) isWeightedThreshold_maj3
    hx₀_pos (r := 3) le_rfl
  have hp1 : eqPrice maj3 P x₁ = 1 := by
    simpa [maj3, x₁] using eqPrice_eq_of_isWeightedThreshold (by decide) isWeightedThreshold_maj3
      hx₁_pos
  have hp0 : eqPrice maj3 P x₀ = 0 := by
    simpa [maj3, x₀] using eqPrice_eq_of_isWeightedThreshold (by decide) isWeightedThreshold_maj3
      hx₀_pos
  exact ⟨hP, hp1, by simpa [maj3, x₁] using h1.2.1, hp0, by simpa [maj3, x₀] using h0.2.1⟩

/-! ### Theorem 26.13 on 2-agent XOR -/

/-- Theorem 26.13 applied to 2-agent XOR produces a mixed-strategy prior stuck at `p^∞ = 1/2`,
and `isWeightedThreshold_iff_forall_eqPrice_eq` certifies non-computability across all priors. -/
example :
    (∃ P : (Fin 2 → Bool) → ℝ, IsMixedStrategy P ∧
      ∀ x, 0 < P x → eqPrice (fun y => xor (y 0) (y 1)) P x = 1 / 2) ∧
    ¬ (∀ P : (Fin 2 → Bool) → ℝ, IsMixedStrategy P → ∀ x, 0 < P x →
      eqPrice (fun y => xor (y 0) (y 1)) P x = if xor (x 0) (x 1) then 1 else 0) :=
  ⟨exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold not_isWeightedThreshold_xor,
    mt (isWeightedThreshold_iff_forall_eqPrice_eq (by decide) _).mpr not_isWeightedThreshold_xor⟩

/-! ### Theorem 26.14 & Theorem 26.15 concrete `C₂` (4-input) round-by-round witness -/

/-- Concrete `C₂` (`2 * 2 = 4` inputs) witness verifying every round-by-round clearing price:
* `C₂` is a weighted threshold function and `carryPrior 2` is a valid prior;
* on `x₀ = carryInputFalse 2` (`C₂ = false`) and `x₁ = carryInputTrue 2` (`C₂ = true`):
  - Round 1 (`S⁰`): `S⁰(x₀) = S⁰(x₁)`, `condExpect = 1/2`, `p¹(x₀) = p¹(x₁) = 1/2`;
  - Round 2 (`S¹`): `S¹(x₀) = S¹(x₁)`, `condExpect = 1/2`, `p²(x₀) = 5/12` and `p²(x₁) = 7/12`;
  - After round 2 (`S²`): common knowledge reveals `C₂`, with `p³(x₀) = 0` and `p³(x₁) = 1`,
    and by Theorem 26.14 equilibrium holds for all `r ≥ 4`. -/
example :
    IsWeightedThreshold (carryChain 2) ∧
    IsMixedStrategy (carryPrior 2) ∧
    carryChain 2 (carryInputFalse 2) = false ∧
    carryChain 2 (carryInputTrue 2) = true ∧
    commonKnowledge (carryChain 2) (carryPrior 2) (carryInputFalse 2) 1 =
      commonKnowledge (carryChain 2) (carryPrior 2) (carryInputTrue 2) 1 ∧
    roundPrice (carryChain 2) (carryPrior 2)
      (commonKnowledge (carryChain 2) (carryPrior 2) (carryInputFalse 2) 0)
      (carryInputFalse 2) = 1 / 2 ∧
    roundPrice (carryChain 2) (carryPrior 2)
      (commonKnowledge (carryChain 2) (carryPrior 2) (carryInputFalse 2) 1)
      (carryInputFalse 2) = 5 / 12 ∧
    roundPrice (carryChain 2) (carryPrior 2)
      (commonKnowledge (carryChain 2) (carryPrior 2) (carryInputTrue 2) 1)
      (carryInputTrue 2) = 7 / 12 ∧
    roundPrice (carryChain 2) (carryPrior 2)
      (commonKnowledge (carryChain 2) (carryPrior 2) (carryInputFalse 2) 2)
      (carryInputFalse 2) = 0 ∧
    roundPrice (carryChain 2) (carryPrior 2)
      (commonKnowledge (carryChain 2) (carryPrior 2) (carryInputTrue 2) 2)
      (carryInputTrue 2) = 1 := by
  obtain ⟨_, _, hff, hft, hlt, hf2, ht2⟩ := carryChain_convergence_rounds (n := 2) (by decide)
  obtain ⟨_, _, hpf0, _⟩ := hlt 0 (by decide)
  obtain ⟨hS1, _, hpf1, hpt1⟩ := hlt 1 (by decide)
  refine ⟨isWeightedThreshold_carryChain 2, isMixedStrategy_carryPrior 2, hff, hft, hS1,
    ?_, ?_, ?_, hf2.2, ht2.2⟩
  · simpa using hpf0
  · rw [hpf1]; norm_num
  · rw [hpt1]; norm_num

/-- Direct invocation of Theorem 26.15 (`exists_n_round_lower_bound`) at `n = 2` (`4` inputs). -/
example :
    ∃ (f : (Fin 4 → Bool) → Bool) (P : (Fin 4 → Bool) → ℝ) (x₀ x₁ : Fin 4 → Bool),
      IsWeightedThreshold f ∧ IsMixedStrategy P ∧
      0 < P x₀ ∧ 0 < P x₁ ∧ f x₀ = false ∧ f x₁ = true ∧
      (∀ r < 2,
        commonKnowledge f P x₀ r = commonKnowledge f P x₁ r ∧
        condExpect f P (commonKnowledge f P x₀ r) = 1 / 2 ∧
        roundPrice f P (commonKnowledge f P x₀ r) x₀ ≠ 0 ∧
        roundPrice f P (commonKnowledge f P x₁ r) x₁ ≠ 1) ∧
      ((∀ y ∈ commonKnowledge f P x₀ 2, f y = false) ∧
        roundPrice f P (commonKnowledge f P x₀ 2) x₀ = 0) ∧
      ((∀ y ∈ commonKnowledge f P x₁ 2, f y = true) ∧
        roundPrice f P (commonKnowledge f P x₁ 2) x₁ = 1) :=
  exists_n_round_lower_bound (n := 2) (by decide)

end CslibFrontierTests.GameTheory.BooleanAggregation
