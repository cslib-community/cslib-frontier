/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.ResourceAllocation.MarketClearing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests and boundary witnesses for NRTV §21.3 smooth market-clearing mechanisms

Exercises `CslibFrontier.GameTheory.ResourceAllocation.MarketClearing` as an ordinary `module`
client without exposing internal implementation details:

* `c = 1` (`powerElasticityMechanism 1`, `D(p, θ) = θ / p`): belongs to `𝒟`
  (`IsRegularMarketClearing`), achieves exact worst-case efficiency ratio `3 / 4`, satisfies the
  Johari–Tsitsiklis scalar-proportional characterization (`Δ = 1`), and admits competitive and
  unique Nash equilibria on concrete instances.
* `c = 2` (`powerElasticityMechanism 2`, `D(p, θ) = θ * p ^ (-1 / 2)`): belongs to `𝒟`, has exact
  worst-case efficiency ratio `4 * √2 - 5 < 3 / 4`, and admits an explicit 7-player linear-utility
  game whose unique Nash equilibrium achieves welfare `5 / 3` against optimal welfare `7 / 3`
  (ratio `5 / 7 < 3 / 4`, strictly violating Kelly's `3 / 4` guarantee).
* Boundary non-member of `𝒟` (`c = 1 / 2`, `D(p, θ) = θ * p ^ (-2)`): satisfies
  `IsSmoothMarketClearing` and demand surjectivity on `[0, ∞)`, yet fails price-anticipating payoff
  concavity (`¬ IsRegularMarketClearing (powerElasticityMechanism (1 / 2))`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.KellyMarketClearing

open Cslib.GameTheory Set

/-! ### 1. Kelly proportional sharing (`c = 1`, `D(p, θ) = θ / p`, `ρ = 3 / 4`) -/

section KellyMechanismInstance

/-- At `c = 1`, `powerElasticityMechanism 1` is Kelly's demand `D(p, θ) = θ / p`, belongs to `𝒟`,
and achieves the maximum possible worst-case efficiency ratio `3 / 4`. -/
example :
    (∀ p > 0, ∀ θ : ℝ, powerElasticityMechanism 1 p θ = θ / p) ∧
    IsRegularMarketClearing (powerElasticityMechanism 1) ∧
    efficiencyRatio (powerElasticityMechanism 1) = 3 / 4 := by
  refine ⟨fun p _ θ => ?_, isRegularMarketClearing_powerElasticity le_rfl, ?_⟩
  · rw [powerElasticityMechanism_apply, div_one, Real.rpow_neg_one, div_eq_mul_inv]
  · rw [efficiencyRatio_powerElasticity le_rfl, elasticityEfficiencyBound_one]

/-- Exercising Theorem 21.10(i)–(iii) on `powerElasticityMechanism 1` and a 2-user instance. -/
example :
    let D := powerElasticityMechanism 1
    let G : KellyGame (Fin 2) := ⟨1, fun _ x => x⟩
    (∃ B : ℝ → ℝ, BijOn B (Ioi 0) (Ioi 0) ∧ ConcaveOn ℝ (Ioi 0) B ∧ StrictMonoOn B (Ioi 0) ∧
      DifferentiableOn ℝ B (Ioi 0) ∧ ∀ p > 0, ∀ θ ≥ 0, D p θ = θ / B p) ∧
    (∃ θ, IsMarketCompetitiveEquilibrium D G θ ∧ G.IsSocialOptimum (marketAllocation D 1 θ)) ∧
    (∃! θ, IsMarketNashEquilibrium D G θ) ∧
    (∃ Δ > 0, ∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = Δ * θ / p) := by
  intro D G
  have hD : IsRegularMarketClearing D := isRegularMarketClearing_powerElasticity le_rfl
  have hU : ∀ i : Fin 2, IsAdmissibleUtility (G.utility i) := fun _ => by
    simpa only [G, one_mul] using KellyGame.isAdmissibleUtility_linear zero_lt_one
  have hρ : efficiencyRatio D = 3 / 4 := by
    dsimp only [D]
    rw [efficiencyRatio_powerElasticity le_rfl, elasticityEfficiencyBound_one]
  exact ⟨hD.exists_priceScale,
    hD.exists_isMarketCompetitiveEquilibrium (by decide) zero_lt_one hU,
    hD.existsUnique_isMarketNashEquilibrium (by decide) zero_lt_one hU,
    hD.efficiencyRatio_eq_three_fourths_iff.mp hρ⟩

end KellyMechanismInstance

/-! ### 2. Square-root demand (`c = 2`, `D(p, θ) = θ / √p`, `ρ = 4√2 - 5 < 3 / 4`) -/

section RootPriceInstance

/-- At `c = 2`, `D(p, θ) = θ / √p` belongs to `𝒟` and has exact worst-case efficiency ratio
`4 * √2 - 5`, which is strictly below `3 / 4`. -/
example :
    (∀ p > 0, ∀ θ : ℝ, powerElasticityMechanism 2 p θ = θ / Real.sqrt p) ∧
    IsRegularMarketClearing (powerElasticityMechanism 2) ∧
    efficiencyRatio (powerElasticityMechanism 2) = 4 * Real.sqrt 2 - 5 ∧
    efficiencyRatio (powerElasticityMechanism 2) < 3 / 4 := by
  have hc : (1 : ℝ) ≤ 2 := by norm_num
  have hform : ∀ p > 0, ∀ θ : ℝ, powerElasticityMechanism 2 p θ = θ / Real.sqrt p := by
    intro p hp θ
    rw [powerElasticityMechanism_apply, show (-1 : ℝ) / 2 = -(1 / 2) by ring,
      Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hρ : efficiencyRatio (powerElasticityMechanism 2) = 4 * Real.sqrt 2 - 5 := by
    rw [efficiencyRatio_powerElasticity hc,
      elasticityEfficiencyBound_eq_of_one_lt (by norm_num : (1 : ℝ) < 2)]
    ring
  have hlt : efficiencyRatio (powerElasticityMechanism 2) < 3 / 4 := by
    rw [efficiencyRatio_powerElasticity hc, ← elasticityEfficiencyBound_one]
    exact elasticityEfficiencyBound_strictAntiOn (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr hc) (by norm_num)
  exact ⟨hform, isRegularMarketClearing_powerElasticity hc, hρ, hlt⟩

/-- Concrete 7-player linear-utility game of unit capacity witnessing that
`powerElasticityMechanism 2` has a price-anticipating Nash equilibrium with welfare `5 / 3` against
optimal welfare `7 / 3`, giving welfare ratio `5 / 7 < 3 / 4`. -/
private noncomputable def cTwoWitnessGame : KellyGame (Fin 7) where
  capacity := 1
  utility := fun r x => if r = 0 then (7 / 3 : ℝ) * x else (11 / 9 : ℝ) * x

private noncomputable def cTwoWitnessBids : Fin 7 → ℝ :=
  fun r => if r = 0 then 2 / 5 else 1 / 10

example :
    let D := powerElasticityMechanism 2
    let G := cTwoWitnessGame
    let θ := cTwoWitnessBids
    let opt : Fin 7 → ℝ := Pi.single 0 1
    (∀ r, IsAdmissibleUtility (G.utility r)) ∧
    G.IsSocialOptimum opt ∧
    IsMarketNashEquilibrium D G θ ∧
    G.welfare (marketAllocation D G.capacity θ) = 5 / 3 ∧
    G.welfare opt = 7 / 3 ∧
    G.welfare (marketAllocation D G.capacity θ) / G.welfare opt < 3 / 4 := by
  intro D G θ opt
  have hc : (1 : ℝ) ≤ 2 := by norm_num
  have hc_pos : (0 : ℝ) < 2 := by norm_num
  have hreg : IsRegularMarketClearing D := isRegularMarketClearing_powerElasticity hc
  have hU : ∀ r : Fin 7, IsAdmissibleUtility (G.utility r) := fun r => by
    dsimp only [G, cTwoWitnessGame]
    split_ifs
    · exact KellyGame.isAdmissibleUtility_linear (by norm_num)
    · exact KellyGame.isAdmissibleUtility_linear (by norm_num)
  have hopt_w : G.welfare opt = 7 / 3 := by
    rw [KellyGame.welfare, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 7))]
    have hrest : ∑ r ∈ Finset.univ.erase (0 : Fin 7), G.utility r (opt r) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        have hne := Finset.ne_of_mem_erase hr
        simp only [G, cTwoWitnessGame, opt, Pi.single_eq_of_ne hne, hne, ↓reduceIte, mul_zero]
    rw [hrest, add_zero]
    simp only [G, cTwoWitnessGame, opt, Pi.single_eq_same, ↓reduceIte, mul_one]
  have hopt : G.IsSocialOptimum opt := by
    refine ⟨⟨fun r => by
        rcases eq_or_ne r 0 with rfl | hr
        · simp [opt]
        · simp [opt, hr],
      by simp [opt, G, cTwoWitnessGame]⟩, fun x hx => ?_⟩
    rw [hopt_w]
    calc G.welfare x = ∑ r, G.utility r (x r) := rfl
      _ ≤ ∑ r, (7 / 3 : ℝ) * x r := Finset.sum_le_sum fun r _ => by
          dsimp only [G, cTwoWitnessGame]
          split_ifs
          · exact le_rfl
          · exact mul_le_mul_of_nonneg_right (by norm_num) (hx.1 r)
      _ = (7 / 3 : ℝ) * ∑ r, x r := (Finset.mul_sum ..).symm
      _ ≤ (7 / 3 : ℝ) * 1 := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
      _ = 7 / 3 := mul_one _
  have hθ0 : ∀ r : Fin 7, 0 ≤ θ r := fun r => by
    dsimp only [θ, cTwoWitnessBids]; split_ifs <;> norm_num
  have hcard_e0 : (Finset.univ.erase (0 : Fin 7)).card = 6 := by decide
  have hsum_e0 : ∑ r ∈ Finset.univ.erase (0 : Fin 7), θ r = 3 / 5 := by
    have hconst : ∑ r ∈ Finset.univ.erase (0 : Fin 7), θ r =
        ∑ _r ∈ Finset.univ.erase (0 : Fin 7), (1 / 10 : ℝ) :=
      Finset.sum_congr rfl fun r hr => by
        simp only [θ, cTwoWitnessBids, Finset.ne_of_mem_erase hr, ↓reduceIte]
    rw [hconst, Finset.sum_const, hcard_e0, nsmul_eq_mul]
    norm_num
  have hsum_θ : ∑ r : Fin 7, θ r = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 7)), hsum_e0]
    simp only [θ, cTwoWitnessBids, ↓reduceIte]
    norm_num
  have hne_zero : ∃ r : Fin 7, θ r ≠ 0 := ⟨0, by simp [θ, cTwoWitnessBids]⟩
  have hpay_formula : ∀ (r : Fin 7) (θb : Fin 7 → ℝ),
      (∀ s, 0 ≤ θb s) → (∃ s, θb s ≠ 0) →
        marketPayoff D G θb r =
          G.utility r (θb r / ∑ s, θb s) - θb r * ∑ s, θb s := by
    intro r θb hθb0 hθbne
    obtain ⟨s₀, hs₀⟩ := hθbne
    have hW_pos : 0 < ∑ s, θb s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀)]
      have hpos : 0 < θb s₀ := lt_of_le_of_ne (hθb0 s₀) (Ne.symm hs₀)
      have hrest : 0 ≤ ∑ s ∈ Finset.univ.erase s₀, θb s := Finset.sum_nonneg fun s _ => hθb0 s
      linarith
    have hp_eq : clearingPrice D G.capacity θb = (∑ s, θb s) ^ 2 := by
      dsimp only [G, cTwoWitnessGame, D]
      rw [clearingPrice_powerElasticity hc_pos (by decide) zero_lt_one hθb0 ⟨s₀, hs₀⟩,
        div_one, Real.rpow_two]
    have halloc_all : marketAllocation D G.capacity θb = G.allocation θb :=
      hreg.marketAllocation_eq_kellyAllocation (by decide) (by simp [G, cTwoWitnessGame])
        hθb0 ⟨s₀, hs₀⟩
    have halloc_r : marketAllocation D G.capacity θb r = θb r / ∑ s, θb s := by
      rw [congrFun halloc_all r]
      simp only [KellyGame.allocation, G, cTwoWitnessGame, one_mul]
    rw [marketPayoff_apply, hp_eq, halloc_r]
    congr 1
    field_simp [hW_pos.ne']
  have hne : IsMarketNashEquilibrium D G θ := by
    refine ⟨hθ0, hne_zero, fun r t ht0 hnz => ?_⟩
    have hupd0 : ∀ s : Fin 7, 0 ≤ Function.update θ r t s := fun s => by
      rcases eq_or_ne s r with rfl | hs
      · simpa only [Function.update_self] using ht0
      · simpa only [Function.update_of_ne hs] using hθ0 s
    rw [hpay_formula r _ hupd0 hnz, hpay_formula r θ hθ0 hne_zero, Function.update_self, hsum_θ,
      div_one, mul_one]
    have hsplit_θ := Finset.add_sum_erase Finset.univ θ (Finset.mem_univ r)
    rw [hsum_θ] at hsplit_θ
    have hsum_upd : ∑ s : Fin 7, Function.update θ r t s = t + (1 - θ r) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), Function.update_self]
      have herase_eq : ∑ s ∈ Finset.univ.erase r, Function.update θ r t s =
          ∑ s ∈ Finset.univ.erase r, θ s :=
        Finset.sum_congr rfl fun s hs => Function.update_of_ne (Finset.ne_of_mem_erase hs) _ _
      rw [herase_eq]
      linarith
    rw [hsum_upd]
    rcases eq_or_ne r 0 with rfl | hr
    · simp only [G, cTwoWitnessGame, θ, cTwoWitnessBids, ↓reduceIte]
      have hden_pos : 0 < t + (1 - (2 / 5 : ℝ)) := by linarith
      have hdiff : (7 / 3 : ℝ) * (2 / 5) - 2 / 5 -
          ((7 / 3 : ℝ) * (t / (t + (1 - 2 / 5))) - t * (t + (1 - 2 / 5))) =
          (5 * t - 2) ^ 2 * (3 * t + 6) / (75 * (t + (1 - 2 / 5))) := by
        field_simp [hden_pos.ne']
        ring
      have hnn : 0 ≤ (5 * t - 2) ^ 2 * (3 * t + 6) / (75 * (t + (1 - 2 / 5))) := by positivity
      linarith
    · simp only [G, cTwoWitnessGame, θ, cTwoWitnessBids, hr, ↓reduceIte]
      have hden_pos : 0 < t + (1 - (1 / 10 : ℝ)) := by linarith
      have hdiff : (11 / 9 : ℝ) * (1 / 10) - 1 / 10 -
          ((11 / 9 : ℝ) * (t / (t + (1 - 1 / 10))) - t * (t + (1 - 1 / 10))) =
          (10 * t - 1) ^ 2 * (9 * t + 18) / (900 * (t + (1 - 1 / 10))) := by
        field_simp [hden_pos.ne']
        ring
      have hnn : 0 ≤ (10 * t - 1) ^ 2 * (9 * t + 18) / (900 * (t + (1 - 1 / 10))) := by positivity
      linarith
  have halloc_θ : marketAllocation D G.capacity θ = θ := by
    rw [hreg.marketAllocation_eq_kellyAllocation (by decide) (by simp [G, cTwoWitnessGame])
      hθ0 hne_zero]
    funext r
    simp only [KellyGame.allocation, G, cTwoWitnessGame, hsum_θ, one_mul, div_one]
  have hw_ne : G.welfare (marketAllocation D G.capacity θ) = 5 / 3 := by
    rw [halloc_θ, KellyGame.welfare, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 7))]
    have hrest : ∑ r ∈ Finset.univ.erase (0 : Fin 7), G.utility r (θ r) = 11 / 15 := by
      have hconst : ∑ r ∈ Finset.univ.erase (0 : Fin 7), G.utility r (θ r) =
          ∑ _r ∈ Finset.univ.erase (0 : Fin 7), ((11 / 9 : ℝ) * (1 / 10)) :=
        Finset.sum_congr rfl fun r hr => by
          simp only [G, cTwoWitnessGame, θ, cTwoWitnessBids, Finset.ne_of_mem_erase hr, ↓reduceIte]
      rw [hconst, Finset.sum_const, hcard_e0, nsmul_eq_mul]
      norm_num
    rw [hrest]
    simp only [G, cTwoWitnessGame, θ, cTwoWitnessBids, ↓reduceIte]
    norm_num
  have hlt_ratio : G.welfare (marketAllocation D G.capacity θ) / G.welfare opt < 3 / 4 := by
    rw [hw_ne, hopt_w]
    norm_num
  exact ⟨hU, hopt, hne, hw_ne, hopt_w, hlt_ratio⟩

end RootPriceInstance

/-! ### 3. Boundary non-member of `𝒟` (`c = 1 / 2`, `D(p, θ) = θ * p ^ (-2)`) -/

section NonMemberBoundary

/-- For `c = 1 / 2 < 1`, `powerElasticityMechanism (1 / 2)` (`D(p, θ) = θ * p ^ (-2)`) satisfies
`IsSmoothMarketClearing` and demand surjectivity on `[0, ∞)`, yet fails price-anticipating payoff
concavity and therefore is not in `𝒟` (`¬ IsRegularMarketClearing`). -/
example :
    let D := powerElasticityMechanism (1 / 2)
    IsSmoothMarketClearing D ∧
    (∀ p > 0, ∀ d ≥ 0, ∃ θ ≥ 0, D p θ = d) ∧
    ¬ IsRegularMarketClearing D := by
  intro D
  have hc_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hsmooth : IsSmoothMarketClearing D := isSmoothMarketClearing_powerElasticity hc_pos
  have hsurj : ∀ p > 0, ∀ d ≥ 0, ∃ θ ≥ 0, D p θ = d := by
    intro p hp d hd
    refine ⟨d * p ^ (2 : ℝ), mul_nonneg hd (Real.rpow_nonneg hp.le _), ?_⟩
    dsimp only [D]
    rw [powerElasticityMechanism_apply, mul_assoc, ← Real.rpow_add hp,
      show (2 : ℝ) + -1 / (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one]
  refine ⟨hsmooth, hsurj, fun hreg => ?_⟩
  have hu : IsAdmissibleUtility (fun x => x) := by
    simpa only [one_mul] using KellyGame.isAdmissibleUtility_linear zero_lt_one
  have hconc := hreg.concaveOn_payoff_pos 2 le_rfl 1 zero_lt_one (fun x => x) hu 0 ![0, 0]
    (fun s hs => by
      fin_cases s
      · exact absurd rfl hs
      · rfl)
  set f : ℝ → ℝ :=
    fun t => marketPayoff D ⟨1, fun _ x => x⟩ (Function.update (![0, 0] : Fin 2 → ℝ) 0 t) 0
  have hf_eq : ∀ t > 0, f t = 1 - t ^ (1 / 2 : ℝ) := by
    intro t ht
    have hupd0 : ∀ s : Fin 2, 0 ≤ Function.update (![0, 0] : Fin 2 → ℝ) 0 t s := fun s => by
      fin_cases s <;> simp [ht.le]
    have hne : ∃ s : Fin 2, Function.update (![0, 0] : Fin 2 → ℝ) 0 t s ≠ 0 :=
      ⟨0, by simp [ht.ne']⟩
    have hsum : ∑ s : Fin 2, Function.update (![0, 0] : Fin 2 → ℝ) 0 t s = t := by
      simp [Fin.sum_univ_two]
    have hp : clearingPrice D 1 (Function.update (![0, 0] : Fin 2 → ℝ) 0 t) = t ^ (1 / 2 : ℝ) := by
      dsimp only [D]
      rw [clearingPrice_powerElasticity hc_pos (by decide) zero_lt_one hupd0 hne, hsum, div_one]
    have ha : marketAllocation D 1 (Function.update (![0, 0] : Fin 2 → ℝ) 0 t) 0 = 1 := by
      rw [marketAllocation_apply, hp, Function.update_self]
      dsimp only [D]
      rw [powerElasticityMechanism_apply, ← Real.rpow_mul ht.le,
        show (1 / 2 : ℝ) * (-1 / (1 / 2)) = -1 by norm_num, Real.rpow_neg_one,
        mul_inv_cancel₀ ht.ne']
    simp only [f, marketPayoff_apply, ha, hp, mul_one]
  have hf1 : f 1 = 0 := by rw [hf_eq 1 zero_lt_one, Real.one_rpow, sub_self]
  have hf4 : f 4 = -1 := by
    rw [hf_eq 4 (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num), show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    norm_num
  have hf16 : f 16 = -3 := by
    rw [hf_eq 16 (by norm_num), show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num), show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    norm_num
  have hineq := hconc.2 (mem_Ioi.mpr zero_lt_one) (mem_Ioi.mpr (by norm_num : (0 : ℝ) < 16))
    (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num)
  change (4 / 5 : ℝ) • f 1 + (1 / 5 : ℝ) • f 16 ≤ f ((4 / 5 : ℝ) • 1 + (1 / 5 : ℝ) • 16) at hineq
  simp only [smul_eq_mul, show (4 / 5 : ℝ) * 1 + (1 / 5) * 16 = 4 by norm_num] at hineq
  rw [hf1, hf4, hf16] at hineq
  linarith

end NonMemberBoundary

end CslibFrontierTests.GameTheory.KellyMarketClearing
