/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.Bandits.EXP3
import CslibFrontier.MachineLearning.OnlineLearning.Bandits.UCB1
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Checks for multi-armed bandits (`Bandits/{Basic,EXP3,UCB1}`): non-vacuous `K = 2` (`Bool`)
oblivious and stochastic bandit instances, single-arm partial-information weight updates,
importance-weighted unbiasedness on unequal probabilities, `UCB1` initialization and deterministic
tie-breaking boundary witnesses, and concrete small-horizon regret bounds for `EXP3` and `UCB1`. -/

namespace CslibFrontierTests.Bandits

open Finset MeasureTheory Real
open Cslib.MachineLearning.OnlineLearning.Bandits
open scoped BigOperators ENNReal

/-! ### `K = 2` oblivious bandit (`Bool`) and `EXP3` checks -/

/-- Non-vacuous 2-armed oblivious bandit: arm `false` pays `0` on even rounds and `1 / 2` on odd
rounds; arm `true` pays `1` on even rounds and `0` on odd rounds. -/
noncomputable def twoArmOblivious : ObliviousBandit Bool where
  loss t b := if b then (if t % 2 = 0 then 1 else 0) else (if t % 2 = 0 then 0 else 1 / 2)
  mem_unitInterval t b := by
    cases b <;> split_ifs <;> norm_num

/-- On an empty history, loss-based `EXP3` plays the uniform distribution `(1 / 2, 1 / 2)` on
`Bool`. -/
example (η : ℝ) (b : Bool) : exp3Prob η ([] : List (BanditStep Bool)) b = 1 / 2 := by
  simp [Fintype.card_bool]

/-- Partial-information boundary check: after observing `[⟨true, 1⟩]` at learning rate `η = 1 / 2`,
the unpulled arm `false` retains weight `1` while the pulled arm `true` (which had initial selection
probability `1 / 2`, hence importance-weighted loss `2`) has updated weight `exp (-1)`. -/
example :
    exp3Weight (1 / 2) ([⟨true, 1⟩] : List (BanditStep Bool)) false = 1 ∧
      exp3Weight (1 / 2) ([⟨true, 1⟩] : List (BanditStep Bool)) true = exp (-1) := by
  constructor
  · rw [show ([⟨true, 1⟩] : List (BanditStep Bool)) = [] ++ [⟨true, 1⟩] from rfl,
      exp3Weight_append_singleton, Cslib.MachineLearning.OnlineLearning.Experts.hedgeFactor_apply]
    norm_num [importanceWeightedEst_apply]
  · rw [show ([⟨true, 1⟩] : List (BanditStep Bool)) = [] ++ [⟨true, 1⟩] from rfl,
      exp3Weight_append_singleton, Cslib.MachineLearning.OnlineLearning.Experts.hedgeFactor_apply]
    norm_num [importanceWeightedEst_apply, Fintype.card_bool]

/-- Importance-weighted estimator unbiasedness on a non-uniform 2-arm distribution
`(1 / 3, 2 / 3)`. -/
example (v : Bool → ℝ) (i : Bool) :
    (∑ a : Bool, (if a then (1 / 3 : ℝ) else 2 / 3) *
      importanceWeightedEst (fun b : Bool => if b then (1 / 3 : ℝ) else 2 / 3) ⟨a, v a⟩ i) =
      v i :=
  sum_importanceWeightedEst v (by cases i <;> norm_num)

/-- Pseudo-regret equals expected hindsight regret on `twoArmOblivious` for any policy and
horizon. -/
example (pol : RandomizedPolicy Bool) (T : ℕ) :
    twoArmOblivious.pseudoRegret pol T =
      ∑ traj : Fin T → Bool, (trajectoryPMF pol twoArmOblivious.loss T traj).toReal *
        ((∑ t : Fin T, twoArmOblivious.loss t (traj t)) - twoArmOblivious.bestCumLoss T) :=
  twoArmOblivious.pseudoRegret_eq_expectedRegret pol T

/-- Concrete `K = 2`, `T = 2` horizon check for loss-based `EXP3`: pseudo-regret is at most
`√(8 ln 2)`. -/
example :
    twoArmOblivious.pseudoRegret (exp3Policy (exp3Rate 2 2)) 2 ≤ √(8 * log 2) := by
  have h := exp3_pseudoRegret_le_sqrt twoArmOblivious 2
  simpa [Fintype.card_bool, show (2 : ℝ) * 2 * 2 = 8 by norm_num] using h

/-- Concrete `K = 2`, `T = 4` horizon check for loss-based `EXP3`: pseudo-regret is at most
`4 √(ln 2)`. -/
example :
    twoArmOblivious.pseudoRegret (exp3Policy (exp3Rate 2 4)) 4 ≤ 4 * √(log 2) := by
  have h := exp3_pseudoRegret_le_sqrt twoArmOblivious 4
  have hcard : Fintype.card Bool = 2 := Fintype.card_bool
  rw [hcard] at h
  refine h.trans_eq ?_
  calc √((2 : ℝ) * (4 : ℕ) * (2 : ℕ) * log (2 : ℕ))
      = √((4 : ℝ) ^ 2 * log 2) := by norm_num
    _ = 4 * √(log 2) := by rw [sqrt_mul (by positivity), sqrt_sq (by positivity)]

/-- Concrete `K = 2`, `T = 4` horizon check for reward-based `γ`-mixed `Exp3`
([AuerCesaBianchiFreundSchapire2002, Corollary 3.2]). -/
example :
    obliviousRewardRegret (exp3GammaPolicy (exp3GammaRate 2 4))
      (fun t b => 1 - twoArmOblivious.loss t b) 4 ≤
      2 * √(8 * (exp 1 - 1) * log 2) := by
  have hg : ∀ s < 4, ∀ a : Bool, 1 - twoArmOblivious.loss s a ∈ Set.Icc (0 : ℝ) 1 := by
    intro s _ a
    have h01 := twoArmOblivious.mem_unitInterval s a
    exact ⟨by linarith [h01.2], by linarith [h01.1]⟩
  have h := exp3Gamma_rewardRegret_le_sqrt (ι := Bool) 4 hg
  simpa only [Fintype.card_bool, Nat.cast_ofNat,
    show (exp 1 - 1) * 4 * 2 * log 2 = 8 * (exp 1 - 1) * log 2 by ring] using h

/-! ### `K = 2` stochastic bandit (`Bool`) and `UCB1` checks -/

/-- Fair `{0, 1}` Bernoulli coin law on `ℝ`: `(1 / 2) • δ_0 + (1 / 2) • δ_1`. -/
noncomputable def bernoulliHalfLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)

instance : IsProbabilityMeasure bernoulliHalfLaw where
  measure_univ := by
    simp only [bernoulliHalfLaw, one_div, FunLike.coe_add, smul_apply, Pi.add_apply,
      measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.inv_two_add_inv_two

/-- Non-vacuous 2-armed stochastic bandit: arm `false` is a genuinely non-deterministic fair
`{0, 1}` Bernoulli coin (`mean = 1 / 2`), and arm `true` is `δ_1` (`mean = 1`), giving
`bestMean = 1`, `gap false = 1 / 2 > 0`, and `gap true = 0`. -/
noncomputable def twoArmStochastic : StochasticBandit Bool where
  law b := if b then Measure.dirac (1 : ℝ) else bernoulliHalfLaw
  isProb b := by cases b <;> infer_instance
  mem_unitInterval b := by
    have h0 : ∀ᵐ x ∂Measure.dirac (0 : ℝ), x ∈ Set.Icc (0 : ℝ) 1 :=
      (ae_dirac_iff (p := (· ∈ Set.Icc (0 : ℝ) 1)) measurableSet_Icc).mpr (by norm_num)
    have h1 : ∀ᵐ x ∂Measure.dirac (1 : ℝ), x ∈ Set.Icc (0 : ℝ) 1 :=
      (ae_dirac_iff (p := (· ∈ Set.Icc (0 : ℝ) 1)) measurableSet_Icc).mpr (by norm_num)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, bernoulliHalfLaw, ae_add_measure_iff]
      exact ⟨Measure.ae_smul_measure h0 _, Measure.ae_smul_measure h1 _⟩
    · simpa only [↓reduceIte] using h1

theorem twoArmStochastic_mean_false : twoArmStochastic.mean false = 1 / 2 := by
  rw [StochasticBandit.mean_def]
  change ∫ x : ℝ, x ∂bernoulliHalfLaw = 1 / 2
  rw [bernoulliHalfLaw]
  have hint0 : Integrable (fun x : ℝ => x) ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (a := (0 : ℝ)) (f := id) (by simp)).smul_measure (by norm_num)
  have hint1 : Integrable (fun x : ℝ => x) ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (a := (1 : ℝ)) (f := id) (by simp)).smul_measure (by norm_num)
  rw [integral_add_measure hint0 hint1, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  norm_num

theorem twoArmStochastic_mean_true : twoArmStochastic.mean true = 1 := by
  rw [StochasticBandit.mean_def]
  change ∫ x : ℝ, x ∂Measure.dirac (1 : ℝ) = 1
  simp [integral_dirac]

theorem twoArmStochastic_bestMean : twoArmStochastic.bestMean = 1 := by
  apply le_antisymm
  · exact (twoArmStochastic.bestMean_mem_Icc).2
  · have h := twoArmStochastic.mean_le_bestMean true
    linarith [twoArmStochastic_mean_true]

theorem twoArmStochastic_gap_false : twoArmStochastic.gap false = 1 / 2 := by
  rw [twoArmStochastic.gap_def, twoArmStochastic_bestMean, twoArmStochastic_mean_false]
  norm_num

theorem twoArmStochastic_gap_true : twoArmStochastic.gap true = 0 := by
  rw [twoArmStochastic.gap_def, twoArmStochastic_bestMean, twoArmStochastic_mean_true]
  norm_num

/-- `UCB1` initialization and tie-breaking boundary witnesses on `Bool` (`false < true`):
1. Empty history `[]`: pulls `false` (least unpulled arm).
2. After `[⟨false, 1 / 2⟩]`: pulls `true` (only remaining unpulled arm).
3. Tie-breaking boundary `[⟨false, 1 / 2⟩, ⟨true, 1 / 2⟩]`: both arms have `pullCount = 1` and
   equal `ucb1Index`, so deterministic tie-breaking chooses `false`.
4. Strict empirical-mean separation `[⟨false, 0⟩, ⟨true, 1⟩]`: both arms have equal confidence
   bonus `√(2 ln 2)`, so `UCB1` chooses `true`. -/
example :
    ucb1Policy.choose ([] : List (BanditStep Bool)) = false ∧
      ucb1Policy.choose ([⟨false, 1 / 2⟩] : List (BanditStep Bool)) = true ∧
      ucb1Policy.choose ([⟨false, 1 / 2⟩, ⟨true, 1 / 2⟩] : List (BanditStep Bool)) = false ∧
      ucb1Policy.choose ([⟨false, 0⟩, ⟨true, 1⟩] : List (BanditStep Bool)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmem : false ∈ unpulledArms ([] : List (BanditStep Bool)) := by simp
    rw [ucb1Policy_choose_of_nonempty ⟨false, hmem⟩]
    exact le_antisymm (min'_le _ false hmem) (Bool.false_le _)
  · have hmem_t : true ∈ unpulledArms ([⟨false, 1 / 2⟩] : List (BanditStep Bool)) := by simp
    have hnot_f : false ∉ unpulledArms ([⟨false, 1 / 2⟩] : List (BanditStep Bool)) := by simp
    rw [ucb1Policy_choose_of_nonempty ⟨true, hmem_t⟩]
    have hmin := min'_mem (unpulledArms ([⟨false, 1 / 2⟩] : List (BanditStep Bool))) ⟨true, hmem_t⟩
    cases h : (unpulledArms ([⟨false, 1 / 2⟩] : List (BanditStep Bool))).min' ⟨true, hmem_t⟩
    · rw [h] at hmin
      exact False.elim (hnot_f hmin)
    · rfl
  · let hist : List (BanditStep Bool) := [⟨false, 1 / 2⟩, ⟨true, 1 / 2⟩]
    have hun : ¬ (unpulledArms hist).Nonempty := by
      rintro ⟨b, hb⟩
      rw [mem_unpulledArms] at hb
      cases b <;> simp [hist] at hb
    have heq_idx : ucb1Index hist true = ucb1Index hist false := by
      simp [hist, ucb1Index_def, empiricalMean_def]
    refine le_antisymm (ucb1Policy_choose_le_of_unpulled_empty hun fun j => ?_) (Bool.false_le _)
    cases j <;> simp [heq_idx]
  · let hist : List (BanditStep Bool) := [⟨false, 0⟩, ⟨true, 1⟩]
    have hun : ¬ (unpulledArms hist).Nonempty := by
      rintro ⟨b, hb⟩
      rw [mem_unpulledArms] at hb
      cases b <;> simp [hist] at hb
    have hlt_idx : ucb1Index hist false < ucb1Index hist true := by
      simp [hist, ucb1Index_def, empiricalMean_def]
    have hmax := ucb1Index_le_choose_of_unpulled_empty hun true
    cases hch : ucb1Policy.choose hist
    · rw [hch] at hmax
      linarith
    · rfl

/-- Concrete `K = 2`, `T = 10` pull-count bound for suboptimal arm `false` (`Δ = 1 / 2`):
`𝔼[N_false(10)] ≤ 32 ln 10 + 2`. -/
example :
    twoArmStochastic.expectedPulls ucb1Policy 10 false ≤ 32 * log 10 + 2 := by
  have hgap : 0 < twoArmStochastic.gap false := by
    rw [twoArmStochastic_gap_false]
    norm_num
  have h := ucb1_expectedPulls_le_add_two twoArmStochastic (T := 10) (by omega) hgap
  rw [twoArmStochastic_gap_false] at h
  norm_num at h
  linarith

/-- Concrete `K = 2`, `T = 10` instance-dependent regret bound
([AuerCesaBianchiFischer2002, Theorem 1]):
`twoArmStochastic.stochasticRegret ucb1Policy 10 ≤ 16 ln 10 + (1 + π² / 3) / 2`. -/
example :
    twoArmStochastic.stochasticRegret ucb1Policy 10 ≤
      16 * log 10 + (1 + π ^ 2 / 3) / 2 := by
  have h := ucb1_stochasticRegret_le twoArmStochastic (T := 10) (by omega)
  have hfilter : (univ.filter fun b : Bool => 0 < twoArmStochastic.gap b) = {false} := by
    ext b
    cases b <;> simp [twoArmStochastic_gap_false, twoArmStochastic_gap_true]
  rw [hfilter, sum_singleton, Fintype.sum_bool, twoArmStochastic_gap_false,
    twoArmStochastic_gap_true] at h
  norm_num at h
  linarith

/-- Concrete `K = 2`, `T = 2` and `T = 10` minimax regret bounds
(`ucb1_stochasticRegret_le_sqrt`). -/
example :
    twoArmStochastic.stochasticRegret ucb1Policy 2 ≤ 2 * √(12 * log 2) ∧
      twoArmStochastic.stochasticRegret ucb1Policy 10 ≤ 2 * √(60 * log 10) := by
  constructor
  · have h := ucb1_stochasticRegret_le_sqrt twoArmStochastic (T := 2) le_rfl
    simpa [Fintype.card_bool, show (3 : ℝ) * 2 * 2 = 12 by norm_num] using h
  · have h := ucb1_stochasticRegret_le_sqrt twoArmStochastic (T := 10) (by omega)
    simpa [Fintype.card_bool, show (3 : ℝ) * 2 * 10 = 60 by norm_num] using h

/-! ### Boundary checks: `T = 0`, `K = 1` (`Unit`), and `γ = 1` -/

/-- `T = 0` boundary check for both loss-based `EXP3` and reward-based `Exp3`. -/
example :
    twoArmOblivious.pseudoRegret (exp3Policy (exp3Rate 2 0)) 0 ≤ 0 ∧
      obliviousRewardRegret (exp3GammaPolicy (exp3GammaRate 2 0))
        (fun t b => 1 - twoArmOblivious.loss t b) 0 ≤ 0 := by
  constructor
  · simpa [Fintype.card_bool] using exp3_pseudoRegret_le_sqrt twoArmOblivious 0
  · have hg : ∀ s < 0, ∀ a : Bool, 1 - twoArmOblivious.loss s a ∈ Set.Icc (0 : ℝ) 1 :=
      fun s hs => absurd hs (Nat.not_lt_zero s)
    simpa [Fintype.card_bool] using exp3Gamma_rewardRegret_le_sqrt (ι := Bool) 0 hg

/-- `γ = 1` pure-exploration boundary check for reward-based `Exp3`
(`exp3Gamma_rewardRegret_le`). -/
example :
    let g : ℕ → Bool → ℝ := fun t b => 1 - twoArmOblivious.loss t b
    obliviousRewardRegret (exp3GammaPolicy 1) g 4 ≤
      (exp 1 - 1) * bestCumReward g 4 + 2 * log 2 := by
  intro g
  have hg : ∀ s < 4, ∀ a : Bool, g s a ∈ Set.Icc (0 : ℝ) 1 := fun s _ a => by
    have h01 := twoArmOblivious.mem_unitInterval s a
    exact ⟨by linarith [h01.2], by linarith [h01.1]⟩
  simpa [Fintype.card_bool] using
    exp3Gamma_rewardRegret_le (ι := Bool) (γ := 1) zero_lt_one le_rfl 4 hg

/-- `K = 1` (`Unit`) boundary check for loss-based `EXP3` and reward-based `Exp3`:
single-arm regret is bounded by `0`. -/
example (T : ℕ) :
    let E : ObliviousBandit Unit := ⟨fun _ _ => 1 / 2, fun _ _ => by norm_num⟩
    E.pseudoRegret (exp3Policy (exp3Rate 1 T)) T ≤ 0 ∧
      obliviousRewardRegret (exp3GammaPolicy (exp3GammaRate 1 T))
        (fun _ (_ : Unit) => (1 / 2 : ℝ)) T ≤ 0 := by
  intro E
  constructor
  · simpa using exp3_pseudoRegret_le_sqrt E T
  · simpa using exp3Gamma_rewardRegret_le_sqrt (ι := Unit) (g := fun _ _ => 1 / 2) T
      fun _ _ _ => by norm_num

/-- `K = 1` (`Unit`) boundary check for `UCB1` on a deterministic single-arm stochastic bandit
(for any horizon `T : ℕ`, including `T = 0`). -/
example (T : ℕ) :
    let B : StochasticBandit Unit :=
      ⟨fun _ => Measure.dirac (1 / 2 : ℝ), fun _ => inferInstance,
        fun _ => (ae_dirac_iff (p := (· ∈ Set.Icc (0 : ℝ) 1)) measurableSet_Icc).mpr
          (by norm_num)⟩
    B.stochasticRegret ucb1Policy T = 0 := by
  intro B
  rw [B.stochasticRegret_eq_pseudoRegret ucb1Policy_isMeasurable T, B.pseudoRegret_def,
    Fintype.sum_unique]
  obtain ⟨a, _, ha⟩ := B.exists_optimal_arm
  have h0 : B.gap () = 0 := by simpa [Subsingleton.elim a ()] using ha
  simp [h0]

/-- `T = 0` boundary check for `StochasticBandit.stochasticRegret` on `twoArmStochastic`. -/
example : twoArmStochastic.stochasticRegret ucb1Policy 0 = 0 := by
  rw [twoArmStochastic.stochasticRegret_eq_pseudoRegret ucb1Policy_isMeasurable 0,
    twoArmStochastic.pseudoRegret_def]
  simp [StochasticBandit.expectedPulls_def]

end CslibFrontierTests.Bandits
