/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.MachineLearning.PACBayes.Catoni
import CslibFrontier.MachineLearning.PACBayes.Inversion
import CslibFrontier.Probability.DonskerVaradhan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.privateModule false

/-!
# Checked tests for Donsker–Varadhan, Gibbs posteriors, Catoni bounds, and `binaryKL` inversions

Ordinary-import `module` client (zero `import all`) verifying:

1. **Donsker–Varadhan / Gibbs optimality (`CslibFrontier.Probability.DonskerVaradhan`)**: on `Bool`
   equipped with the uniform prior `P = (1/2) δ_false + (1/2) δ_true`, `P.tilted f` hits exact
   equality in the change-of-measure bound (`toReal_klDiv_tilted_self`), strictly minimizes the free
   energy `∫ g ∂μ + KL(μ ‖ P) / β` against a non-tilted point mass `Measure.dirac false` (negative
   witness), and matches `log_integral_exp_eq_sSup` / `toReal_klDiv_eq_sSup`.
2. **Catoni's potential and PAC-Bayes bounds on an *uncountable* hypothesis space (`Catoni`)**:
   instantiates `measure_pi_exists_catoni_integral_risk_gt`,
   `measure_pi_exists_catoni_linear_integral_risk_gt`,
   `measure_pi_exists_realizable_integral_risk_gt`,
   `measure_pi_exists_hoeffding_integral_risk_gt`,
   `measure_pi_exists_integral_risk_gt_of_measurable`,
   `measure_pi_gibbs_fixed_oracle_gt`, and `measure_pi_gibbs_oracle_gt` on the **uncountable**
   threshold class `Θ = ℝ` equipped with the uniform Lebesgue prior `volume.restrict (Icc 0 1)`
   (a space where the `[Countable ι]` form in `CslibFrontier.MachineLearning.PACBayes.Basic`
   does not apply!).
3. **Catoni potential identity check**: exact `catoniPhi` boundary values at `p = 0, 1`,
   `catoniInv_catoniPhi` at `c = 2, p = 1/3`, and `catoniPhi_le_self` at `c = 1, p = 1/2`.
4. **Analytical `binaryKL` inversions (`Inversion`)**: numerical strict comparisons showing the
   fast-rate quadratic bound `q + c + √(c² + 2 q c)` improves on Pinsker `q + √(c / 2)` at small
   empirical risk (`q = 0, c = 1 / 10`), and instantiations of
   `measure_pi_exists_pinsker_risk_gt_of_binaryKL`,
   `measure_pi_exists_fastRate_risk_gt_of_binaryKL`,
   `measure_pi_exists_tolstikhin_risk_gt_of_binaryKL`, and
   `measure_pi_exists_zero_risk_gt_of_binaryKL`.
-/

namespace CslibFrontierTests.PACBayesCatoni

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open Cslib.MachineLearning Cslib.MachineLearning.PACBayes Cslib.Probability
open scoped ENNReal

/-! ### 1. Finite Gibbs posterior and Donsker–Varadhan checks -/

private noncomputable def fairBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

private instance : IsProbabilityMeasure fairBool := by
  refine ⟨?_⟩
  simp only [fairBool, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply, mem_univ, indicator_of_mem, Pi.one_apply, mul_one, one_div]
  exact ENNReal.inv_two_add_inv_two

private theorem fairBool_false_ne_zero : fairBool {false} ≠ 0 := by
  simp [fairBool]

private theorem fairBool_integral (f : Bool → ℝ) :
    ∫ b, f b ∂fairBool = (f false + f true) / 2 := by
  have h1 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac false) := by
    have : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac false) := by
      refine ⟨?_⟩; simp
    exact Integrable.of_finite
  have h2 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac true) := by
    have : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac true) := by
      refine ⟨?_⟩; simp
    exact Integrable.of_finite
  simp only [fairBool, integral_add_measure h1 h2, integral_smul_measure, integral_dirac,
    smul_eq_mul]
  norm_num
  ring

/-- Equality check for Donsker–Varadhan on `fairBool` tilted by `f b = if b then 1 else 0`. -/
example :
    let f : Bool → ℝ := fun b => if b then 1 else 0
    (klDiv (fairBool.tilted f) fairBool).toReal =
      ∫ b, f b ∂(fairBool.tilted f) - log ((1 + exp 1) / 2) := by
  intro f
  have h1 : Integrable (fun b => exp (f b)) fairBool := Integrable.of_finite
  have : IsProbabilityMeasure (fairBool.tilted f) := isProbabilityMeasure_tilted h1
  have h2 : Integrable f (fairBool.tilted f) := Integrable.of_finite
  rw [toReal_klDiv_tilted_self h1 h2, fairBool_integral]
  simp [f]

/-- Strict non-optimality (negative witness): on loss `g b = if b then 1 else 0`, the point mass
`Measure.dirac false` has strictly larger free energy than the Gibbs posterior
`fairBool.tilted (fun b => -g b)`. -/
example :
    let g : Bool → ℝ := fun b => if b then 1 else 0
    let Qhat := fairBool.tilted fun b => -1 * g b
    ∫ b, g b ∂Qhat + (klDiv Qhat fairBool).toReal / 1 <
      ∫ b, g b ∂Measure.dirac false + (klDiv (Measure.dirac false) fairBool).toReal / 1 := by
  intro g Qhat
  have hexp : Integrable (fun b => exp (-1 * g b)) fairBool := Integrable.of_finite
  have hkl_d : klDiv (Measure.dirac false) fairBool ≠ ⊤ :=
    klDiv_dirac_ne_top fairBool_false_ne_zero
  have hopt := freeEnergy_tilted_le (μ := Measure.dirac false) (ν := fairBool) hkl_d one_pos
    Integrable.of_finite hexp (by
      have : IsProbabilityMeasure Qhat := isProbabilityMeasure_tilted hexp
      exact Integrable.of_finite)
  refine lt_of_le_of_ne hopt fun heq => ?_
  have : IsProbabilityMeasure Qhat := isProbabilityMeasure_tilted hexp
  have hval : ∫ b, g b ∂Qhat + (klDiv Qhat fairBool).toReal / 1 =
      -log (∫ b, exp (-1 * g b) ∂fairBool) / 1 := by
    have h1 := toReal_klDiv_tilted_self hexp (Integrable.of_finite.const_mul (-1))
    rw [integral_const_mul] at h1
    linarith
  have hmem : Measure.dirac false = Qhat :=
    (freeEnergy_eq_tilted_iff hkl_d one_pos Integrable.of_finite hexp).mp (by linarith)
  have hfa0 : fairBool {true} = 0 :=
    absolutelyContinuous_tilted hexp (show Qhat {true} = 0 by rw [← hmem]; simp)
  have hfa : fairBool {true} = 1 / 2 := by simp [fairBool]
  rw [hfa] at hfa0
  simp at hfa0

/-- Checking `log_integral_exp_eq_sSup` recovers `log ((1 + exp 1) / 2)`. -/
example :
    let f : Bool → ℝ := fun b => if b then 1 else 0
    sSup { r : ℝ | ∃ μ : Measure Bool, IsProbabilityMeasure μ ∧ klDiv μ fairBool ≠ ⊤ ∧
      Integrable f μ ∧ r = ∫ x, f x ∂μ - (klDiv μ fairBool).toReal } =
      log ((1 + exp 1) / 2) := by
  intro f
  have h1 : Integrable (fun b => exp (f b)) fairBool := Integrable.of_finite
  have : IsProbabilityMeasure (fairBool.tilted f) := isProbabilityMeasure_tilted h1
  rw [← log_integral_exp_eq_sSup h1 Integrable.of_finite, fairBool_integral]
  simp [f]

/-- Checking `toReal_klDiv_eq_sSup` recovers `KL(δ_false ‖ fairBool) = log 2`. -/
example :
    sSup { r : ℝ | ∃ f : Bool → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧
      r = ∫ x, f x ∂Measure.dirac false - log (∫ x, exp (f x) ∂fairBool) } = log 2 := by
  have hkl : klDiv (Measure.dirac false) fairBool ≠ ⊤ :=
    klDiv_dirac_ne_top fairBool_false_ne_zero
  rw [← toReal_klDiv_eq_sSup hkl, toReal_klDiv_dirac fairBool_false_ne_zero]
  have hf : fairBool.real {false} = 1 / 2 := by
    rw [measureReal_def]; simp [fairBool]
  rw [hf, one_div, log_inv, neg_neg]

/-! ### 2. Catoni potential identities & uncountable `Θ = ℝ` witness -/

example : catoniPhi 1 0 = 0 := catoniPhi_zero 1
example : catoniPhi 1 1 = 1 := catoniPhi_one one_ne_zero
example : catoniInv 2 (catoniPhi 2 (1 / 3)) = 1 / 3 :=
  catoniInv_catoniPhi (by norm_num) (by norm_num)
example : catoniPhi 1 (1 / 2) ≤ 1 / 2 :=
  catoniPhi_le_self one_pos (by norm_num)

/-- Uniform probability measure on `[0, 1] ⊆ ℝ` (an **uncountable** prior). -/
private noncomputable def unitIntervalPrior : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure unitIntervalPrior := by
  refine ⟨?_⟩
  rw [unitIntervalPrior, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- Threshold loss `ℓ θ (x, y) = 1_{decide (x ≤ θ) ≠ y}` on the uncountable space `Θ = ℝ`. -/
private noncomputable def threshLoss (θ : ℝ) (z : ℝ × Bool) : ℝ :=
  if (z.1 ≤ θ) ↔ (z.2 = true) then 0 else 1

private theorem measurable_threshLoss : Measurable (Function.uncurry threshLoss) := by
  have h1 : MeasurableSet {p : ℝ × (ℝ × Bool) | p.2.1 ≤ p.1} :=
    measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst
  have h2 : MeasurableSet {p : ℝ × (ℝ × Bool) | p.2.2 = true} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton true)
  have hset : MeasurableSet {p : ℝ × (ℝ × Bool) | (p.2.1 ≤ p.1) ↔ (p.2.2 = true)} := by
    have heq : {p : ℝ × (ℝ × Bool) | (p.2.1 ≤ p.1) ↔ (p.2.2 = true)} =
        ({p | p.2.1 ≤ p.1} ∩ {p | p.2.2 = true}) ∪
          ({p | p.2.1 ≤ p.1}ᶜ ∩ {p | p.2.2 = true}ᶜ) := by
      ext p; simp [iff_iff_and_or_not_and_not]
    rw [heq]
    exact (h1.inter h2).union (h1.compl.inter h2.compl)
  exact measurable_const.ite hset measurable_const

private theorem threshLoss_mem_Icc (θ : ℝ) (z : ℝ × Bool) : threshLoss θ z ∈ Icc (0 : ℝ) 1 := by
  dsimp [threshLoss]
  split_ifs <;> norm_num

/-- Non-vacuous **Catoni (2007)** instantiation on the **uncountable** space `Θ = ℝ` with
Lebesgue prior `volume.restrict [0, 1]` and threshold classifiers (`m = 10`, `c = 1`, `δ = 1/20`).
-/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧
        catoniInv 1 (∫ θ, empiricalRisk threshLoss S θ ∂Q +
          ((klDiv Q unitIntervalPrior).toReal + log (1 / (1 / 20))) / (1 * 10)) <
        ∫ θ, trueRisk threshLoss D θ ∂Q} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_exists_catoni_integral_risk_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) one_pos unitIntervalPrior (by norm_num)

/-- Non-vacuous linearized **Catoni** and **PAC-Bayes–Hoeffding** bounds on `Θ = ℝ`. -/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧
        (1 / (1 - exp (-1))) * ∫ θ, empiricalRisk threshLoss S θ ∂Q +
          ((klDiv Q unitIntervalPrior).toReal + log (1 / (1 / 20))) / (10 * (1 - exp (-1))) <
        ∫ θ, trueRisk threshLoss D θ ∂Q} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_exists_catoni_linear_integral_risk_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) one_pos unitIntervalPrior (by norm_num)

example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧ ∫ θ, empiricalRisk threshLoss S θ ∂Q +
        ((klDiv Q unitIntervalPrior).toReal + log (1 / (1 / 20))) / 4 + 4 / (8 * 10) <
        ∫ θ, trueRisk threshLoss D θ ∂Q} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_exists_hoeffding_integral_risk_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) (by norm_num : (0 : ℝ) < 4) unitIntervalPrior (by norm_num)

/-- Fixed-oracle **Gibbs posterior** inequality on uncountable `Θ = ℝ` (with `Q = P`). -/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S |
      ∫ θ, trueRisk threshLoss D θ ∂unitIntervalPrior +
        (klDiv unitIntervalPrior unitIntervalPrior).toReal / 4 + 4 / (4 * 10) +
        2 * log (2 / (1 / 20)) / 4 <
      ∫ θ, trueRisk threshLoss D θ ∂(unitIntervalPrior.tilted fun θ =>
        -4 * empiricalRisk threshLoss S θ)} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_gibbs_fixed_oracle_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) (by norm_num : (0 : ℝ) < 4) unitIntervalPrior unitIntervalPrior (by simp)
    (by norm_num)

/-- Non-vacuous **realizable `O(1 / m)`** PAC-Bayes bound on uncountable `Θ = ℝ`. -/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧ ∫ θ, empiricalRisk threshLoss S θ ∂Q = 0 ∧
        ((klDiv Q unitIntervalPrior).toReal + log (1 / (1 / 20))) / 10 <
        ∫ θ, trueRisk threshLoss D θ ∂Q} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_exists_realizable_integral_risk_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) unitIntervalPrior (by norm_num)

/-- Non-vacuous **Gibbs posterior uniform oracle inequality** on uncountable `Θ = ℝ`. -/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧
        ∫ θ, trueRisk threshLoss D θ ∂Q + 2 * (klDiv Q unitIntervalPrior).toReal / 4 +
          4 / (4 * 10) + 2 * log (2 / (1 / 20)) / 4 <
        ∫ θ, trueRisk threshLoss D θ ∂(unitIntervalPrior.tilted fun θ =>
          -4 * empiricalRisk threshLoss S θ)} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_gibbs_oracle_gt measurable_threshLoss threshLoss_mem_Icc
    (by decide) (by norm_num : (0 : ℝ) < 4) unitIntervalPrior (by norm_num)

/-- Non-vacuous **general-measurable McAllester bound** on uncountable `Θ = ℝ`. -/
example (D : Measure (ℝ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10 => D) {S | ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧
      klDiv Q unitIntervalPrior ≠ ⊤ ∧
        ∫ θ, empiricalRisk threshLoss S θ ∂Q +
          sqrt (((klDiv Q unitIntervalPrior).toReal + log (sqrt 10 / (1 / 20))) /
            (2 * ((10 : ℝ) - 1))) <
        ∫ θ, trueRisk threshLoss D θ ∂Q} ≤ ENNReal.ofReal (1 / 20) :=
  measure_pi_exists_integral_risk_gt_of_measurable measurable_threshLoss threshLoss_mem_Icc
    (by decide) unitIntervalPrior (by norm_num)

/-! ### 3. `binaryKL` inversions and fast-rate separation over Pinsker -/

/-- At `q = 0` and `c = 1 / 10`, the fast-rate quadratic bound `q + c + √(c² + 2 q c) = 0.2`
strictly beats Pinsker's `q + √(c / 2) = √(0.05) ≈ 0.2236`. -/
example :
    (0 : ℝ) + (1 / 10) + sqrt ((1 / 10 : ℝ) ^ 2 + 2 * 0 * (1 / 10)) <
      0 + sqrt ((1 / 10 : ℝ) / 2) := by
  have harg : (1 / 10 : ℝ) ^ 2 + 2 * 0 * (1 / 10) = (1 / 10 : ℝ) ^ 2 := by ring
  rw [harg, sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  have hlt : (1 / 5 : ℝ) < sqrt ((1 / 10 : ℝ) / 2) := by
    have h := sqrt_lt_sqrt (sq_nonneg (1 / 5 : ℝ)) (by norm_num : (1 / 5 : ℝ) ^ 2 < (1 / 10) / 2)
    rwa [sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 5)] at h
  linarith

/-- Concrete Bernoulli Pinsker and Bernstein-quadratic inequalities at `q = 1 / 4`, `p = 1 / 2`. -/
example : 2 * ((1 / 4 : ℝ) - 1 / 2) ^ 2 ≤ binaryKL (1 / 4) (1 / 2) :=
  two_mul_sq_le_binaryKL (by norm_num) (by norm_num) (by norm_num)

example : ((1 / 2 : ℝ) - 1 / 4) ^ 2 / (2 * (1 / 2)) ≤ binaryKL (1 / 4) (1 / 2) :=
  sub_sq_div_two_mul_le_binaryKL (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Instantiations of the three explicit `PAC-Bayes-kl` inversion corollaries on `Bool`. -/
example (D : Measure Bool) [IsProbabilityMeasure D] :
    let ℓ : Bool → Bool → ℝ := fun b z => if b = z then 0 else 1
    Measure.pi (fun _ : Fin 8 => D) {S | ∃ Q : Measure Bool, IsProbabilityMeasure Q ∧
      klDiv Q fairBool ≠ ⊤ ∧ ∫ b, empiricalRisk ℓ S b ∂Q +
        sqrt (((klDiv Q fairBool).toReal + log ((8 + 1) / (1 / 10))) / (2 * 8)) <
        ∫ b, trueRisk ℓ D b ∂Q} ≤ ENNReal.ofReal (1 / 10) :=
  measure_pi_exists_pinsker_risk_gt_of_binaryKL
    (fun _ => measurable_of_countable _) (fun _ _ => by split_ifs <;> norm_num)
    (by decide) fairBool (by norm_num)

example (D : Measure Bool) [IsProbabilityMeasure D] :
    let ℓ : Bool → Bool → ℝ := fun b z => if b = z then 0 else 1
    Measure.pi (fun _ : Fin 8 => D) {S | ∃ Q : Measure Bool, IsProbabilityMeasure Q ∧
      klDiv Q fairBool ≠ ⊤ ∧
        let q := ∫ b, empiricalRisk ℓ S b ∂Q
        let c := ((klDiv Q fairBool).toReal + log ((8 + 1) / (1 / 10))) / 8
        q + c + sqrt (c ^ 2 + 2 * q * c) < ∫ b, trueRisk ℓ D b ∂Q} ≤ ENNReal.ofReal (1 / 10) :=
  measure_pi_exists_fastRate_risk_gt_of_binaryKL
    (fun _ => measurable_of_countable _) (fun _ _ => by split_ifs <;> norm_num)
    (by decide) fairBool (by norm_num)

example (D : Measure Bool) [IsProbabilityMeasure D] :
    let ℓ : Bool → Bool → ℝ := fun b z => if b = z then 0 else 1
    Measure.pi (fun _ : Fin 8 => D) {S | ∃ Q : Measure Bool, IsProbabilityMeasure Q ∧
      klDiv Q fairBool ≠ ⊤ ∧
        let q := ∫ b, empiricalRisk ℓ S b ∂Q
        let c := ((klDiv Q fairBool).toReal + log ((8 + 1) / (1 / 10))) / 8
        q + sqrt (2 * q * c) + 2 * c < ∫ b, trueRisk ℓ D b ∂Q} ≤ ENNReal.ofReal (1 / 10) :=
  measure_pi_exists_tolstikhin_risk_gt_of_binaryKL
    (fun _ => measurable_of_countable _) (fun _ _ => by split_ifs <;> norm_num)
    (by decide) fairBool (by norm_num)

example (D : Measure Bool) [IsProbabilityMeasure D] :
    let ℓ : Bool → Bool → ℝ := fun b z => if b = z then 0 else 1
    Measure.pi (fun _ : Fin 8 => D) {S | ∃ Q : Measure Bool, IsProbabilityMeasure Q ∧
      klDiv Q fairBool ≠ ⊤ ∧ ∫ b, empiricalRisk ℓ S b ∂Q = 0 ∧
        1 - exp (-(((klDiv Q fairBool).toReal + log ((8 + 1) / (1 / 10))) / 8)) <
          ∫ b, trueRisk ℓ D b ∂Q} ≤ ENNReal.ofReal (1 / 10) :=
  measure_pi_exists_zero_risk_gt_of_binaryKL
    (fun _ => measurable_of_countable _) (fun _ _ => by split_ifs <;> norm_num)
    (by decide) fairBool (by norm_num)

end CslibFrontierTests.PACBayesCatoni
