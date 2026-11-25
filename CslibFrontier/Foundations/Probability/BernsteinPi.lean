/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.BennettStep
public import Mathlib.MeasureTheory.Constructions.Pi
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bennett, Bernstein, and Freedman inequalities under a product measure

Variance-sensitive counterparts to `CslibFrontier.Foundations.Probability.AzumaPi` for adapted
supermartingale differences `Y i : (∀ j, α j) → ℝ` over a finite linearly ordered index type `ι`
under `Measure.pi μ`:

* `Y i` does not depend on coordinates `j > i`;
* `∫ z, Y i (Function.update v i z) ∂μ i ≤ 0`;
* `Y i v ≤ b` (one-sided upper bound);
* `∫ z, (Y i (Function.update v i z))² ∂μ i ≤ s2 i`.

Integrating out one coordinate at a time (`MeasureTheory.integral_integral_update`) and applying
`ProbabilityTheory.mgf_le_exp_bennett_of_le` on each coordinate line avoids conditional-expectation
kernels and standard-Borel hypotheses, so the coordinate spaces `α j` are arbitrary measurable
spaces.

## Main results

* `ProbabilityTheory.mgf_sum_pi_le_exp_bennett`: product-filtration Bennett MGF bound for `t ≥ 0`.
* `ProbabilityTheory.measure_sum_ge_le_bennett_pi`: sharp Poisson (`klFun`) Bennett–Freedman upper
  tail `exp (-((∑ i, s2 i) / b²) * klFun (1 + b ε / ∑ i, s2 i))` (`b > 0, ∑ i, s2 i > 0, ε ≥ 0`).
* `ProbabilityTheory.measure_sum_ge_le_bernstein_pi`: unconditional rational Bernstein upper tail
  `exp (-ε² / (2 * ((∑ i, s2 i) + b ε / 3)))` for *all* `b ≥ 0`, `s2 i ≥ 0`, and `ε ≥ 0`.
* `ProbabilityTheory.measure_sum_gt_sqrt_add_le_pi`: confidence-`δ` Bernstein bound
  `√(2 (∑ i, s2 i) log (1 / δ)) + 2 b log (1 / δ) / 3` (`δ ∈ (0, 1]`).

## References

* [G. Bennett, *Probability inequalities for the sum of independent random variables*][Bennett1962]
* [D. A. Freedman, *On tail probabilities for martingales*][Freedman1975]
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018]
-/

public section

open MeasureTheory InformationTheory Real Finset
open scoped BigOperators NNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Y : ι → (∀ i, α i) → ℝ}

/-- **Product-filtration Bennett MGF bound**: if adapted coordinate functions `Y i` satisfy
`∫ z, Y i (update v i z) ∂μ i ≤ 0`, `Y i v ≤ b` (`b > 0`), and
`∫ z, Y i (update v i z)² ∂μ i ≤ s2 i`, then for every `t ≥ 0`,
`mgf (fun v => ∑ i, Y i v) (Measure.pi μ) t ≤ exp (((∑ i, s2 i) / b²) * (exp (t b) - 1 - t b))`. -/
theorem mgf_sum_pi_le_exp_bennett {b : ℝ} {s2 : ι → ℝ} (hb : 0 < b)
    (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hint1 : ∀ i v, Integrable (fun z => Y i (Function.update v i z)) (μ i))
    (hint2 : ∀ i v, Integrable (fun z => Y i (Function.update v i z) ^ 2) (μ i))
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i ≤ 0)
    (hupper : ∀ i v, Y i v ≤ b)
    (hvar : ∀ i v, ∫ z, Y i (Function.update v i z) ^ 2 ∂μ i ≤ s2 i)
    {t : ℝ} (ht : 0 ≤ t) :
    mgf (fun v => ∑ i, Y i v) (Measure.pi μ) t ≤
      exp (((∑ i, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) := by
  have hint_s (s : Finset ι) :
      Integrable (fun v => exp (t * ∑ i ∈ s, Y i v)) (Measure.pi μ) :=
    integrable_exp_mul_of_le t (s.card * b) ht
      (Finset.measurable_sum s fun i _ => hY i).aemeasurable
      (Filter.Eventually.of_forall fun v => (Finset.sum_le_sum fun i _ => hupper i v).trans_eq
        (by rw [Finset.sum_const, nsmul_eq_mul]))
  have key (s : Finset ι) :
      ∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ ≤
        exp (((∑ i ∈ s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert j s hlt ih =>
      have hj : j ∉ s := fun h => lt_irrefl j (hlt j h)
      calc ∫ v, exp (t * ∑ i ∈ insert j s, Y i v) ∂Measure.pi μ
          = ∫ v, ∫ z, exp (t * ∑ i ∈ insert j s, Y i (Function.update v j z)) ∂μ j
              ∂Measure.pi μ := (integral_integral_update μ (hint_s (insert j s)) j).symm
        _ = ∫ v, exp (t * ∑ i ∈ s, Y i v) *
              ∫ z, exp (t * Y j (Function.update v j z)) ∂μ j ∂Measure.pi μ := by
            congr 1 with v
            rw [← integral_const_mul]
            congr 1 with z
            rw [Finset.sum_insert hj,
              Finset.sum_congr rfl fun i hi => hadapted i j (hlt i hi) v z,
              mul_add, exp_add, mul_comm]
        _ ≤ ∫ v, exp (t * ∑ i ∈ s, Y i v) * exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b))
              ∂Measure.pi μ :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun v =>
                mul_nonneg (exp_pos _).le (integral_nonneg fun _ => (exp_pos _).le))
              ((hint_s s).mul_const _)
              (Filter.Eventually.of_forall fun v => mul_le_mul_of_nonneg_left
                (mgf_le_exp_bennett_of_le (hint1 j v) (hint2 j v) (hmean j v) hb
                  (Filter.Eventually.of_forall fun z => hupper j (Function.update v j z))
                  (hvar j v) ht) (exp_pos _).le)
        _ = (∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ) *
              exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b)) := integral_mul_const _ _
        _ ≤ exp (((∑ i ∈ s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) *
              exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b)) :=
            mul_le_mul_of_nonneg_right ih (exp_pos _).le
        _ = exp (((∑ i ∈ insert j s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) := by
            rw [← exp_add, Finset.sum_insert hj]; exact congrArg exp (by ring)
  simpa only [mgf] using key Finset.univ

/-- **Product-filtration Bennett–Freedman inequality**: under the hypotheses of
`mgf_sum_pi_le_exp_bennett` with `V = ∑ i, s2 i > 0`, `b > 0`, and `ε ≥ 0`,
`(Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤ exp (-(V / b²) * klFun (1 + b ε / V))`. -/
theorem measure_sum_ge_le_bennett_pi {b ε : ℝ} {s2 : ι → ℝ} (hb : 0 < b)
    (hV : 0 < ∑ i, s2 i) (hε : 0 ≤ ε)
    (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hint1 : ∀ i v, Integrable (fun z => Y i (Function.update v i z)) (μ i))
    (hint2 : ∀ i v, Integrable (fun z => Y i (Function.update v i z) ^ 2) (μ i))
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i ≤ 0)
    (hupper : ∀ i v, Y i v ≤ b)
    (hvar : ∀ i v, ∫ z, Y i (Function.update v i z) ^ 2 ∂μ i ≤ s2 i) :
    (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤
      exp (-((∑ i, s2 i) / b ^ 2) * klFun (1 + b * ε / ∑ i, s2 i)) :=
  measure_ge_le_bennett_of_mgf_le (Finset.measurable_sum Finset.univ fun i _ => hY i).aemeasurable
    (B := Fintype.card ι * b) (Filter.Eventually.of_forall fun v =>
      (Finset.sum_le_sum fun i _ => hupper i v).trans_eq
        (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
    hb hV hε fun _ => mgf_sum_pi_le_exp_bennett hb hY hadapted hint1 hint2 hmean hupper hvar

/-- **Product-filtration Bernstein inequality**: for adapted coordinate functions `Y i` satisfying
`∫ z, Y i (update v i z) ∂μ i ≤ 0`, `Y i v ≤ b`, and `∫ z, Y i (update v i z)² ∂μ i ≤ s2 i`, for
*all* `b ≥ 0`, `s2 i ≥ 0`, and `ε ≥ 0`,
`(Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤ exp (-ε² / (2 * ((∑ i, s2 i) + b ε / 3)))`. -/
theorem measure_sum_ge_le_bernstein_pi {b ε : ℝ} {s2 : ι → ℝ} (hb : 0 ≤ b)
    (hσ : ∀ i, 0 ≤ s2 i) (hε : 0 ≤ ε)
    (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hint1 : ∀ i v, Integrable (fun z => Y i (Function.update v i z)) (μ i))
    (hint2 : ∀ i v, Integrable (fun z => Y i (Function.update v i z) ^ 2) (μ i))
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i ≤ 0)
    (hupper : ∀ i v, Y i v ≤ b)
    (hvar : ∀ i v, ∫ z, Y i (Function.update v i z) ^ 2 ∂μ i ≤ s2 i) :
    (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤
      exp (-ε ^ 2 / (2 * ((∑ i, s2 i) + b * ε / 3))) := by
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · simp
  · rcases isEmpty_or_nonempty ι with hι | hι
    · rw [show {v : ∀ i, α i | ε ≤ ∑ i, Y i v} = ∅ by ext v; simpa using hε_pos, measureReal_empty]
      exact (exp_pos _).le
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · rw [show {v : ∀ i, α i | ε ≤ ∑ i, Y i v} = ∅ by
          ext v; simpa using (Finset.sum_nonpos fun i _ => hupper i v).trans_lt hε_pos,
          measureReal_empty]
        exact (exp_pos _).le
      · set V := ∑ i, s2 i
        have hV_nn : 0 ≤ V := Finset.sum_nonneg fun i _ => hσ i
        rcases eq_or_lt_of_le hV_nn with hV_zero | hV_pos
        · have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
          have hfor_eta (η : ℝ) (hη : 0 < η) : (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤
              exp (-ε ^ 2 / (2 * (η + b * ε / 3))) := by
            have hsum_σ' : ∑ _ : ι, η / Fintype.card ι = η := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              field_simp [hcard_pos.ne']
            have hben := measure_sum_ge_le_bennett_pi hb_pos (by rw [hsum_σ']; exact hη) hε
              hY hadapted hint1 hint2 hmean hupper fun i v => (hvar i v).trans
                ((Finset.single_le_sum (fun k _ => hσ k) (Finset.mem_univ i)).trans
                  (hV_zero.symm.le.trans (by positivity)))
            rw [hsum_σ'] at hben
            exact hben.trans (Cslib.Probability.exp_neg_klFun_le_exp_bernstein hb_pos hη hε)
          have hden0 : (2 : ℝ) * (0 + b * ε / 3) ≠ 0 := by positivity
          have hcont : ContinuousAt (fun η : ℝ => exp (-ε ^ 2 / (2 * (η + b * ε / 3)))) 0 := by
            fun_prop (disch := exact hden0)
          rw [← hV_zero]
          exact ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
            (Filter.eventually_of_mem self_mem_nhdsWithin hfor_eta)
        · exact (measure_sum_ge_le_bennett_pi hb_pos hV_pos hε hY hadapted hint1 hint2 hmean
            hupper hvar).trans
            (Cslib.Probability.exp_neg_klFun_le_exp_bernstein hb_pos hV_pos hε)

/-- **Confidence-`δ` product-filtration Bernstein bound**: under the hypotheses of
`measure_sum_ge_le_bernstein_pi`, for every `δ ∈ (0, 1]`,
`∑ i, Y i` exceeds `√(2 (∑ i, s2 i) log (1 / δ)) + 2 b log (1 / δ) / 3` with probability at most
`δ`. -/
theorem measure_sum_gt_sqrt_add_le_pi {b δ : ℝ} {s2 : ι → ℝ} (hb : 0 ≤ b)
    (hσ : ∀ i, 0 ≤ s2 i) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hint1 : ∀ i v, Integrable (fun z => Y i (Function.update v i z)) (μ i))
    (hint2 : ∀ i v, Integrable (fun z => Y i (Function.update v i z) ^ 2) (μ i))
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i ≤ 0)
    (hupper : ∀ i v, Y i v ≤ b)
    (hvar : ∀ i v, ∫ z, Y i (Function.update v i z) ^ 2 ∂μ i ≤ s2 i) :
    let V := ∑ i, s2 i
    let L := log (1 / δ)
    (Measure.pi μ).real {v | √(2 * V * L) + 2 * b * L / 3 < ∑ i, Y i v} ≤ δ := by
  intro V L
  rcases eq_or_lt_of_le hδ1 with rfl | hδ_lt1
  · exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  · have hV_nn : 0 ≤ V := Finset.sum_nonneg fun i _ => hσ i
    by_cases hvb : 0 < V ∨ 0 < b
    · obtain ⟨hε_pos, htail⟩ := Cslib.Probability.exp_bernstein_le_of_sqrt_add hV_nn hb hδ hδ_lt1
        hvb
      exact ((measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hv => hv.le)).trans
        (measure_sum_ge_le_bernstein_pi hb hσ hε_pos.le hY hadapted hint1 hint2 hmean
          hupper hvar)).trans htail
    · push Not at hvb
      rw [show √(2 * V * L) + 2 * b * L / 3 = 0 by
          simp [le_antisymm hvb.1 hV_nn, le_antisymm hvb.2 hb],
        show {v : ∀ i, α i | 0 < ∑ i, Y i v} = ∅ by
          ext v; simpa using Finset.sum_nonpos fun i _ => (hupper i v).trans hvb.2,
        measureReal_empty]
      exact hδ.le

end ProbabilityTheory
