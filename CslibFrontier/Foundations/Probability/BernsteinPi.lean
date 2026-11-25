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
      (Filter.Eventually.of_forall fun v => by
        calc ∑ i ∈ s, Y i v ≤ ∑ _ ∈ s, b := Finset.sum_le_sum fun i _ => hupper i v
          _ = s.card * b := by rw [Finset.sum_const, nsmul_eq_mul])
  have key (s : Finset ι) :
      ∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ ≤
        exp (((∑ i ∈ s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert j s hlt ih =>
      have hj : j ∉ s := fun h => lt_irrefl j (hlt j h)
      have hP : ∀ v z, ∑ i ∈ s, Y i (Function.update v j z) = ∑ i ∈ s, Y i v :=
        fun v z => Finset.sum_congr rfl fun i hi => hadapted i j (hlt i hi) v z
      have hstep (v : ∀ i, α i) :
          ∫ z, exp (t * Y j (Function.update v j z)) ∂μ j ≤
            exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b)) :=
        mgf_le_exp_bennett_of_le (hint1 j v) (hint2 j v) (hmean j v) hb
          (Filter.Eventually.of_forall fun z => hupper j (Function.update v j z)) (hvar j v) ht
      calc ∫ v, exp (t * ∑ i ∈ insert j s, Y i v) ∂Measure.pi μ
          = ∫ v, ∫ z, exp (t * ∑ i ∈ insert j s, Y i (Function.update v j z)) ∂μ j
              ∂Measure.pi μ := (integral_integral_update μ (hint_s (insert j s)) j).symm
        _ = ∫ v, exp (t * ∑ i ∈ s, Y i v) *
              ∫ z, exp (t * Y j (Function.update v j z)) ∂μ j ∂Measure.pi μ := by
            congr 1 with v
            rw [← integral_const_mul]
            congr 1 with z
            rw [Finset.sum_insert hj, hP, mul_add, exp_add]
            exact mul_comm _ _
        _ ≤ ∫ v, exp (t * ∑ i ∈ s, Y i v) * exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b))
              ∂Measure.pi μ :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun v =>
                mul_nonneg (exp_pos _).le (integral_nonneg fun _ => (exp_pos _).le))
              ((hint_s s).mul_const _)
              (Filter.Eventually.of_forall fun v =>
                mul_le_mul_of_nonneg_left (hstep v) (exp_pos _).le)
        _ = (∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ) *
              exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b)) := integral_mul_const _ _
        _ ≤ exp (((∑ i ∈ s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) *
              exp ((s2 j / b ^ 2) * (exp (t * b) - 1 - t * b)) :=
            mul_le_mul_of_nonneg_right ih (exp_pos _).le
        _ = exp (((∑ i ∈ insert j s, s2 i) / b ^ 2) * (exp (t * b) - 1 - t * b)) := by
            rw [← exp_add, Finset.sum_insert hj]
            congr 1
            ring
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
    (B := Fintype.card ι * b)
    (Filter.Eventually.of_forall fun v => by
      calc ∑ i, Y i v ≤ ∑ _ : ι, b := Finset.sum_le_sum fun i _ => hupper i v
        _ = Fintype.card ι * b := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
    hb hV hε fun _ ht =>
      mgf_sum_pi_le_exp_bennett hb hY hadapted hint1 hint2 hmean hupper hvar ht

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
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
      exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · have hempty : {v : ∀ i, α i | ε ≤ ∑ i, Y i v} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact (Finset.sum_nonpos fun i _ => hupper i v).trans_lt hε_pos
      rw [hempty, measureReal_empty]
      exact (exp_pos _).le
    · set V := ∑ i, s2 i
      have hV_nn : 0 ≤ V := Finset.sum_nonneg fun i _ => hσ i
      rcases eq_or_lt_of_le hV_nn with hV_zero | hV_pos
      · by_cases hι : Nonempty ι
        · have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
          have hfor_eta : ∀ η : ℝ, 0 < η →
              (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤
                exp (-ε ^ 2 / (2 * (η + b * ε / 3))) := by
            intro η hη
            let σ' : ι → ℝ := fun _ => η / Fintype.card ι
            have hsum_σ' : ∑ i : ι, σ' i = η := by
              simp only [σ', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              field_simp [hcard_pos.ne']
            have hvar' (i : ι) (v : ∀ j, α j) :
                ∫ z, Y i (Function.update v i z) ^ 2 ∂μ i ≤ σ' i :=
              (hvar i v).trans ((Finset.single_le_sum (fun k _ => hσ k)
                (Finset.mem_univ i)).trans (hV_zero.symm.le.trans (by positivity)))
            have hben := measure_sum_ge_le_bennett_pi hb_pos (by rw [hsum_σ']; exact hη) hε
              hY hadapted hint1 hint2 hmean hupper hvar'
            rw [hsum_σ'] at hben
            exact hben.trans (Cslib.Probability.exp_neg_klFun_le_exp_bernstein hb_pos hη hε)
          have hcont : ContinuousAt (fun η : ℝ => exp (-ε ^ 2 / (2 * (η + b * ε / 3)))) 0 := by
            have hden0 : (2 : ℝ) * (0 + b * ε / 3) ≠ 0 := by positivity
            fun_prop (disch := exact hden0)
          have htend : Filter.Tendsto (fun η : ℝ => exp (-ε ^ 2 / (2 * (η + b * ε / 3))))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (exp (-ε ^ 2 / (2 * (0 + b * ε / 3))))) :=
            hcont.tendsto.mono_left nhdsWithin_le_nhds
          rw [← hV_zero]
          exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin hfor_eta)
        · rw [not_nonempty_iff] at hι
          have hempty : {v : ∀ i, α i | ε ≤ ∑ i, Y i v} = ∅ := by
            ext v
            simp only [Set.mem_ofPred_eq, Finset.univ_eq_empty, Finset.sum_empty,
              Set.mem_empty_iff_false, iff_false, not_le]
            exact hε_pos
          rw [hempty, measureReal_empty]
          exact (exp_pos _).le
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
      set ε := √(2 * V * L) + 2 * b * L / 3
      calc (Measure.pi μ).real {v | ε < ∑ i, Y i v}
          ≤ (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} :=
            measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hv => hv.le)
        _ ≤ exp (-ε ^ 2 / (2 * (V + b * ε / 3))) :=
            measure_sum_ge_le_bernstein_pi hb hσ hε_pos.le hY hadapted hint1 hint2 hmean hupper hvar
        _ ≤ δ := htail
    · push Not at hvb
      have hV0 : V = 0 := le_antisymm hvb.1 hV_nn
      have hb0 : b = 0 := le_antisymm hvb.2 hb
      have hε0 : √(2 * V * L) + 2 * b * L / 3 = 0 := by simp [hV0, hb0]
      rw [hε0]
      have hempty : {v : ∀ i, α i | 0 < ∑ i, Y i v} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact Finset.sum_nonpos fun i _ => (hupper i v).trans_eq hb0
      rw [hempty, measureReal_empty]
      exact hδ.le

end ProbabilityTheory
