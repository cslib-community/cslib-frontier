/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/InformationTheory/KullbackLeibler/ChangeOfMeasure.lean`)

public import CslibFrontier.Init
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The change-of-measure inequality

For probability measures `μ` and `ν` with finite Kullback–Leibler divergence and a function `f`
integrable under `μ` with `exp ∘ f` integrable under `ν`,

`∫ f ∂μ ≤ KL(μ ‖ ν) + log ∫ exp f ∂ν`,

the divergence in nats. This is the easy half of the Donsker–Varadhan variational formula, and
the change-of-measure step of PAC-Bayes bounds [McAllester1999] [ShalevShwartzBenDavid2014,
Section 31.1, inequality (31.2)]. The proof is Gibbs' inequality for the exponentially tilted
measure `ν.tilted f`, through Mathlib's `integral_llr_tilted_right`; the source derives it from
Jensen's inequality for discrete distributions, and the measure form covers that case.

For nonnegative `f`, finiteness of `∫ exp f ∂ν` already makes `f` integrable under `μ`, by the
inequality for the truncations `min f n` and monotone convergence; this applies the inequality to
unbounded functions, such as the binary relative entropy in the PAC-Bayes-kl bound.

The divergence of a point mass from a probability measure `ν` with an atom at `a` is
`log (1 / ν {a})`. This evaluates the change-of-measure bound at a point mass, which turns a
PAC-Bayes bound into an Occam bound.

## Main results

* `Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp`: the change-of-measure
  inequality.
* `Cslib.Probability.integrable_of_lintegral_exp_ne_top`: integrability of nonnegative `f` with
  `∫ exp f ∂ν < ∞`.
* `Cslib.Probability.klDiv_dirac_ne_top`, `Cslib.Probability.toReal_klDiv_dirac`: the divergence
  of a point mass.

## References

* [M. D. Donsker, S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process
  expectations for large time, IV*][DonskerVaradhan1983]
* [D. A. McAllester, *PAC-Bayesian model averaging*][McAllester1999]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- **The change-of-measure inequality** (Donsker–Varadhan): for probability measures with
`klDiv μ ν ≠ ∞`, `∫ f ∂μ ≤ KL(μ ‖ ν) + log ∫ exp f ∂ν`, in nats. -/
theorem integral_le_toReal_klDiv_add_log_integral_exp {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {f : α → ℝ} (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν) :
    ∫ x, f x ∂μ ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hkl
  have := isProbabilityMeasure_tilted hfν
  have hgibbs := integral_llr_add_sub_measure_univ_nonneg
    (hac.trans (absolutelyContinuous_tilted hfν)) (integrable_llr_tilted_right hac hfμ hint hfν)
  simp only [probReal_univ, add_sub_cancel_right] at hgibbs
  rw [integral_llr_tilted_right hac hfμ hfν hint] at hgibbs
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  linarith

/-- A nonnegative function whose exponential has finite `ν`-integral is `μ`-integrable whenever
`KL(μ ‖ ν) < ∞`: by change of measure, its truncations at level `n` have `μ`-integrals at most
`KL(μ ‖ ν) + log ∫ exp f ∂ν`. -/
theorem integrable_of_lintegral_exp_ne_top {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {f : α → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂ν ≠ ⊤) :
    Integrable f μ := by
  set C := (klDiv μ ν).toReal + Real.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂ν).toReal
  set g : ℕ → α → ℝ := fun n x => min (f x) n
  have hgm (n : ℕ) : Measurable (g n) := hfm.min measurable_const
  have hg0 (n : ℕ) (x : α) : 0 ≤ g n x := le_min (hf0 x) (Nat.cast_nonneg n)
  have hgi (n : ℕ) : Integrable (g n) μ :=
    Integrable.of_mem_Icc 0 n (hgm n).aemeasurable
      (ae_of_all _ fun x => ⟨hg0 n x, min_le_right _ _⟩)
  have hbound (n : ℕ) : ∫ x, g n x ∂μ ≤ C := by
    have hei : Integrable (fun x => Real.exp (g n x)) ν :=
      Integrable.of_mem_Icc 0 (Real.exp n) (hgm n).exp.aemeasurable
        (ae_of_all _ fun x => ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (min_le_right _ _)⟩)
    refine (integral_le_toReal_klDiv_add_log_integral_exp hkl (hgi n) hei).trans
      (add_le_add_right (Real.log_le_log (integral_exp_pos hei) ?_) _)
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      hei.aestronglyMeasurable]
    exact ENNReal.toReal_mono hexp (lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _)))
  have hsup (x : α) : ⨆ n : ℕ, ENNReal.ofReal (g n x) = ENNReal.ofReal (f x) := by
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (f x)
    exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (le_min le_rfl hn))
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C := by
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ
        = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (g n x) ∂μ := lintegral_congr fun x => (hsup x).symm
      _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (g n x) ∂μ :=
          lintegral_iSup (fun n => (hgm n).ennreal_ofReal) fun n n' h x =>
            ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 h))
      _ ≤ ENNReal.ofReal C := iSup_le fun n => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (ae_of_all _ (hg0 n))]
          exact ENNReal.ofReal_le_ofReal (hbound n)
  exact ⟨hfm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩

section Dirac

variable [MeasurableSingletonClass α] {ν : Measure α} [IsProbabilityMeasure ν] {a : α}

omit [IsProbabilityMeasure ν] in
private theorem dirac_absolutelyContinuous (ha : ν {a} ≠ 0) : Measure.dirac a ≪ ν := by
  intro s hs
  have hnot : a ∉ s := fun h => ha (measure_mono_null (Set.singleton_subset_iff.mpr h) hs)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hnot]

/-- The log-likelihood ratio of a point mass at its atom is `-log ν {a}`. -/
private theorem llr_dirac_self (ha : ν {a} ≠ 0) :
    llr (Measure.dirac a) ν a = -Real.log (ν.real {a}) := by
  have hmass := congrArg (fun μ : Measure α => μ {a})
    (Measure.withDensity_rnDeriv_eq _ ν (dirac_absolutelyContinuous ha))
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
    Measure.dirac_apply_of_mem (Set.mem_singleton a)] at hmass
  rw [llr, ENNReal.eq_inv_of_mul_eq_one_left hmass, ENNReal.toReal_inv, Real.log_inv,
    measureReal_def]

/-- The divergence of a point mass at an atom of `ν` is finite. -/
theorem klDiv_dirac_ne_top (ha : ν {a} ≠ 0) : klDiv (Measure.dirac a) ν ≠ ⊤ := by
  refine klDiv_ne_top (dirac_absolutelyContinuous ha) (integrable_dirac ?_)
  rw [llr_dirac_self ha]
  exact eNorm_lt_top

/-- The divergence of a point mass at an atom `a` of `ν` is `log (1 / ν {a})`, in nats. -/
theorem toReal_klDiv_dirac (ha : ν {a} ≠ 0) :
    (klDiv (Measure.dirac a) ν).toReal = -Real.log (ν.real {a}) := by
  rw [toReal_klDiv_of_measure_eq (dirac_absolutelyContinuous ha) (by simp), integral_dirac,
    llr_dirac_self ha]

end Dirac

end Cslib.Probability
