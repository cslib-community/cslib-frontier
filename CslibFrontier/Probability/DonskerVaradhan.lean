/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.ChangeOfMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Donsker–Varadhan variational formula and Gibbs posteriors

Completes the variational duality of the Kullback–Leibler divergence built on
`CslibFrontier.Probability.ChangeOfMeasure` [DonskerVaradhan1983] [Catoni2007] [Alquier2024]:

1. **Exact excess-KL / tilted decomposition.** For probability measures `μ` and `ν` with
   `KL(μ ‖ ν) < ∞`, an exponentially tilted (**Gibbs**) measure `ν.tilted f` satisfies
   `KL(μ ‖ ν.tilted f) = KL(μ ‖ ν) - ∫ f ∂μ + log ∫ exp f ∂ν`.
   At `μ = ν.tilted f` this gives exact equality in the change-of-measure inequality:
   `∫ f ∂(ν.tilted f) - KL(ν.tilted f ‖ ν) = log ∫ exp f ∂ν`.
2. **Donsker–Varadhan variational formula (both halves).**
   - `log_integral_exp_eq_sSup`: `log ∫ exp f ∂ν = sup_μ (∫ f ∂μ - KL(μ ‖ ν))`, where the supremum
     ranges over probability measures `μ` with `KL(μ ‖ ν) < ∞` and `f ∈ L¹(μ)`, attained uniquely
     at `μ = ν.tilted f`.
   - `toReal_klDiv_eq_sSup`: for arbitrary probability measures `μ, ν` with `KL(μ ‖ ν) < ∞`,
     `KL(μ ‖ ν) = sup_f (∫ f ∂μ - log ∫ exp f ∂ν)`, where the supremum ranges over bounded
     measurable functions `f : α → ℝ`. The proof truncates the log-likelihood ratio `llr μ ν` to
     `[-n, n]` (setting `-n` on `{dμ/dν = 0}` where `log 0 = 0`), then passes to the limit using
     dominated convergence and `log (1 + e⁻ⁿ) ≤ e⁻ⁿ`.
3. **Unique Gibbs posterior minimizer.** At inverse temperature `β > 0`, for any measurable loss
   `g : α → ℝ` with `exp (-β * g) ∈ L¹(ν)`, the Gibbs posterior `ν.tilted (-β * g)` uniquely
   minimizes the PAC-Bayes free-energy functional `μ ↦ ∫ g ∂μ + KL(μ ‖ ν) / β`, with excess value
   `KL(μ ‖ ν.tilted (-β * g)) / β`.

## Main results

* `Cslib.Probability.klDiv_tilted_right_ne_top`,
  `Cslib.Probability.toReal_klDiv_tilted_right`: KL divergence against a tilted measure.
* `Cslib.Probability.klDiv_tilted_self_ne_top`,
  `Cslib.Probability.toReal_klDiv_tilted_self`: equality case of change of measure.
* `Cslib.Probability.log_integral_exp_eq_sSup`: Fenchel dual of `KL(· ‖ ν)`.
* `Cslib.Probability.toReal_klDiv_eq_sSup`: full Donsker–Varadhan variational formula.
* `Cslib.Probability.freeEnergy_sub_eq_toReal_klDiv_tilted`,
  `Cslib.Probability.freeEnergy_tilted_le`,
  `Cslib.Probability.freeEnergy_eq_tilted_iff`: unique optimality of the Gibbs posterior.

## References

Exact section and page locators below are unverified against the primary PDFs (pending an
outside-fleet source check).

* [M. D. Donsker, S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process expectations
  for large time, IV*][DonskerVaradhan1983] (locator unverified)
* [O. Catoni, *PAC-Bayesian Supervised Classification*][Catoni2007] (locator unverified)
* [P. Alquier, *User-friendly Introduction to PAC-Bayes Bounds*][Alquier2024] (locator unverified)
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory Filter Real
open scoped ENNReal Topology

variable {α : Type*} {mα : MeasurableSpace α}

/-! ### Tilted measure identities and equality case of change of measure -/

/-- If `KL(μ ‖ ν) < ∞`, `f` is `μ`-integrable, and `exp ∘ f` is `ν`-integrable, then
`KL(μ ‖ ν.tilted f) < ∞`. -/
theorem klDiv_tilted_right_ne_top {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {f : α → ℝ} (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => exp (f x)) ν) :
    klDiv μ (ν.tilted f) ≠ ⊤ := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hkl
  exact klDiv_ne_top (hac.trans (absolutelyContinuous_tilted hfν))
    (integrable_llr_tilted_right hac hfμ hint hfν)

/-- Exact tilted KL decomposition: for probability measures with `KL(μ ‖ ν) < ∞`,
`KL(μ ‖ ν.tilted f) = KL(μ ‖ ν) - ∫ f ∂μ + log ∫ exp f ∂ν`. -/
theorem toReal_klDiv_tilted_right {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {f : α → ℝ} (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => exp (f x)) ν) :
    (klDiv μ (ν.tilted f)).toReal =
      (klDiv μ ν).toReal - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hkl
  have hμt : μ ≪ ν.tilted f := hac.trans (absolutelyContinuous_tilted hfν)
  rw [toReal_klDiv_of_measure_eq hμt (by simp), toReal_klDiv_of_measure_eq hac (by simp),
    integral_llr_tilted_right hac hfμ hfν hint]

private theorem llr_tilted_self_ae {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => exp (f x)) ν) :
    llr (ν.tilted f) ν =ᵐ[ν.tilted f] fun x => f x - log (∫ z, exp (f z) ∂ν) := by
  have h1 := llr_tilted_left (.refl ν) hfν (aemeasurable_of_aemeasurable_exp hfν.1.aemeasurable)
  refine (tilted_absolutelyContinuous ν f).ae_le ?_
  filter_upwards [h1, llr_self ν] with x hx h0
  rw [hx, h0, Pi.zero_apply, add_zero]

/-- The tilted probability measure `ν.tilted f` has finite KL divergence from `ν` whenever
`exp ∘ f` is `ν`-integrable and `f` is `(ν.tilted f)`-integrable. -/
theorem klDiv_tilted_self_ne_top {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => exp (f x)) ν) (hft : Integrable f (ν.tilted f)) :
    klDiv (ν.tilted f) ν ≠ ⊤ := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  exact klDiv_ne_top (tilted_absolutelyContinuous ν f)
    ((integrable_congr (llr_tilted_self_ae hfν)).mpr (hft.sub (integrable_const _)))

/-- **Equality case of the change-of-measure inequality**: the exponentially tilted measure
`ν.tilted f` satisfies `KL(ν.tilted f ‖ ν) = ∫ f ∂(ν.tilted f) - log ∫ exp f ∂ν`. -/
theorem toReal_klDiv_tilted_self {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => exp (f x)) ν) (hft : Integrable f (ν.tilted f)) :
    (klDiv (ν.tilted f) ν).toReal =
      ∫ x, f x ∂(ν.tilted f) - log (∫ x, exp (f x) ∂ν) := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  rw [toReal_klDiv_of_measure_eq (tilted_absolutelyContinuous ν f) (by simp),
    integral_congr_ae (llr_tilted_self_ae hfν), integral_sub hft (integrable_const _)]
  simp

/-! ### Donsker–Varadhan variational duality -/

/-- **Dual variational principle for the log-moment generating function** (`Fenchel` conjugate of
`KL(· ‖ ν)`): `log ∫ exp f ∂ν = sup { ∫ f ∂μ - KL(μ ‖ ν) }`, where the supremum runs over
probability measures `μ` with `KL(μ ‖ ν) < ∞` and `f ∈ L¹(μ)`, attained at `μ = ν.tilted f`. -/
theorem log_integral_exp_eq_sSup {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfν : Integrable (fun x => exp (f x)) ν) (hft : Integrable f (ν.tilted f)) :
    log (∫ x, exp (f x) ∂ν) =
      sSup { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ klDiv μ ν ≠ ⊤ ∧
        Integrable f μ ∧ r = ∫ x, f x ∂μ - (klDiv μ ν).toReal } := by
  set S : Set ℝ := { r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ klDiv μ ν ≠ ⊤ ∧
    Integrable f μ ∧ r = ∫ x, f x ∂μ - (klDiv μ ν).toReal }
  have hmem : log (∫ x, exp (f x) ∂ν) ∈ S :=
    ⟨ν.tilted f, isProbabilityMeasure_tilted hfν, klDiv_tilted_self_ne_top hfν hft, hft,
      by linarith [toReal_klDiv_tilted_self hfν hft]⟩
  have hbdd : ∀ r ∈ S, r ≤ log (∫ x, exp (f x) ∂ν) := fun _ ⟨_, _, hkl, hfμ, hr⟩ => by
    linarith [hr, Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp hkl hfμ hfν]
  exact le_antisymm (le_csSup ⟨log (∫ x, exp (f x) ∂ν), hbdd⟩ hmem)
    (csSup_le ⟨_, hmem⟩ hbdd)

/-- **Donsker–Varadhan variational formula for `KL(μ ‖ ν)`** [DonskerVaradhan1983] (locator
unverified): for arbitrary probability measures `μ, ν` with `KL(μ ‖ ν) < ∞`,
`KL(μ ‖ ν) = sup { ∫ f ∂μ - log ∫ exp f ∂ν }`, taken over bounded measurable functions `f : α → ℝ`.
-/
theorem toReal_klDiv_eq_sSup {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ⊤) :
    (klDiv μ ν).toReal =
      sSup { r : ℝ | ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧
        r = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) } := by
  set S : Set ℝ := { r : ℝ | ∃ f : α → ℝ, Measurable f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧
    r = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) }
  have hle : ∀ r ∈ S, r ≤ (klDiv μ ν).toReal := by
    rintro _ ⟨f, hfm, ⟨C, hC⟩, rfl⟩
    have hfμ : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
    have hfν : Integrable (fun x => exp (f x)) ν :=
      Integrable.of_bound hfm.exp.aestronglyMeasurable (exp C) (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (exp_pos _).le]
        exact exp_le_exp.mpr (le_trans (le_abs_self _) (hC x)))
    linarith [Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp hkl hfμ hfν]
  have hbdd : BddAbove S := ⟨(klDiv μ ν).toReal, hle⟩
  refine le_antisymm ?_
    (csSup_le ⟨0, fun _ => 0, measurable_const, ⟨0, fun _ => by simp⟩, by simp⟩ hle)
  -- Lower bound: approximate `llr μ ν` by bounded truncations `f n` clamped to `[-n, n]`,
  -- mapping `{dμ/dν = 0}` to `-n` so that `exp (f n x) ≤ (dμ/dν)(x) + exp (-n)` `ν`-a.e.
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 hkl
  let f : ℕ → α → ℝ := fun n x =>
    if μ.rnDeriv ν x = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (llr μ ν x))
  have hf_meas (n : ℕ) : Measurable (f n) :=
    Measurable.ite ((μ.measurable_rnDeriv ν) (measurableSet_singleton 0)) measurable_const
      (measurable_const.max (measurable_const.min (measurable_llr μ ν)))
  have hf_bound (n : ℕ) (x : α) : |f n x| ≤ (n : ℝ) := by
    dsimp only [f]
    split_ifs
    · rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    · rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩
  have hf_le_llr (n : ℕ) : ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖llr μ ν x‖ := by
    filter_upwards [Measure.rnDeriv_pos hac] with x hx
    simp only [f, hx.ne', ↓reduceIte, Real.norm_eq_abs]
    have := abs_nonneg (llr μ ν x)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact abs_le.2 ⟨(le_min (by linarith) (neg_abs_le _)).trans (le_max_right _ _),
      max_le (by linarith) ((min_le_right _ _).trans (le_abs_self _))⟩
  have hf_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (llr μ ν x)) := by
    filter_upwards [Measure.rnDeriv_pos hac] with x hx
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil |llr μ ν x|) fun n hn => ?_
    have hmem := abs_le.mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr hn) : |llr μ ν x| ≤ n)
    simp only [f, hx.ne', ↓reduceIte, min_eq_right hmem.2, max_eq_right hmem.1]
  have hlim_int : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, llr μ ν x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖llr μ ν x‖)
      (fun n => (hf_meas n).aestronglyMeasurable) hllr.norm hf_le_llr hf_tendsto
  have hkl_eq : ∫ x, llr μ ν x ∂μ = (klDiv μ ν).toReal :=
    (toReal_klDiv_of_measure_eq hac (by simp)).symm
  have hrn_int : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable
      (by rw [Measure.lintegral_rnDeriv hac]; simp)
  have hrn_val : ∫ x, (μ.rnDeriv ν x).toReal ∂ν = 1 := by
    rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (Measure.rnDeriv_lt_top μ ν),
      Measure.lintegral_rnDeriv hac]
    simp
  have hlog_le (n : ℕ) : log (∫ x, exp (f n x) ∂ν) ≤ exp (-(n : ℝ)) := by
    have hexp_int : Integrable (fun x => exp (f n x)) ν :=
      Integrable.of_bound (hf_meas n).exp.aestronglyMeasurable (exp n) (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (exp_pos _).le]
        exact exp_le_exp.mpr (le_trans (le_abs_self _) (hf_bound n x)))
    have hpt : ∀ᵐ x ∂ν, exp (f n x) ≤ (μ.rnDeriv ν x).toReal + exp (-(n : ℝ)) := by
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hxtop
      dsimp only [f]
      split_ifs with hx0
      · simp [hx0]
      · rw [exp_monotone.map_max]
        exact max_le (le_add_of_nonneg_left ENNReal.toReal_nonneg) (le_add_of_le_of_nonneg
          ((exp_le_exp.mpr (min_le_right _ _)).trans_eq (exp_log (ENNReal.toReal_pos hx0 hxtop.ne)))
          (exp_pos _).le)
    have hsum : ∫ x, exp (f n x) ∂ν ≤ 1 + exp (-(n : ℝ)) := by
      refine (integral_mono_ae hexp_int (hrn_int.add (integrable_const _)) hpt).trans_eq ?_
      rw [integral_add' hrn_int (integrable_const _), hrn_val]; simp
    exact (log_le_log (integral_exp_pos hexp_int) hsum).trans
      ((log_le_sub_one_of_pos (by positivity)).trans_eq (by ring))
  have hlim : Tendsto (fun n : ℕ => ∫ x, f n x ∂μ - exp (-(n : ℝ))) atTop
      (𝓝 (klDiv μ ν).toReal) := by
    have h2 : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa only [sub_zero, hkl_eq] using hlim_int.sub h2
  exact le_of_tendsto' hlim fun n => by
    linarith [le_csSup hbdd (⟨f n, hf_meas n, ⟨n, hf_bound n⟩, rfl⟩ : _ ∈ S), hlog_le n]

/-! ### Gibbs posterior free-energy minimization -/

/-- Exact excess free-energy identity for the Gibbs posterior `ν.tilted (fun x => -β * g x)` at
inverse temperature `β > 0`:
`(∫ g ∂μ + KL(μ ‖ ν) / β) - (-log ∫ exp (-β * g) ∂ν / β) = KL(μ ‖ ν.tilted (-β * g)) / β`. -/
theorem freeEnergy_sub_eq_toReal_klDiv_tilted {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {β : ℝ} (hβ : β ≠ 0) {g : α → ℝ}
    (hgμ : Integrable g μ) (hexp : Integrable (fun x => exp (-β * g x)) ν) :
    (∫ x, g x ∂μ + (klDiv μ ν).toReal / β) - (-log (∫ x, exp (-β * g x) ∂ν) / β) =
      (klDiv μ (ν.tilted fun x => -β * g x)).toReal / β := by
  rw [toReal_klDiv_tilted_right hkl (hgμ.const_mul (-β)) hexp, integral_const_mul]
  field_simp; ring

/-- The Gibbs posterior `ν.tilted (fun x => -β * g x)` minimizes the KL-regularized loss
`μ ↦ ∫ g ∂μ + KL(μ ‖ ν) / β` over all probability measures with `KL(μ ‖ ν) < ∞` and
`g ∈ L¹(μ)` [Catoni2007] [Alquier2024] (locators unverified). -/
theorem freeEnergy_tilted_le {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ⊤) {β : ℝ} (hβ : 0 < β) {g : α → ℝ} (hgμ : Integrable g μ)
    (hexp : Integrable (fun x => exp (-β * g x)) ν)
    (hgt : Integrable g (ν.tilted fun x => -β * g x)) :
    ∫ x, g x ∂(ν.tilted fun x => -β * g x) +
        (klDiv (ν.tilted fun x => -β * g x) ν).toReal / β ≤
      ∫ x, g x ∂μ + (klDiv μ ν).toReal / β := by
  have hval : ∫ x, g x ∂(ν.tilted fun x => -β * g x) +
      (klDiv (ν.tilted fun x => -β * g x) ν).toReal / β =
      -log (∫ x, exp (-β * g x) ∂ν) / β := by
    rw [toReal_klDiv_tilted_self hexp (hgt.const_mul (-β)), integral_const_mul]
    field_simp; ring
  rw [hval, ← sub_nonneg, freeEnergy_sub_eq_toReal_klDiv_tilted hkl hβ.ne' hgμ hexp]
  exact div_nonneg ENNReal.toReal_nonneg hβ.le

/-- Uniqueness of the Gibbs posterior minimizer: a probability measure `μ` with `KL(μ ‖ ν) < ∞`
achieves the minimum free energy `-log ∫ exp (-β * g) ∂ν / β` if and only if
`μ = ν.tilted (fun x => -β * g x)`. -/
theorem freeEnergy_eq_tilted_iff {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ⊤) {β : ℝ} (hβ : 0 < β) {g : α → ℝ}
    (hgμ : Integrable g μ) (hexp : Integrable (fun x => exp (-β * g x)) ν) :
    ∫ x, g x ∂μ + (klDiv μ ν).toReal / β = -log (∫ x, exp (-β * g x) ∂ν) / β ↔
      μ = ν.tilted fun x => -β * g x := by
  have : IsProbabilityMeasure (ν.tilted fun x => -β * g x) := isProbabilityMeasure_tilted hexp
  have hne : klDiv μ (ν.tilted fun x => -β * g x) ≠ ⊤ :=
    klDiv_tilted_right_ne_top hkl (hgμ.const_mul (-β)) hexp
  rw [← sub_eq_zero, freeEnergy_sub_eq_toReal_klDiv_tilted hkl hβ.ne' hgμ hexp,
    div_eq_zero_iff, or_iff_left hβ.ne', ENNReal.toReal_eq_zero_iff, or_iff_left hne,
    klDiv_eq_zero_iff]

end Cslib.Probability
