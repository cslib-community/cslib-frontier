/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.StatisticalDistance.TotalVariation
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import CslibFrontier.Probability.Pinsker
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Kullback–Leibler divergence of finite distributions

The library has one divergence notion, Mathlib's `InformationTheory.klDiv`, and one entropy
notion, `Cslib.Probability.PMF.entropy`. This file bridges them. For PMFs on a finite type with
a discrete measurable structure, `klDiv p.toMeasure q.toMeasure` is finite exactly when the
support of `p` is contained in that of `q`, and is then the finite sum
`∑ a, p a * log (p a / q a)` in nats. Consequences:

* Gibbs' inequality: the sum is nonnegative and vanishes only at `p = q`. Equivalently, the
  entropy of `p` is at most its cross-entropy `∑ a, p a * surprisal q a`.
* Entropy is the logarithm of the alphabet size minus the divergence from uniform.
* Mutual information, `H(X) + H(Y) - H(X, Y)`, is the divergence of the joint law from the
  product of its marginals. Entropy is subadditive and conditioning cannot increase it; by the
  equality case of Gibbs' inequality, subadditivity is an equality exactly for independent
  pairs.
* Pinsker's inequality `2 δ(p, q)² ≤ D(p ‖ q)` for the statistical distance `δ`, from the form
  for arbitrary probability measures and events in `Probability/Pinsker`. Statistical distance
  is half of Mathlib's total variation distance `tvDist`.

Divergences are in nats and entropies in bits, so the bridges divide by `log 2`.

## Main results

* `Cslib.Probability.PMF.toReal_klDiv_toMeasure`: the finite-sum formula.
* `Cslib.Probability.PMF.klDiv_toMeasure_ne_top_iff`: finiteness is support inclusion.
* `Cslib.Probability.PMF.klDiv_toMeasure_map_le`: data processing for deterministic maps.
* `Cslib.Probability.PMF.sum_mul_log_div_nonneg`, `.sum_mul_log_div_eq_zero_iff`: Gibbs.
* `Cslib.Probability.PMF.entropy_le_sum_mul_surprisal`: entropy is at most cross-entropy.
* `Cslib.Probability.PMF.entropy_le_logb_card_of_support_subset`: entropy is at most the
  logarithm of the support size.
* `Cslib.Probability.PMF.entropy_eq_logb_card_sub_klDiv`: entropy and divergence from uniform.
* `Cslib.Probability.PMF.entropy_map_fst_add_entropy_map_snd_sub_entropy`: mutual information.
* `Cslib.Probability.PMF.entropy_le_entropy_map_fst_add_entropy_map_snd`: subadditivity, with
  equality exactly for independent pairs
  (`Cslib.Probability.PMF.entropy_eq_entropy_map_fst_add_entropy_map_snd_iff`).
* `Cslib.Probability.PMF.conditionalEntropy_le_entropy_map_snd`: conditioning reduces entropy.
* `Cslib.Probability.PMF.ofReal_two_mul_dist_sq_le_klDiv`,
  `Cslib.Probability.PMF.dist_le_sqrt_toReal_klDiv_div_two`: Pinsker's inequality.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006],
  Theorems 2.6.3 (Gibbs), 2.6.4 (uniform maximizes entropy), 2.6.5 (conditioning reduces
  entropy), 2.6.6 (independence bound on entropy, here for two variables), Section 2.3 and
  Theorem 2.4.1 (mutual information) and Lemma 11.6.1 (Pinsker).
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*}

namespace PMF

/-! ### The finite-sum formula -/

section Bridge

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A PMF measure on a countable type is absolutely continuous with respect to another exactly
when its support is contained in the other's support. -/
theorem toMeasure_absolutelyContinuous_iff [Countable α] {p q : PMF α} :
    p.toMeasure ≪ q.toMeasure ↔ p.support ⊆ q.support := by
  refine ⟨fun h a ha => by_contra fun hq => ha ?_, fun h s hs => ?_⟩
  · simpa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)] using
      h ((PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)).trans
        ((PMF.apply_eq_zero_iff q a).mpr hq))
  · rw [PMF.toMeasure_apply_eq_zero_iff _ (Set.to_countable s).measurableSet] at hs ⊢
    exact hs.mono_left h

/-- The finite-sum formula for the Kullback–Leibler divergence of finite distributions, in
nats. Null outcomes of `p` contribute zero. -/
theorem toReal_klDiv_toMeasure [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal =
      ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  have hac := toMeasure_absolutelyContinuous_iff.mpr h
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  have hdensity : p.toMeasure = q.toMeasure.withDensity (fun a => p a / q a) :=
    Measure.ext_of_singleton fun a => by
      rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
      by_cases hq : q a = 0
      · simp [show p a = 0 from by_contra fun hp => h hp hq, hq]
      · exact (ENNReal.div_mul_cancel hq (PMF.apply_ne_top q a)).symm
  have hrn : p.toMeasure.rnDeriv q.toMeasure =ᵐ[p.toMeasure] fun a => p a / q a :=
    hac.ae_le (hdensity ▸ Measure.rnDeriv_withDensity q.toMeasure (measurable_of_countable _))
  rw [integral_congr_ae (hrn.mono fun a ha => by rw [llr, ha]), PMF.integral_eq_sum]
  simp [ENNReal.toReal_div]

/-- The divergence of finite distributions is finite exactly when the support of the first is
contained in the support of the second. -/
theorem klDiv_toMeasure_ne_top_iff [Finite α] {p q : PMF α} :
    klDiv p.toMeasure q.toMeasure ≠ ⊤ ↔ p.support ⊆ q.support := by
  exact ⟨fun h => toMeasure_absolutelyContinuous_iff.mp (klDiv_ne_top_iff.mp h).1,
    fun h => klDiv_ne_top (toMeasure_absolutelyContinuous_iff.mpr h) Integrable.of_finite⟩

/-- The divergence of finite distributions with nested supports, as an extended real. -/
theorem klDiv_toMeasure_eq_ofReal [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    klDiv p.toMeasure q.toMeasure =
      ENNReal.ofReal (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) := by
  rw [← toReal_klDiv_toMeasure h, ENNReal.ofReal_toReal (klDiv_toMeasure_ne_top_iff.mpr h)]

/-- **Data processing**: a deterministic map cannot increase the divergence of distributions on
a countable type. -/
theorem klDiv_toMeasure_map_le [Countable α] [MeasurableSpace β] (p q : PMF α) (f : α → β) :
    klDiv (p.map f).toMeasure (q.map f).toMeasure ≤ klDiv p.toMeasure q.toMeasure := by
  have hf : Measurable f := measurable_of_countable f
  rw [← _root_.PMF.toMeasure_map f p hf, ← _root_.PMF.toMeasure_map f q hf]
  exact klDiv_map_le _ _ hf

end Bridge

/-! ### Gibbs' inequality -/

section Gibbs

variable [Fintype α]

/-- **Gibbs' inequality**: the divergence sum of finite distributions is nonnegative. -/
theorem sum_mul_log_div_nonneg {p q : PMF α} (h : p.support ⊆ q.support) :
    0 ≤ ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  let : MeasurableSpace α := ⊤
  rw [← toReal_klDiv_toMeasure h]
  exact ENNReal.toReal_nonneg

/-- The equality case of Gibbs' inequality: the divergence sum vanishes only for equal
distributions. -/
theorem sum_mul_log_div_eq_zero_iff {p q : PMF α} (h : p.support ⊆ q.support) :
    ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) = 0 ↔ p = q := by
  let : MeasurableSpace α := ⊤
  rw [← toReal_klDiv_toMeasure h, ENNReal.toReal_eq_zero_iff,
    or_iff_left (klDiv_toMeasure_ne_top_iff.mpr h), klDiv_eq_zero_iff]
  exact PMF.toMeasure_injective.eq_iff

omit [Fintype α] in
/-- Where `p` has positive mass, the information-content gap of `p` and `q` is the logarithm
of their mass ratio, in bits. -/
private theorem mul_surprisal_sub_eq {p q : PMF α} (h : p.support ⊆ q.support) (a : α) :
    (p a).toReal * (surprisal q a - surprisal p a) =
      (p a).toReal * Real.log ((p a).toReal / (q a).toReal) / Real.log 2 := by
  by_cases hp : p a = 0
  · simp [hp]
  have hq : q a ≠ 0 := (PMF.mem_support_iff q a).mp (h ((PMF.mem_support_iff p a).mpr hp))
  have hp' : (p a).toReal ≠ 0 := by ennreal_to_real using hp
  have hq' : (q a).toReal ≠ 0 := by ennreal_to_real using hq
  rw [surprisal, surprisal, Real.logb, Real.logb, Real.log_div hp' hq']
  ring

/-- **Gibbs' inequality** in entropy form: the entropy of `p` is at most its cross-entropy
relative to any `q` whose support contains that of `p`. -/
theorem entropy_le_sum_mul_surprisal {p q : PMF α} (h : p.support ⊆ q.support) :
    entropy p ≤ ∑ a, (p a).toReal * surprisal q a := by
  rw [entropy_eq_sum_surprisal, ← sub_nonneg, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, mul_surprisal_sub_eq h, ← Finset.sum_div]
  exact div_nonneg (sum_mul_log_div_nonneg h) (Real.log_nonneg (by norm_num))

omit [Fintype α] in
/-- The uniform distribution on a nonempty finite set has the logarithm of its size as
entropy. -/
theorem entropy_uniformOfFinset [Finite α] (s : Finset α) (hs : s.Nonempty) :
    entropy (uniformOfFinset s hs) = Real.logb 2 s.card := by
  classical
  let := Fintype.ofFinite α
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hterm (a : α) : Real.negMulLog ((uniformOfFinset s hs) a).toReal =
      if a ∈ s then (s.card : ℝ)⁻¹ * Real.log s.card else 0 := by
    by_cases ha : a ∈ s <;> simp [ha, Real.negMulLog, Real.log_inv]
  rw [entropy_eq_sum]
  simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    Real.logb]
  field_simp

omit [Fintype α] in
/-- A distribution supported on a finite set `s` has entropy at most `log₂ |s|`. This is Gibbs'
inequality against the uniform distribution on `s`. -/
theorem entropy_le_logb_card_of_support_subset [Finite α] (p : PMF α) {s : Finset α}
    (h : p.support ⊆ s) : entropy p ≤ Real.logb 2 s.card := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hs : s.Nonempty := ⟨a, h ha⟩
  refine (entropy_le_sum_mul_surprisal (q := uniformOfFinset s hs)
    fun b hb => (mem_support_uniformOfFinset_iff hs b).mpr (h hb)).trans_eq ?_
  have hterm (b : α) : (p b).toReal * surprisal (uniformOfFinset s hs) b =
      (p b).toReal * Real.logb 2 s.card := by
    by_cases hb : p b = 0
    · simp [hb]
    · simp [surprisal, show b ∈ s from h hb, Real.logb_inv]
  simp only [hterm, ← Finset.sum_mul, sum_toReal, one_mul]

/-- Entropy is the logarithm of the alphabet size minus the divergence from the uniform
distribution, converted to bits. -/
theorem entropy_eq_logb_card_sub_klDiv [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) :
    entropy p = Real.logb 2 (Fintype.card α) -
      (klDiv p.toMeasure (PMF.uniformOfFintype α).toMeasure).toReal / Real.log 2 := by
  rw [toReal_klDiv_toMeasure fun _ _ => by simp [PMF.mem_support_iff], entropy_eq_sum_surprisal]
  have hcard : (0 : ℝ) < Fintype.card α := mod_cast Fintype.card_pos
  have hterm (a : α) : (p a).toReal * Real.log ((p a).toReal /
      ((PMF.uniformOfFintype α) a).toReal) / Real.log 2 =
        (p a).toReal * Real.logb 2 (Fintype.card α) - (p a).toReal * surprisal p a := by
    by_cases hp : p a = 0
    · simp [hp]
    have hp' : (p a).toReal ≠ 0 := by ennreal_to_real using hp
    simp only [PMF.uniformOfFintype_apply]
    ennreal_to_real
    simp only [div_inv_eq_mul, surprisal, Real.logb, Real.log_mul hp' hcard.ne']
    ring
  simp only [Finset.sum_div, hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal,
    one_mul]
  ring

end Gibbs

/-! ### Mutual information and subadditivity -/

section MutualInformation

/-- A joint law is supported where the product of its marginals is. -/
theorem support_subset_bind_map_prodMk (joint : PMF (α × β)) :
    joint.support ⊆
      ((joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·)).support := by
  intro pair hpair
  rw [PMF.mem_support_iff, bind_map_prodMk_apply]
  exact mul_ne_zero
    (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hpair) (le_map_apply joint _ pair)))
    (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hpair) (le_map_apply joint _ pair)))

/-- **Mutual information** `I(X; Y) = H(X) + H(Y) - H(X, Y)`, in bits, is the divergence of
the joint law from the product of its marginals. -/
theorem entropy_map_fst_add_entropy_map_snd_sub_entropy [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (joint : PMF (α × β)) :
    entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint =
      (klDiv joint.toMeasure
        ((joint.map Prod.fst).toMeasure.prod (joint.map Prod.snd).toMeasure)).toReal /
          Real.log 2 := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [← toMeasure_bind_pair, toReal_klDiv_toMeasure (support_subset_bind_map_prodMk joint)]
  have hterm (pair : α × β) : (joint pair).toReal * Real.log ((joint pair).toReal /
      (((joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·)) pair).toReal) =
        -Real.negMulLog (joint pair).toReal -
          (joint pair).toReal * Real.log ((joint.map Prod.fst) pair.1).toReal -
            (joint pair).toReal * Real.log ((joint.map Prod.snd) pair.2).toReal := by
    by_cases hp : joint pair = 0
    · simp [hp]
    have hp' : (joint pair).toReal ≠ 0 := by ennreal_to_real using hp
    have h1 : ((joint.map Prod.fst) pair.1).toReal ≠ 0 := by
      ennreal_to_real using
        ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp) (le_map_apply joint Prod.fst pair))
    have h2 : ((joint.map Prod.snd) pair.2).toReal ≠ 0 := by
      ennreal_to_real using
        ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp) (le_map_apply joint Prod.snd pair))
    rw [bind_map_prodMk_apply]
    ennreal_to_real
    rw [Real.log_div hp' (mul_ne_zero h1 h2), Real.log_mul h1 h2, Real.negMulLog]
    ring
  simp only [hterm, Finset.sum_sub_distrib]
  rw [← sum_map_mul joint Prod.fst (fun a => Real.log ((joint.map Prod.fst) a).toReal),
    ← sum_map_mul joint Prod.snd (fun b => Real.log ((joint.map Prod.snd) b).toReal)]
  simp only [entropy_eq_sum, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

variable [Finite α] [Finite β]

/-- **Conditioning reduces entropy**: the entropy of the second component given the first is
at most its unconditional entropy. -/
theorem conditionalEntropy_le_entropy_map_snd (joint : PMF (α × β)) :
    conditionalEntropy joint ≤ entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_map_fst_ge joint (fun _ => ())
  rwa [show joint.map (fun pair => ((), pair.2)) = (joint.map Prod.snd).map ((), ·) by
    rw [PMF.map_comp]; rfl, conditionalEntropy_map_const] at h

/-- **Subadditivity of entropy**: the joint entropy is at most the sum of the marginal
entropies ([CoverThomas2006], Theorem 2.6.6 for two variables). -/
theorem entropy_le_entropy_map_fst_add_entropy_map_snd (joint : PMF (α × β)) :
    entropy joint ≤ entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_le_entropy_map_snd joint
  rw [conditionalEntropy] at h
  linarith

/-- Subadditivity of entropy is an equality exactly for independent pairs, whose joint law is
the product of its marginals. -/
theorem entropy_eq_entropy_map_fst_add_entropy_map_snd_iff (joint : PMF (α × β)) :
    entropy joint = entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) ↔
      joint = (joint.map Prod.fst).bind fun a => (joint.map Prod.snd).map (a, ·) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have h := entropy_map_fst_add_entropy_map_snd_sub_entropy joint
  rw [← toMeasure_bind_pair] at h
  refine ⟨fun heq => ?_, fun heq => ?_⟩
  · have h0 : (klDiv joint.toMeasure ((joint.map Prod.fst).bind
        fun a => (joint.map Prod.snd).map (a, ·)).toMeasure).toReal = 0 := by
      rw [show entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint = 0
        by linarith, eq_comm, div_eq_zero_iff] at h
      exact h.resolve_right (Real.log_pos (by norm_num)).ne'
    have hfin := klDiv_toMeasure_ne_top_iff.mpr (support_subset_bind_map_prodMk joint)
    exact PMF.toMeasure_injective (klDiv_eq_zero_iff.mp (by ennreal_to_real using h0))
  · rw [← heq, klDiv_self, ENNReal.toReal_zero, zero_div] at h; linarith

end MutualInformation

/-! ### Pinsker's inequality -/

section Pinsker

variable [Fintype α]

/-- **Pinsker's inequality** for finite distributions: twice the squared statistical distance
is at most the Kullback–Leibler divergence, in nats. -/
theorem ofReal_two_mul_dist_sq_le_klDiv [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : ENNReal.ofReal (2 * dist p q ^ 2) ≤ klDiv p.toMeasure q.toMeasure := by
  rw [dist_eq_tvDist_toMeasure_div_two,
    show 2 * (tvDist p.toMeasure q.toMeasure / 2) ^ 2 =
      tvDist p.toMeasure q.toMeasure ^ 2 / 2 by ring]
  exact ofReal_tvDist_sq_div_two_le_klDiv p.toMeasure q.toMeasure

/-- **Pinsker's inequality** with a finite-sum divergence. -/
theorem two_mul_dist_sq_le_sum_mul_log_div {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * dist p q ^ 2 ≤ ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := by
  let : MeasurableSpace α := ⊤
  exact (ENNReal.ofReal_le_ofReal_iff (sum_mul_log_div_nonneg h)).mp
    (klDiv_toMeasure_eq_ofReal h ▸ ofReal_two_mul_dist_sq_le_klDiv p q)

/-- **Pinsker's inequality** in its usual form: statistical distance is at most
`sqrt (D(p ‖ q) / 2)`, the divergence in nats. -/
theorem dist_le_sqrt_toReal_klDiv_div_two [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    dist p q ≤ Real.sqrt ((klDiv p.toMeasure q.toMeasure).toReal / 2) := by
  rw [toReal_klDiv_toMeasure h]
  apply Real.le_sqrt_of_sq_le
  linarith [two_mul_dist_sq_le_sum_mul_log_div h]

end Pinsker

end PMF

end Cslib.Probability
