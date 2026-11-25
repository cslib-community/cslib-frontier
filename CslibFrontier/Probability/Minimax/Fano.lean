/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Divergence.Pi
public import CslibFrontier.Probability.Entropy.Fano
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-!
# Generalized Fano minimax lower-bound framework

**Fano's minimax method** reduces estimation over a parameter space `Θ` to `M`-ary hypothesis
testing over a `2Δ`-separated finite packing `θ : V → Θ` (`|V| ≥ 2`), then lower-bounds the
testing error probability via Fano's inequality
(`Cslib.Probability.PMF.conditionalEntropy_le_one_add_mul_logb`) and upper-bounds the
observation–parameter mutual information via KL divergence
(`Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_le_sum_klDiv`,
`Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_le_sum_sum_klDiv`) ([Tsybakov2009], Sections
2.6–2.7; [CoverThomas2006], Section 2.10).

## Main results

* `Cslib.Probability.PMF.fano_binEntropy_testing_bound`: sharp binary-entropy form
  `log₂ |V| - I(X; V) ≤ h₂(Pe) + Pe · log₂ (|V| - 1)` under uniform prior on `V`.
* `Cslib.Probability.PMF.fano_avg_testing_error_ge_of_mutualInfo`: closed-form average testing error
  bound `1 - (I(X; V) · log 2 + log 2) / log |V| ≤ Pe` for `2 ≤ |V|`.
* `Cslib.Probability.PMF.fano_avg_testing_error_ge_of_klDiv_center`,
  `Cslib.Probability.PMF.fano_avg_testing_error_ge_of_klDiv_pairwise`: KL-center (Yang–Barron) and
  pairwise-KL hypothesis-testing lower bounds.
* `Cslib.Probability.PMF.fano_minimax_prob_ge_of_klDiv_center`: high-probability minimax estimation
  lower bound `∃ v, 1 - (β + log 2) / log |V| ≤ Pr_{P v}[Δ ≤ loss (est X) (θ v)]`.
* `Cslib.Probability.PMF.fano_minimax_risk_ge_of_klDiv_center`,
  `Cslib.Probability.PMF.fano_minimax_risk_ge_of_klDiv_pairwise`,
  `Cslib.Probability.PMF.fano_randomized_minimax_risk_ge_of_klDiv_center`,
  `Cslib.Probability.PMF.fano_iid_minimax_risk_ge_of_klDiv_pairwise`: deterministic, randomized, and
  `n`-sample i.i.d. expected-risk Fano minimax lower bounds `Δ · (1 - (β + log 2) / log |V|)`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 2.10.
* [A. B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Sections 2.6–2.7.
-/

public section

namespace Cslib.Probability.PMF

open Finset MeasureTheory InformationTheory
open scoped BigOperators ENNReal

section Testing

variable {V X : Type*} [Fintype V] [Finite X]

private theorem joint_error_eq_avg [Nonempty V] (P : V → PMF X) (ψ : X → V) :
    (((uniformOfFintype V).bind fun v => (P v).map (·, v)).toOuterMeasure
        {z : X × V | ψ z.1 ≠ z.2}).toReal =
      (Fintype.card V : ℝ)⁻¹ *
        ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal := by
  classical
  let _ := Fintype.ofFinite X
  have hjoint_apply (x : X) (v : V) :
      (((uniformOfFintype V).bind fun v => (P v).map (·, v)) (x, v)).toReal =
        (Fintype.card V : ℝ)⁻¹ * (P v x).toReal := by
    rw [toReal_bind_map_prodMk_apply, uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  rw [toOuterMeasure_apply_toReal, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Set.mem_ofPred_eq, hjoint_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [toOuterMeasure_apply_toReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> ring

/-- **Sharp binary-entropy Fano bound** under a uniform prior on `V`: for a channel `P : V → PMF X`
and decoder `ψ : X → V` with average error probability `Pe`,
`log₂ |V| - I(X; V) ≤ h₂(Pe) + Pe · log₂ (|V| - 1)`. -/
theorem fano_binEntropy_testing_bound [Nonempty V] (P : V → PMF X) (ψ : X → V) :
    let Pe := (Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal
    Real.logb 2 (Fintype.card V) -
        mutualInfo ((uniformOfFintype V).bind fun v => (P v).map (·, v)) ≤
      Real.binEntropy Pe / Real.log 2 + Pe * Real.logb 2 (Fintype.card V - 1) := by
  intro Pe
  let joint : PMF (X × V) := (uniformOfFintype V).bind fun v => (P v).map (·, v)
  have hfano := conditionalEntropy_le_binEntropy_add_mul_logb joint ψ
  have hmi := mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy joint
  rw [map_snd_bind_prodMk (uniformOfFintype V) P, entropy_uniform] at hmi
  rw [joint_error_eq_avg P ψ] at hfano
  linarith

/-- **Mutual-information Fano testing lower bound**: for `2 ≤ |V|`, any channel `P : V → PMF X`, and
any decoder `ψ : X → V`, the average testing error probability is at least
`1 - (I(X; V) · log 2 + log 2) / log |V|`. -/
theorem fano_avg_testing_error_ge_of_mutualInfo [Nonempty V] (hV : 2 ≤ Fintype.card V)
    (P : V → PMF X) (ψ : X → V) :
    1 - (mutualInfo ((uniformOfFintype V).bind fun v => (P v).map (·, v)) * Real.log 2 +
          Real.log 2) / Real.log (Fintype.card V) ≤
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal := by
  set joint : PMF (X × V) := (uniformOfFintype V).bind fun v => (P v).map (·, v)
  have hfano := conditionalEntropy_le_one_add_mul_logb joint ψ
  have hmi := mutualInfo_eq_entropy_map_snd_sub_conditionalEntropy joint
  rw [map_snd_bind_prodMk (uniformOfFintype V) P, entropy_uniform] at hmi
  rw [joint_error_eq_avg P ψ] at hfano
  set Pe := (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard_gt : (1 : ℝ) < Fintype.card V := by exact_mod_cast (show 1 < Fintype.card V by omega)
  have hlogV : 0 < Real.log (Fintype.card V) := Real.log_pos hcard_gt
  have hcond : Real.logb 2 (Fintype.card V) - mutualInfo joint ≤
      1 + Pe * Real.logb 2 (Fintype.card V) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcond hlog2.le
  rw [sub_mul, add_mul, one_mul, mul_assoc, Real.logb, div_mul_cancel₀ _ hlog2.ne'] at hmul
  rw [sub_div' hlogV.ne', one_mul, div_le_iff₀ hlogV]
  linarith

private theorem fano_avg_testing_error_ge_of_mutualInfo_le [Nonempty V] (hV : 2 ≤ Fintype.card V)
    (P : V → PMF X) {β : ℝ}
    (hmi_le : mutualInfo ((uniformOfFintype V).bind fun v => (P v).map (·, v)) * Real.log 2 ≤ β)
    (ψ : X → V) :
    1 - (β + Real.log 2) / Real.log (Fintype.card V) ≤
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal := by
  have hlogV : 0 < Real.log (Fintype.card V) :=
    Real.log_pos (by exact_mod_cast (show 1 < Fintype.card V by omega))
  have hdiv : (mutualInfo ((uniformOfFintype V).bind fun v => (P v).map (·, v)) * Real.log 2 +
        Real.log 2) / Real.log (Fintype.card V) ≤
      (β + Real.log 2) / Real.log (Fintype.card V) :=
    div_le_div_of_nonneg_right (by linarith) hlogV.le
  exact (by linarith : 1 - (β + Real.log 2) / Real.log (Fintype.card V) ≤ _).trans
    (fano_avg_testing_error_ge_of_mutualInfo hV P ψ)

/-- **KL-center Fano testing lower bound** (Yang–Barron / [Tsybakov2009], Section 2.6): if a
reference distribution `Q : PMF X` dominates every `P v` and the average divergence satisfies
`|V|⁻¹ · ∑ v, D(P v ‖ Q) ≤ β`, then average testing error is at least
`1 - (β + log 2) / log |V|`. -/
theorem fano_avg_testing_error_ge_of_klDiv_center [MeasurableSpace X] [MeasurableSingletonClass X]
    (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {Q : PMF X} {β : ℝ}
    (hQ : ∀ v, (P v).support ⊆ Q.support)
    (hβ : (Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, (klDiv (P v).toMeasure Q.toMeasure).toReal ≤ β)
    (ψ : X → V) :
    1 - (β + Real.log 2) / Real.log (Fintype.card V) ≤
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine fano_avg_testing_error_ge_of_mutualInfo_le hV P ?_ ψ
  refine (mutualInfo_bind_mul_log_two_le_sum_klDiv (uniformOfFintype V) P
    fun v _ => hQ v).trans ?_
  have hunif (v : V) : (uniformOfFintype V v).toReal = (Fintype.card V : ℝ)⁻¹ := by
    rw [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [hunif, ← Finset.mul_sum]
  exact hβ

/-- **Pairwise KL-Fano testing lower bound**: if `(P v).support ⊆ (P w).support` and the average
pairwise divergence satisfies `(|V| : ℝ)⁻² · ∑ v, ∑ w, D(P v ‖ P w) ≤ β`, then average testing error
is at least `1 - (β + log 2) / log |V|`. -/
theorem fano_avg_testing_error_ge_of_klDiv_pairwise [MeasurableSpace X] [MeasurableSingletonClass X]
    (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {β : ℝ}
    (hsupp : ∀ v w, (P v).support ⊆ (P w).support)
    (hβ : ((Fintype.card V : ℝ) ^ 2)⁻¹ *
      ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal ≤ β)
    (ψ : X → V) :
    1 - (β + Real.log 2) / Real.log (Fintype.card V) ≤
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine fano_avg_testing_error_ge_of_mutualInfo_le hV P ?_ ψ
  refine (mutualInfo_bind_mul_log_two_le_sum_sum_klDiv (uniformOfFintype V) P
    fun v _ w _ => hsupp v w).trans ?_
  have hunif (v : V) : (uniformOfFintype V v).toReal = (Fintype.card V : ℝ)⁻¹ := by
    rw [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hpull : (∑ v : V, ∑ w : V,
      (uniformOfFintype V v).toReal * (uniformOfFintype V w).toReal *
        (klDiv (P v).toMeasure (P w).toMeasure).toReal) =
      ((Fintype.card V : ℝ) ^ 2)⁻¹ *
        ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal := by
    simp only [hunif]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hpull]
  exact hβ

end Testing

/-! ### Packing-to-estimation reduction and minimax risk lower bounds -/

section Estimation

variable {V X T Θ : Type*}

/-- Given a `2Δ`-packing `θ : V → Θ` (`v ≠ w → 2 Δ ≤ loss t (θ v) + loss t (θ w)`), minimum-loss
decoding `argmin_v loss (est x) (θ v)` errs only when `Δ ≤ loss (est x) (θ v)`. -/
private theorem exists_decoder_err_imp_ge [Finite V] [Nonempty V] {loss : T → Θ → ℝ} {θ : V → Θ}
    {Δ : ℝ} (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → T) :
    ∃ ψ : X → V, ∀ x v, ψ x ≠ v → Δ ≤ loss (est x) (θ v) := by
  classical
  let _ := Fintype.ofFinite V
  let ψ : X → V := fun x =>
    (Finset.exists_min_image Finset.univ (fun v => loss (est x) (θ v)) Finset.univ_nonempty).choose
  refine ⟨ψ, fun x v hne => ?_⟩
  have hspec :=
    (Finset.exists_min_image Finset.univ (fun v => loss (est x) (θ v))
      Finset.univ_nonempty).choose_spec.2 v (Finset.mem_univ v)
  have hsum := hpack (est x) (ψ x) v hne
  change loss (est x) (θ (ψ x)) ≤ loss (est x) (θ v) at hspec
  linarith

private theorem exists_mem_ge_of_avg_ge [Fintype V] [Nonempty V] {f : V → ℝ} {c : ℝ}
    (h : c ≤ (Fintype.card V : ℝ)⁻¹ * ∑ v : V, f v) :
    ∃ v : V, c ≤ f v := by
  have hsum : ∑ _ : V, c ≤ ∑ v : V, f v := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (le_inv_mul_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mp h
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨v, hv⟩

variable [Fintype V]

/-- **High-probability KL-Fano minimax lower bound**: if `θ : V → Θ` (`2 ≤ |V|`) is `2Δ`-separated
under `loss` and `|V|⁻¹ · ∑ v, D(P v ‖ Q) ≤ β`, then for every estimator `est : X → T` there exists
`v : V` with `Pr_{X ~ P v}[Δ ≤ loss (est X) (θ v)] ≥ 1 - (β + log 2) / log |V|`. -/
theorem fano_minimax_prob_ge_of_klDiv_center [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {Q : PMF X} {β : ℝ}
    (hQ : ∀ v, (P v).support ⊆ Q.support)
    (hβ : (Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, (klDiv (P v).toMeasure Q.toMeasure).toReal ≤ β)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ}
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → T) :
    ∃ v : V, 1 - (β + Real.log 2) / Real.log (Fintype.card V) ≤
      ((P v).toOuterMeasure {x : X | Δ ≤ loss (est x) (θ v)}).toReal := by
  classical
  let _ := Fintype.ofFinite X
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ψ, hψ⟩ := exists_decoder_err_imp_ge hpack est
  have havg := fano_avg_testing_error_ge_of_klDiv_center hV P hQ hβ ψ
  obtain ⟨v, hv⟩ := exists_mem_ge_of_avg_ge havg
  refine ⟨v, hv.trans ?_⟩
  rw [toOuterMeasure_apply_toReal, toOuterMeasure_apply_toReal]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [Set.mem_ofPred_eq]
  by_cases herr : ψ x ≠ v
  · rw [ite_eq_left herr, ite_eq_left (hψ x v herr)]
  · rw [ite_eq_right herr]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

private theorem minimax_risk_ge_of_avg_testing_error [Fintype X] [Nonempty V]
    (P : V → PMF X) {c : ℝ}
    (havg : ∀ ψ : X → V,
      c ≤ (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ((P v).toOuterMeasure {x : X | ψ x ≠ v}).toReal)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hloss : ∀ t v, 0 ≤ loss t (θ v))
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → T) :
    ∃ v : V, Δ * c ≤ ∑ x : X, (P v x).toReal * loss (est x) (θ v) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_decoder_err_imp_ge hpack est
  obtain ⟨v, hv⟩ := exists_mem_ge_of_avg_ge (havg ψ)
  refine ⟨v, (mul_le_mul_of_nonneg_left hv hΔ).trans ?_⟩
  rw [toOuterMeasure_apply_toReal, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [Set.mem_ofPred_eq]
  by_cases hx : ψ x ≠ v
  · rw [ite_eq_left hx, mul_comm]
    exact mul_le_mul_of_nonneg_left (hψ x v hx) ENNReal.toReal_nonneg
  · rw [ite_eq_right hx, mul_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (hloss (est x) v)

/-- **Expected-risk KL-center Fano minimax lower bound** ([Tsybakov2009], Theorem 2.5): if
`θ : V → Θ` (`2 ≤ |V|`) is `2Δ`-separated under a nonnegative `loss` (`Δ ≥ 0`) and
`|V|⁻¹ · ∑ v, D(P v ‖ Q) ≤ β`, then for every estimator `est : X → T` some `v : V` has expected risk
at least `Δ · (1 - (β + log 2) / log |V|)`. -/
theorem fano_minimax_risk_ge_of_klDiv_center [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {Q : PMF X} {β : ℝ}
    (hQ : ∀ v, (P v).support ⊆ Q.support)
    (hβ : (Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, (klDiv (P v).toMeasure Q.toMeasure).toReal ≤ β)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hloss : ∀ t v, 0 ≤ loss t (θ v))
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → T) :
    ∃ v : V, Δ * (1 - (β + Real.log 2) / Real.log (Fintype.card V)) ≤
      ∑ x : X, (P v x).toReal * loss (est x) (θ v) :=
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  minimax_risk_ge_of_avg_testing_error P (fano_avg_testing_error_ge_of_klDiv_center hV P hQ hβ)
    hΔ hloss hpack est

/-- **Randomized-estimator KL-center Fano minimax lower bound**: holds for every randomized
estimator `est : X → PMF T` by lifting `loss` linearly to `PMF T`. -/
theorem fano_randomized_minimax_risk_ge_of_klDiv_center [Fintype X] [Fintype T]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {Q : PMF X} {β : ℝ}
    (hQ : ∀ v, (P v).support ⊆ Q.support)
    (hβ : (Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, (klDiv (P v).toMeasure Q.toMeasure).toReal ≤ β)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hloss : ∀ t v, 0 ≤ loss t (θ v))
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → PMF T) :
    ∃ v : V, Δ * (1 - (β + Real.log 2) / Real.log (Fintype.card V)) ≤
      ∑ x : X, (P v x).toReal * ∑ t : T, (est x t).toReal * loss t (θ v) := by
  refine fano_minimax_risk_ge_of_klDiv_center hV P hQ hβ hΔ
    (loss := fun (q : PMF T) θ' => ∑ t : T, (q t).toReal * loss t θ')
    (fun q v => Finset.sum_nonneg fun t _ => mul_nonneg ENNReal.toReal_nonneg (hloss t v))
    (fun q v w hne => ?_) est
  rw [← Finset.sum_add_distrib]
  calc 2 * Δ = ∑ t : T, (q t).toReal * (2 * Δ) := by
        rw [← Finset.sum_mul, sum_toReal, one_mul]
    _ ≤ ∑ t : T, ((q t).toReal * loss t (θ v) + (q t).toReal * loss t (θ w)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hpack t v w hne) ENNReal.toReal_nonneg

/-- **Expected-risk pairwise KL-Fano minimax lower bound**: if `(P v).support ⊆ (P w).support` and
`(|V| : ℝ)⁻² · ∑ v, ∑ w, D(P v ‖ P w) ≤ β`, then for every estimator `est : X → T` some `v : V` has
expected risk at least `Δ · (1 - (β + log 2) / log |V|)`. -/
theorem fano_minimax_risk_ge_of_klDiv_pairwise [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (hV : 2 ≤ Fintype.card V) (P : V → PMF X) {β : ℝ}
    (hsupp : ∀ v w, (P v).support ⊆ (P w).support)
    (hβ : ((Fintype.card V : ℝ) ^ 2)⁻¹ *
      ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal ≤ β)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hloss : ∀ t v, 0 ≤ loss t (θ v))
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w)) (est : X → T) :
    ∃ v : V, Δ * (1 - (β + Real.log 2) / Real.log (Fintype.card V)) ≤
      ∑ x : X, (P v x).toReal * loss (est x) (θ v) :=
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  minimax_risk_ge_of_avg_testing_error P (fano_avg_testing_error_ge_of_klDiv_pairwise hV P hsupp hβ)
    hΔ hloss hpack est

/-- **I.i.d. `n`-sample pairwise KL-Fano minimax lower bound**: if single-sample laws satisfy
`(|V| : ℝ)⁻² · ∑ v, ∑ w, D(P v ‖ P w) ≤ β`, then from `n` i.i.d. observations some `v : V` incurs
expected risk at least `Δ · (1 - (n · β + log 2) / log |V|)`. -/
theorem fano_iid_minimax_risk_ge_of_klDiv_pairwise [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (hV : 2 ≤ Fintype.card V) (P : V → PMF X) (n : ℕ) {β : ℝ}
    (hsupp : ∀ v w, (P v).support ⊆ (P w).support)
    (hβ : ((Fintype.card V : ℝ) ^ 2)⁻¹ *
      ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal ≤ β)
    {loss : T → Θ → ℝ} {θ : V → Θ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hloss : ∀ t v, 0 ≤ loss t (θ v))
    (hpack : ∀ t, ∀ v w, v ≠ w → 2 * Δ ≤ loss t (θ v) + loss t (θ w))
    (est : (Fin n → X) → T) :
    ∃ v : V, Δ * (1 - (n * β + Real.log 2) / Real.log (Fintype.card V)) ≤
      ∑ x : Fin n → X, (iid (P v) n x).toReal * loss (est x) (θ v) := by
  refine fano_minimax_risk_ge_of_klDiv_pairwise hV (fun v => iid (P v) n)
    (fun v w => support_iid_subset (hsupp v w) n) ?_ hΔ hloss hpack est
  have hiid : (∑ v : V, ∑ w : V,
      (klDiv (iid (P v) n).toMeasure (iid (P w) n).toMeasure).toReal) =
      (n : ℝ) * ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal := by
    simp only [toReal_klDiv_iid (hsupp _ _) n]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
  rw [hiid]
  calc ((Fintype.card V : ℝ) ^ 2)⁻¹ *
        ((n : ℝ) * ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal)
      = (n : ℝ) * (((Fintype.card V : ℝ) ^ 2)⁻¹ *
          ∑ v : V, ∑ w : V, (klDiv (P v).toMeasure (P w).toMeasure).toReal) := by ring
    _ ≤ n * β := mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg n)

end Estimation

end Cslib.Probability.PMF
