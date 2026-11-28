/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.MutualInformation
public import CslibFrontier.Probability.Product
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Tensorization and mixture bounds for Kullback–Leibler divergence

For finite distributions, Kullback–Leibler divergence adds across independent coordinates
(`Cslib.Probability.PMF.toReal_klDiv_pi`) and scales by `n` on `n`-fold i.i.d. laws
(`Cslib.Probability.PMF.toReal_klDiv_iid`). Combined with Pinsker's inequality
(`Cslib.Probability.PMF.dist_le_sqrt_toReal_klDiv_div_two`), this bounds the statistical distance of
product and i.i.d. distributions in terms of single-coordinate divergences.

For a prior `μ : PMF V` and channel `P : V → PMF X`, the observation-first joint law
`μ.bind fun v => (P v).map (·, v)` satisfies the golden mixture identity
(`Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_eq_sum_klDiv_sub`): for every reference law `Q`
dominating the supported `P v`,
`I(X; V) · log 2 = (∑ v, μ v · D(P v ‖ Q)) - D(μ.bind P ‖ Q)`.
Dropping the nonnegative mixture divergence `D(μ.bind P ‖ Q)` yields the KL-center (Yang–Barron) and
pairwise-KL upper bounds on mutual information used in generalized Fano minimax lower bounds
([Tsybakov2009], Section 2.6; [CoverThomas2006], Chapter 2).

## Main results

* `Cslib.Probability.PMF.support_pi_subset_iff`: support inclusion of independent products.
* `Cslib.Probability.PMF.sum_mul_log_div_pi`, `Cslib.Probability.PMF.toReal_klDiv_pi`,
  `Cslib.Probability.PMF.toReal_klDiv_iid`: product and i.i.d. tensorization of KL divergence.
* `Cslib.Probability.PMF.dist_pi_le_sqrt_sum_klDiv_div_two`,
  `Cslib.Probability.PMF.dist_iid_le_sqrt_mul_klDiv_div_two`: product and i.i.d. Pinsker bounds.
* `Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_eq_sum_klDiv_sub`: exact decomposition of
  `I(X; V) · log 2` relative to an arbitrary dominating reference law `Q`.
* `Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_le_sum_klDiv`,
  `Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_le_of_klDiv_le`,
  `Cslib.Probability.PMF.mutualInfo_bind_mul_log_two_le_sum_sum_klDiv`: KL-center and pairwise-KL
  mutual-information bounds.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Chapter 2.
* [A. B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Sections 2.4 and 2.6.
-/

public section

namespace Cslib.Probability.PMF

open Finset MeasureTheory InformationTheory
open scoped BigOperators ENNReal

/-! ### Support inclusion and KL tensorization for independent products -/

section Product

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

/-- An independent product `pi p` has support contained in `(pi q).support` if and only if each
coordinate distribution `p i` has support contained in `(q i).support`. -/
theorem support_pi_subset_iff [∀ i, Finite (α i)] {p q : ∀ i, PMF (α i)} :
    (pi p).support ⊆ (pi q).support ↔ ∀ i, (p i).support ⊆ (q i).support := by
  classical
  refine ⟨fun h i a ha => ?_, fun h x hx =>
    (mem_support_pi_iff q x).2 fun i => h i ((mem_support_pi_iff p x).1 hx i)⟩
  choose x₀ hx₀ using fun j => (p j).support_nonempty
  have hmem : Function.update x₀ i a ∈ (pi p).support := (mem_support_pi_iff p _).2
    ((Function.forall_update_iff x₀ (p := fun j b => b ∈ (p j).support)).2 ⟨ha, fun j _ => hx₀ j⟩)
  simpa only [Function.update_self] using (mem_support_pi_iff q _).mp (h hmem) i

/-- Support inclusion transfers from `p, q` to `n`-fold i.i.d. laws `iid p n, iid q n`. -/
theorem support_iid_subset {β : Type*} {p q : PMF β} (h : p.support ⊆ q.support) (n : ℕ) :
    (iid p n).support ⊆ (iid q n).support := by
  intro x hx
  rw [mem_support_iid_iff] at hx ⊢
  exact fun i => h (hx i)

/-- Finite-sum Kullback–Leibler divergence is additive across independent coordinates. -/
theorem sum_mul_log_div_pi [DecidableEq ι] [∀ i, Fintype (α i)] {p q : ∀ i, PMF (α i)}
    (h : ∀ i, (p i).support ⊆ (q i).support) :
    ∑ x : (∀ i, α i), (pi p x).toReal * Real.log ((pi p x).toReal / (pi q x).toReal) =
      ∑ i, ∑ a : α i, (p i a).toReal * Real.log ((p i a).toReal / (q i a).toReal) := by
  have hterm (x : ∀ i, α i) :
      (pi p x).toReal * Real.log ((pi p x).toReal / (pi q x).toReal) =
        (pi p x).toReal * ∑ i, Real.log ((p i (x i)).toReal / (q i (x i)).toReal) := by
    by_cases h0 : ∀ i, p i (x i) ≠ 0
    · have hp_real : ∀ i, (p i (x i)).toReal ≠ 0 := fun i => by ennreal_to_real using h0 i
      have hq0 : ∀ i, q i (x i) ≠ 0 := fun i =>
        (PMF.mem_support_iff (q i) (x i)).mp (h i ((PMF.mem_support_iff (p i) (x i)).mpr (h0 i)))
      have hq_real : ∀ i, (q i (x i)).toReal ≠ 0 := fun i => by ennreal_to_real using hq0 i
      rw [pi_apply, pi_apply, ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_div_distrib,
        Real.log_prod fun i _ => div_ne_zero (hp_real i) (hq_real i)]
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      simp [pi_apply, Finset.prod_eq_zero (f := fun j => (p j (x j)).toReal) (Finset.mem_univ i)
        (by simp [hi])]
  simp only [hterm]
  exact sum_pi_mul_sum p fun i a => Real.log ((p i a).toReal / (q i a).toReal)

/-- **Tensorization of Kullback–Leibler divergence** for independent finite products:
`D(∏ᵢ pᵢ ‖ ∏ᵢ qᵢ) = ∑ᵢ D(pᵢ ‖ qᵢ)`, in nats. -/
theorem toReal_klDiv_pi [∀ i, Finite (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] {p q : ∀ i, PMF (α i)}
    (h : ∀ i, (p i).support ⊆ (q i).support) :
    (klDiv (pi p).toMeasure (pi q).toMeasure).toReal =
      ∑ i, (klDiv (p i).toMeasure (q i).toMeasure).toReal := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  rw [toReal_klDiv_toMeasure (support_pi_subset_iff.mpr h), sum_mul_log_div_pi h]
  exact Finset.sum_congr rfl fun i _ => (toReal_klDiv_toMeasure (h i)).symm

/-- **Tensorization of Kullback–Leibler divergence** for `n`-fold i.i.d. distributions:
`D(p^{⊗ n} ‖ q^{⊗ n}) = n · D(p ‖ q)`, in nats. -/
theorem toReal_klDiv_iid {β : Type*} [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {p q : PMF β} (h : p.support ⊆ q.support) (n : ℕ) :
    (klDiv (iid p n).toMeasure (iid q n).toMeasure).toReal =
      n * (klDiv p.toMeasure q.toMeasure).toReal := by
  rw [iid_eq_pi, iid_eq_pi, toReal_klDiv_pi fun _ => h, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul]

/-- **Product Pinsker bound**: statistical distance between independent finite products is at most
`√((∑ᵢ D(pᵢ ‖ qᵢ)) / 2)`. -/
theorem dist_pi_le_sqrt_sum_klDiv_div_two [DecidableEq ι] [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] {p q : ∀ i, PMF (α i)}
    (h : ∀ i, (p i).support ⊆ (q i).support) :
    dist (pi p) (pi q) ≤
      Real.sqrt ((∑ i, (klDiv (p i).toMeasure (q i).toMeasure).toReal) / 2) := by
  rw [← toReal_klDiv_pi h]
  exact dist_le_sqrt_toReal_klDiv_div_two (support_pi_subset_iff.mpr h)

/-- **I.i.d. Pinsker bound**: statistical distance between `n`-fold i.i.d. laws is at most
`√(n · D(p ‖ q) / 2)`. -/
theorem dist_iid_le_sqrt_mul_klDiv_div_two {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {p q : PMF β} (h : p.support ⊆ q.support) (n : ℕ) :
    dist (iid p n) (iid q n) ≤ Real.sqrt (n * (klDiv p.toMeasure q.toMeasure).toReal / 2) := by
  rw [← toReal_klDiv_iid h n]
  exact dist_le_sqrt_toReal_klDiv_div_two (support_iid_subset h n)

end Product

/-! ### Mixture KL identity and mutual-information radius bounds -/

section MixtureKL

variable {V X : Type*}

/-- First marginal of the observation-first joint law `μ.bind fun v => (P v).map (·, v)`. -/
theorem map_fst_bind_prodMk (μ : PMF V) (P : V → PMF X) :
    (μ.bind fun v => (P v).map (·, v)).map Prod.fst = μ.bind P := by
  rw [_root_.PMF.map_bind]
  exact congrArg μ.bind (funext fun v => (_root_.PMF.map_comp _ _ _).trans (_root_.PMF.map_id _))

/-- Second marginal of the observation-first joint law `μ.bind fun v => (P v).map (·, v)`. -/
theorem map_snd_bind_prodMk (μ : PMF V) (P : V → PMF X) :
    (μ.bind fun v => (P v).map (·, v)).map Prod.snd = μ := by
  simpa only [_root_.PMF.map_bind, _root_.PMF.bind_pure] using congrArg μ.bind
    (funext fun v => (_root_.PMF.map_comp (·, v) (P v) Prod.snd).trans
      (_root_.PMF.map_const (P v) v))

/-- Real probability mass of the observation-first joint law `μ.bind fun v => (P v).map (·, v)` at
`(x, v)`. -/
theorem toReal_bind_map_prodMk_apply (μ : PMF V) (P : V → PMF X) (x : X) (v : V) :
    ((μ.bind fun v => (P v).map (·, v)) (x, v)).toReal = (μ v).toReal * (P v x).toReal := by
  have h := congrArg ENNReal.toReal
    (map_equiv_apply (μ.bind fun w => (P w).map (w, ·)) (Equiv.prodComm V X) (x, v))
  simpa only [_root_.PMF.map_bind, _root_.PMF.map_comp, Function.comp_def, Equiv.prodComm_apply,
    Equiv.prodComm_symm, Prod.swap_prod_mk, bind_map_prodMk_apply, ENNReal.toReal_mul] using h

private theorem support_bind_subset_of_forall {μ : PMF V} {P : V → PMF X} {Q : PMF X}
    (hQ : ∀ v ∈ μ.support, (P v).support ⊆ Q.support) :
    (μ.bind P).support ⊆ Q.support := fun x hx =>
  let ⟨v, hv, hxv⟩ := (_root_.PMF.mem_support_bind_iff μ P x).1 hx
  hQ v hv hxv

/-- **Golden mixture identity for mutual information**: for a prior `μ : PMF V`, channel
`P : V → PMF X`, and any reference distribution `Q : PMF X` dominating `P v` on `μ.support`,
`I(X; V) · log 2 = (∑ v, μ v · D(P v ‖ Q)) - D(μ.bind P ‖ Q)` on the observation-first joint law
`μ.bind fun v => (P v).map (·, v)`. -/
theorem mutualInfo_bind_mul_log_two_eq_sum_klDiv_sub [Fintype V] [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : PMF V) (P : V → PMF X) {Q : PMF X}
    (hQ : ∀ v ∈ μ.support, (P v).support ⊆ Q.support) :
    mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2 =
      (∑ v, (μ v).toReal * (klDiv (P v).toMeasure Q.toMeasure).toReal) -
        (klDiv (μ.bind P).toMeasure Q.toMeasure).toReal := by
  classical
  let _ := Fintype.ofFinite X
  let : MeasurableSpace V := ⊤
  let joint : PMF (X × V) := μ.bind fun v => (P v).map (·, v)
  have hlog : (Real.log 2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hmi : mutualInfo joint * Real.log 2 =
      ∑ p : X × V, (joint p).toReal *
        Real.log ((joint p).toReal /
          (((joint.map Prod.fst) p.1).toReal * ((joint.map Prod.snd) p.2).toReal)) := by
    have hdiv := entropy_map_fst_add_entropy_map_snd_sub_entropy joint
    rw [← toMeasure_bind_pair,
      toReal_klDiv_toMeasure (support_subset_bind_map_prodMk joint)] at hdiv
    have h1 : mutualInfo joint =
        entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint := by
      simpa only [Prod.mk.eta, ← Function.id_def, _root_.PMF.map_id] using
        mutualInfo_map joint Prod.fst Prod.snd
    rw [h1, hdiv, div_mul_cancel₀ _ hlog]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : joint p = 0
    · simp [hp]
    · rw [bind_map_prodMk_apply, ENNReal.toReal_mul]
  rw [hmi, map_fst_bind_prodMk, map_snd_bind_prodMk,
    toReal_klDiv_toMeasure (support_bind_subset_of_forall hQ)]
  have hbar_apply (x : X) : ((μ.bind P) x).toReal = ∑ v, (μ v).toReal * (P v x).toReal := by
    rw [_root_.PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun v _ =>
      ENNReal.mul_ne_top (μ.apply_ne_top v) ((P v).apply_ne_top x)]
    exact Finset.sum_congr rfl fun v _ => ENNReal.toReal_mul
  rw [Fintype.sum_prod_type]
  have hsplit (x : X) (v : V) :
      (joint (x, v)).toReal *
          Real.log ((joint (x, v)).toReal / (((μ.bind P) x).toReal * (μ v).toReal)) =
        (μ v).toReal * ((P v x).toReal * Real.log ((P v x).toReal / (Q x).toReal)) -
          (μ v).toReal * (P v x).toReal * Real.log (((μ.bind P) x).toReal / (Q x).toReal) := by
    rw [toReal_bind_map_prodMk_apply μ P x v]
    by_cases hμv : μ v = 0
    · simp [hμv]
    by_cases hPvx : P v x = 0
    · simp [hPvx]
    have hx_bar : (μ.bind P) x ≠ 0 := (_root_.PMF.mem_support_iff _ _).mp
      ((_root_.PMF.mem_support_bind_iff μ P x).mpr ⟨v, hμv, hPvx⟩)
    have hμv_r : (μ v).toReal ≠ 0 := by ennreal_to_real using hμv
    have hPvx_r : (P v x).toReal ≠ 0 := by ennreal_to_real using hPvx
    have hQx_r : (Q x).toReal ≠ 0 := by
      ennreal_to_real using (_root_.PMF.mem_support_iff Q x).mp (hQ v hμv hPvx)
    have hbar_r : ((μ.bind P) x).toReal ≠ 0 := by ennreal_to_real using hx_bar
    have hratio : ((μ v).toReal * (P v x).toReal) / (((μ.bind P) x).toReal * (μ v).toReal) =
        ((P v x).toReal / (Q x).toReal) / (((μ.bind P) x).toReal / (Q x).toReal) := by field_simp
    rw [hratio, Real.log_div (div_ne_zero hPvx_r hQx_r) (div_ne_zero hbar_r hQx_r)]; ring
  simp only [hsplit, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ μ.support
    · rw [← Finset.mul_sum, toReal_klDiv_toMeasure (hQ v hv)]
    · simp [(_root_.PMF.apply_eq_zero_iff μ v).mpr hv]
  · exact Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_mul, hbar_apply x]

/-- **KL-center upper bound on mutual information** (Yang–Barron / [Tsybakov2009], Section 2.6):
for any reference law `Q` dominating `P v` on `μ.support`,
`I(X; V) · log 2 ≤ ∑ v, μ v · D(P v ‖ Q)`. -/
theorem mutualInfo_bind_mul_log_two_le_sum_klDiv [Fintype V] [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : PMF V) (P : V → PMF X) {Q : PMF X}
    (hQ : ∀ v ∈ μ.support, (P v).support ⊆ Q.support) :
    mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2 ≤
      ∑ v, (μ v).toReal * (klDiv (P v).toMeasure Q.toMeasure).toReal := by
  rw [mutualInfo_bind_mul_log_two_eq_sum_klDiv_sub μ P hQ]
  linarith [ENNReal.toReal_nonneg (a := klDiv (μ.bind P).toMeasure Q.toMeasure)]

/-- **KL-radius upper bound on mutual information**: if `D(P v ‖ Q) ≤ β` for every `v ∈ μ.support`,
then `I(X; V) · log 2 ≤ β`. -/
theorem mutualInfo_bind_mul_log_two_le_of_klDiv_le [Finite V] [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : PMF V) (P : V → PMF X) {Q : PMF X} {β : ℝ}
    (hQ : ∀ v ∈ μ.support, (P v).support ⊆ Q.support)
    (hβ : ∀ v ∈ μ.support, (klDiv (P v).toMeasure Q.toMeasure).toReal ≤ β) :
    mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2 ≤ β := by
  let _ := Fintype.ofFinite V
  refine (mutualInfo_bind_mul_log_two_le_sum_klDiv μ P hQ).trans ?_
  calc ∑ v, (μ v).toReal * (klDiv (P v).toMeasure Q.toMeasure).toReal
      ≤ ∑ v, (μ v).toReal * β := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : v ∈ μ.support
        · exact mul_le_mul_of_nonneg_left (hβ v hv) ENNReal.toReal_nonneg
        · simp [(_root_.PMF.apply_eq_zero_iff μ v).mpr hv]
    _ = β := by rw [← Finset.sum_mul, sum_toReal, one_mul]

/-- **Pairwise-KL upper bound on mutual information**: when `P v` and `P w` have matching supports
across `μ.support`, `I(X; V) · log 2 ≤ ∑ v, ∑ w, μ v · μ w · D(P v ‖ P w)`. -/
theorem mutualInfo_bind_mul_log_two_le_sum_sum_klDiv [Fintype V] [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : PMF V) (P : V → PMF X)
    (hsupp : ∀ v ∈ μ.support, ∀ w ∈ μ.support, (P v).support ⊆ (P w).support) :
    mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2 ≤
      ∑ v, ∑ w, (μ v).toReal * (μ w).toReal * (klDiv (P v).toMeasure (P w).toMeasure).toReal := by
  have hper_w (w : V) :
      (μ w).toReal * (mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2) ≤
        ∑ v, (μ v).toReal * (μ w).toReal * (klDiv (P v).toMeasure (P w).toMeasure).toReal := by
    by_cases hw : w ∈ μ.support
    · have hle := mutualInfo_bind_mul_log_two_le_sum_klDiv μ P (Q := P w) fun v hv =>
        hsupp v hv w hw
      calc (μ w).toReal * (mutualInfo (μ.bind fun v => (P v).map (·, v)) * Real.log 2)
          ≤ (μ w).toReal * ∑ v, (μ v).toReal * (klDiv (P v).toMeasure (P w).toMeasure).toReal :=
            mul_le_mul_of_nonneg_left hle ENNReal.toReal_nonneg
        _ = ∑ v, (μ v).toReal * (μ w).toReal *
              (klDiv (P v).toMeasure (P w).toMeasure).toReal := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun v _ => by ring
    · simp [(_root_.PMF.apply_eq_zero_iff μ w).mpr hw]
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hper_w w
  rwa [← Finset.sum_mul, sum_toReal, one_mul, Finset.sum_comm] at hsum

end MixtureKL

end Cslib.Probability.PMF
