/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Margin
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Uniform margin generalization bounds via Rademacher complexity

The margin generalization bounds in `CslibFrontier.MachineLearning.Rademacher.Margin` hold for a
margin threshold `ρ > 0` fixed before the sample is drawn. Stratifying `(0, r]` by the geometric
grid `ρₙ = r / 2^(n + 1)` with failure-probability weights `δₙ = δ / ((n + 1) (n + 2))`
(`∑' n, 1 / ((n + 1) (n + 2)) = 1` by telescoping) and taking a countable union bound upgrades
those fixed-`ρ` bounds to hold **simultaneously for all** `h ∈ H` **and all** `ρ ∈ (0, r]`
[MohriRostamizadehTalwalkar2018, Theorem 5.9] [KoltchinskiiPanchenko2002].

For any `ρ ∈ (0, r]`, choosing `n : ℕ` with `r / 2^(n + 1) < ρ ≤ r / 2^n` yields:

* `marginLoss ρₙ u ≤ marginLoss ρ u` (`marginLoss` is monotone in `ρ > 0`),
* `2 / ρₙ ≤ 4 / ρ`, and
* `(n + 1) (n + 2) ≤ 2 (n + 1)² ≤ 2 (log₂ (2 r / ρ))²`, so `log (1 / δₙ)` is bounded by
  `2 log (log₂ (2 r / ρ)) + log (2 / δ)`.

Splitting the square root with `√(a + b) ≤ √a + √b` gives:

* with `R_m(H)`:
  `Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (4 / ρ) R_m(H) + √(log (log₂ (2 r / ρ)) / m) +`
  `√(log (2 / δ) / (2 m))`;
* with `R̂_{S_X}(H)`:
  `Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (4 / ρ) R̂_{S_X}(H) +`
  `3 √(log (log₂ (2 r / ρ)) / m) + 3 √(log (4 / δ) / (2 m))`.

## Main results

* `Cslib.MachineLearning.marginLoss_mono_of_pos`,
  `Cslib.MachineLearning.empiricalMarginLoss_mono_of_pos`: monotonicity of the `ρ`-margin loss in
  `ρ > 0`.
* `Cslib.MachineLearning.uniform_rademacherComplexity_margin_bound`: uniform-in-`ρ` margin
  generalization bound via `R_m(H)` [MohriRostamizadehTalwalkar2018, Theorem 5.9].
* `Cslib.MachineLearning.uniform_empiricalRademacherComplexity_margin_bound`: data-dependent
  uniform-in-`ρ` margin generalization bound via `R̂_{S_X}(H)`.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 5.4, Theorem 5.9
* [V. Koltchinskii, D. Panchenko, *Empirical margin distributions and bounding the generalization
  error of combined classifiers*][KoltchinskiiPanchenko2002]
-/

public section

open Finset Filter Topology
open scoped BigOperators ENNReal

namespace Cslib.MachineLearning

open Cslib.BitString

/-! ### Monotonicity in the margin parameter -/

/-- The `ρ`-margin loss `Φ_ρ(u)` is monotone in `ρ > 0`: a larger margin threshold `ρ₂ ≥ ρ₁ > 0`
penalizes every point at least as heavily. -/
theorem marginLoss_mono_of_pos {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ₂) (u : ℝ) :
    marginLoss ρ₁ u ≤ marginLoss ρ₂ u := by
  have hρ₂ : 0 < ρ₂ := lt_of_lt_of_le hρ₁ hρ
  rcases le_or_gt u 0 with hu | hu
  · rw [marginLoss_of_nonpos hρ₁ hu, marginLoss_of_nonpos hρ₂ hu]
  · simp only [marginLoss_def]
    gcongr

/-- The empirical `ρ`-margin loss `R̂_{S, ρ}(h)` is monotone in `ρ > 0`. -/
theorem empiricalMarginLoss_mono_of_pos {α : Type*} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ₂)
    (h : α → ℝ) {m : ℕ} (S : Fin m → α × Bool) :
    empiricalMarginLoss ρ₁ h S ≤ empiricalMarginLoss ρ₂ h S := by
  rw [empiricalMarginLoss_def, empiricalMarginLoss_def]
  exact Finset.expect_le_expect fun i _ => marginLoss_mono_of_pos hρ₁ hρ _

/-! ### Dyadic stratification helpers -/

/-- Telescoping sum `∑' n : ℕ, 1 / ((n + 1) * (n + 2)) = 1`. -/
private theorem hasSum_inv_succ_mul_succ :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have hsum : ∀ N : ℕ, ∑ n ∈ range N, (1 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) =
      1 - 1 / ((N : ℝ) + 1) := by
    intro N
    have heq : ∀ n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) =
        1 / ((n : ℝ) + 1) - 1 / ((n + 1 : ℕ) + 1 : ℝ) := fun n => by
      push_cast
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl fun n _ => heq n]
    simpa [Nat.cast_add, Nat.cast_one] using
      Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) N
  simp_rw [hsum]
  have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.sub h0

/-- Countable union bound for a finite `PMF` over a telescoping sequence of budgets
`δₙ = δ / ((n + 1) * (n + 2))`. -/
private theorem toOuterMeasure_iUnion_le_of_telescoping {Ω : Type*} (p : PMF Ω)
    (E : ℕ → Set Ω) {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ n : ℕ, (p.toOuterMeasure (E n)).toReal ≤ δ / ((n + 1 : ℕ) * (n + 2 : ℕ))) :
    (p.toOuterMeasure (⋃ n, E n)).toReal ≤ δ := by
  have hsub : ∀ n : ℕ, p.toOuterMeasure (E n) ≤
      ENNReal.ofReal (δ / ((n + 1 : ℕ) * (n + 2 : ℕ))) := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top p _)
      (by positivity)).2 (hE n)
  have hle : p.toOuterMeasure (⋃ n, E n) ≤
      ∑' n : ℕ, ENNReal.ofReal (δ / ((n + 1 : ℕ) * (n + 2 : ℕ))) :=
    (MeasureTheory.measure_iUnion_le E).trans (tsum_le_tsum hsub)
  have hhas : HasSum (fun n : ℕ => δ / ((n + 1 : ℕ) * (n + 2 : ℕ))) δ := by
    simpa only [div_eq_mul_inv, one_mul, mul_one] using
      hasSum_inv_succ_mul_succ.mul_left δ
  have htsum : ∑' n : ℕ, ENNReal.ofReal (δ / ((n + 1 : ℕ) * (n + 2 : ℕ))) =
      ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hhas.summable, hhas.tsum_eq]
  rw [htsum] at hle
  exact (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top p _) hδ.le).1 hle

/-- Every `ρ ∈ (0, r]` falls into a dyadic interval `(r / 2^(n + 1), r / 2^n]`. -/
private theorem exists_dyadic_bracket {r ρ : ℝ} (hρ : ρ ∈ Set.Ioc 0 r) :
    ∃ n : ℕ, r / 2 ^ (n + 1) < ρ ∧ ρ ≤ r / 2 ^ n := by
  have hpos : 0 < ρ := hρ.1
  have hle : ρ ≤ r := hρ.2
  have hex : ∃ n : ℕ, r / 2 ^ (n + 1) < ρ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / ρ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have h1 : r / ρ < 2 ^ (n + 1) := hn.trans_le
      (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
    rw [div_lt_iff₀ hpos] at h1
    linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hn : Nat.find hex with
  | zero => simpa using hle
  | succ k =>
    have hnot : ¬ r / 2 ^ (k + 1) < ρ := Nat.find_min hex (by omega)
    exact le_of_not_gt hnot

/-- Relating the dyadic index `n` to `log₂ (2 r / ρ)` when `ρ ≤ r / 2^n`. -/
private theorem succ_le_logb_two {r ρ : ℝ} {n : ℕ} (hρ : 0 < ρ)
    (hle : ρ ≤ r / 2 ^ n) : (n : ℝ) + 1 ≤ Real.logb 2 (2 * r / ρ) := by
  have hpow : (2 : ℝ) ^ (n + 1) ≤ 2 * r / ρ := by
    rw [le_div_iff₀ hρ, pow_succ']
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).1 hle
    linarith
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_add, Nat.cast_one] at hlog

/-- Bounding `log (c * (n + 1) * (n + 2) / δ)` by `2 * log (log₂ (2 r / ρ)) + log (2 * c / δ)`. -/
private theorem log_weight_le {c r ρ δ : ℝ} {n : ℕ} (hc : 0 < c) (hρ : 0 < ρ)
    (hδ : 0 < δ) (hle : ρ ≤ r / 2 ^ n) :
    Real.log (c * ((n + 1 : ℕ) * (n + 2 : ℕ)) / δ) ≤
      2 * Real.log (Real.logb 2 (2 * r / ρ)) + Real.log (2 * c / δ) := by
  have hlb : (n : ℝ) + 1 ≤ Real.logb 2 (2 * r / ρ) := succ_le_logb_two hρ hle
  have hlb_pos : 0 < Real.logb 2 (2 * r / ρ) := lt_of_lt_of_le (by positivity) hlb
  have hprod : ((n + 1 : ℕ) * (n + 2 : ℕ) : ℝ) ≤ 2 * Real.logb 2 (2 * r / ρ) ^ 2 := by
    push_cast
    have h1 : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith
    calc ((n : ℝ) + 1) * ((n : ℝ) + 2)
        ≤ ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * ((n : ℝ) + 1) ^ 2 := by ring
      _ ≤ 2 * Real.logb 2 (2 * r / ρ) ^ 2 := by gcongr
  have hnum : c * ((n + 1 : ℕ) * (n + 2 : ℕ) : ℝ) / δ ≤
      Real.logb 2 (2 * r / ρ) ^ 2 * (2 * c / δ) := by
    have : c * ((n + 1 : ℕ) * (n + 2 : ℕ) : ℝ) / δ ≤
        c * (2 * Real.logb 2 (2 * r / ρ) ^ 2) / δ := by gcongr
    exact this.trans_eq (by ring)
  calc Real.log (c * ((n + 1 : ℕ) * (n + 2 : ℕ)) / δ)
      ≤ Real.log (Real.logb 2 (2 * r / ρ) ^ 2 * (2 * c / δ)) :=
        Real.log_le_log (by positivity) hnum
    _ = 2 * Real.log (Real.logb 2 (2 * r / ρ)) + Real.log (2 * c / δ) := by
        rw [Real.log_mul (pow_ne_zero 2 hlb_pos.ne') (by positivity), Real.log_pow]
        push_cast
        ring

private theorem sqrt_add_le {a b : ℝ} : √(a + b) ≤ √a + √b := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hb), add_zero]
      exact Real.sqrt_le_sqrt (by linarith)
  · by_cases hb : 0 ≤ b
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha), zero_add]
      exact Real.sqrt_le_sqrt (by linarith)
    · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
      positivity

private theorem sqrt_log_dyadic_le {c r ρ δ : ℝ} {m n : ℕ} (hc : 0 < c) (hm : 0 < m)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hle : ρ ≤ r / 2 ^ n) :
    √(Real.log (c / (δ / ((n + 1 : ℕ) * (n + 2 : ℕ)))) / (2 * m)) ≤
      √(Real.log (Real.logb 2 (2 * r / ρ)) / m) + √(Real.log (2 * c / δ) / (2 * m)) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [div_div_eq_mul_div]
  calc √(Real.log (c * ((n + 1 : ℕ) * (n + 2 : ℕ) : ℝ) / δ) / (2 * m))
      ≤ √((2 * Real.log (Real.logb 2 (2 * r / ρ)) + Real.log (2 * c / δ)) / (2 * m)) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (log_weight_le hc hρ hδ hle) (by positivity))
    _ = √(Real.log (Real.logb 2 (2 * r / ρ)) / m + Real.log (2 * c / δ) / (2 * m)) := by
        congr 1; field_simp
    _ ≤ √(Real.log (Real.logb 2 (2 * r / ρ)) / m) + √(Real.log (2 * c / δ) / (2 * m)) :=
        sqrt_add_le

private theorem two_div_dyadic_le {r ρ : ℝ} {n : ℕ} (hr : 0 < r) (hρ : 0 < ρ)
    (hle : ρ ≤ r / 2 ^ n) : 2 / (r / 2 ^ (n + 1)) ≤ 4 / ρ := by
  have h2 : ρ ≤ 2 * (r / 2 ^ (n + 1)) := by
    have : r / 2 ^ n = 2 * (r / 2 ^ (n + 1)) := by rw [pow_succ']; ring
    exact hle.trans_eq this
  rw [div_le_div_iff₀ (by positivity) hρ]
  linarith

/-! ### Uniform-in-`ρ` margin generalization bounds -/

/-- **Uniform margin generalization bound** [MohriRostamizadehTalwalkar2018, Theorem 5.9]
[KoltchinskiiPanchenko2002]: for a uniformly bounded class `H : Set (α → ℝ)` on a finite domain `α`,
a scale `r > 0`, `m > 0` independent draws from `D : PMF (α × Bool)`, and `δ > 0`, with
probability at least `1 - δ` every `h ∈ H` and every `ρ ∈ (0, r]` simultaneously satisfy
```
Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (4 / ρ) R_m(H)
  + √(log (log₂ (2 r / ρ)) / m) + √(log (2 / δ) / (2 m)).
```
Obtained by a countable union bound over `rademacherComplexity_margin_bound` at dyadic scales
`ρₙ = r / 2^(n + 1)` with failure budgets `δₙ = δ / ((n + 1) (n + 2))`. -/
theorem uniform_rademacherComplexity_margin_bound {α : Type*} [Fintype α] (D : PMF (α × Bool))
    {m : ℕ} (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, ∃ ρ ∈ Set.Ioc 0 r, empiricalMarginLoss ρ h S +
        4 / ρ * rademacherComplexity (D.map Prod.fst) H m +
          √(Real.log (Real.logb 2 (2 * r / ρ)) / m) +
          √(Real.log (2 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  rcases H.eq_empty_or_nonempty with rfl | hne
  · simp [hδ.le]
  have hR_nonneg : 0 ≤ rademacherComplexity (D.map Prod.fst) H m :=
    rademacherComplexity_nonneg _ hne hH m
  let ρn : ℕ → ℝ := fun n => r / 2 ^ (n + 1)
  let δn : ℕ → ℝ := fun n => δ / ((n + 1 : ℕ) * (n + 2 : ℕ))
  let E : ℕ → Set (Fin m → α × Bool) := fun n =>
    {S | ∃ h ∈ H, empiricalMarginLoss (ρn n) h S +
      2 / ρn n * rademacherComplexity (D.map Prod.fst) H m +
        √(Real.log (1 / δn n) / (2 * m)) <
      (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (toOuterMeasure_iUnion_le_of_telescoping _ E hδ fun n =>
      rademacherComplexity_margin_bound D hm hH (ρ := ρn n) (by positivity)
        (δ := δn n) (by positivity))
  rintro S ⟨h, hh, ρ, hρ, hlt⟩
  obtain ⟨n, hρ_gt, hρ_le⟩ := exists_dyadic_bracket hρ
  refine Set.mem_iUnion.2 ⟨n, h, hh, ?_⟩
  have hloss := empiricalMarginLoss_mono_of_pos (by positivity : 0 < ρn n) hρ_gt.le h S
  have hrad := mul_le_mul_of_nonneg_right (two_div_dyadic_le hr hρ.1 hρ_le) hR_nonneg
  have hsqrt := by
    simpa only [mul_one] using sqrt_log_dyadic_le zero_lt_one hm hρ.1 hδ hρ_le
  dsimp only [ρn, δn] at hloss ⊢
  linarith

/-- **Data-dependent uniform margin generalization bound** [MohriRostamizadehTalwalkar2018,
Theorem 5.9] [KoltchinskiiPanchenko2002]: for a uniformly bounded class `H : Set (α → ℝ)` on a
finite domain `α`, a scale `r > 0`, `m > 0` independent draws from `D : PMF (α × Bool)`, and
`δ > 0`, with probability at least `1 - δ` every `h ∈ H` and every `ρ ∈ (0, r]` simultaneously
satisfy
```
Pr_D[signVal y * h x ≤ 0] ≤ R̂_{S, ρ}(h) + (4 / ρ) R̂_{S_X}(H)
  + 3 √(log (log₂ (2 r / ρ)) / m) + 3 √(log (4 / δ) / (2 m)).
```
Here `S_X` is the unlabeled sample `fun i => (S i).1`. Note the constant `4 / δ` arises from
substituting `δₙ = δ / ((n + 1) (n + 2))` into `log (2 / δₙ)`. -/
theorem uniform_empiricalRademacherComplexity_margin_bound {α : Type*} [Finite α]
    (D : PMF (α × Bool)) {m : ℕ} (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ}
    (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B) {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ h ∈ H, ∃ ρ ∈ Set.Ioc 0 r, empiricalMarginLoss ρ h S +
        4 / ρ * empiricalRademacherComplexity H (fun i => (S i).1) +
          3 * √(Real.log (Real.logb 2 (2 * r / ρ)) / m) +
          3 * √(Real.log (4 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  rcases H.eq_empty_or_nonempty with rfl | hne
  · simp [hδ.le]
  let ρn : ℕ → ℝ := fun n => r / 2 ^ (n + 1)
  let δn : ℕ → ℝ := fun n => δ / ((n + 1 : ℕ) * (n + 2 : ℕ))
  let E : ℕ → Set (Fin m → α × Bool) := fun n =>
    {S | ∃ h ∈ H, empiricalMarginLoss (ρn n) h S +
      2 / ρn n * empiricalRademacherComplexity H (fun i => (S i).1) +
        3 * √(Real.log (2 / δn n) / (2 * m)) <
      (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (toOuterMeasure_iUnion_le_of_telescoping _ E hδ fun n =>
      empiricalRademacherComplexity_margin_bound D hm hH (ρ := ρn n) (by positivity)
        (δ := δn n) (by positivity))
  rintro S ⟨h, hh, ρ, hρ, hlt⟩
  obtain ⟨n, hρ_gt, hρ_le⟩ := exists_dyadic_bracket hρ
  refine Set.mem_iUnion.2 ⟨n, h, hh, ?_⟩
  have hloss := empiricalMarginLoss_mono_of_pos (by positivity : 0 < ρn n) hρ_gt.le h S
  have hrad := mul_le_mul_of_nonneg_right (two_div_dyadic_le hr hρ.1 hρ_le)
    (empiricalRademacherComplexity_nonneg hne hH (fun i => (S i).1))
  have hsqrt := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      sqrt_log_dyadic_le two_pos hm hρ.1 hδ hρ_le
  dsimp only [ρn, δn] at hloss ⊢
  linarith

end Cslib.MachineLearning
