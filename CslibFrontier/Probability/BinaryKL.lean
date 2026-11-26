/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
import CslibFrontier.Foundations.Combinatorics.BinomialTail
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.Coin
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Binary relative entropy

The binary relative entropy `binaryKL q p = q log (q / p) + (1 - q) log ((1 - q) / (1 - p))` of
Bernoulli parameters `q, p ∈ [0, 1]`, in nats, written with Mathlib's `klFun` as
`p klFun (q / p) + (1 - p) klFun ((1 - q) / (1 - p))`.

At `p ∈ {0, 1}` with `q ≠ p` the true divergence is infinite; `binaryKL` takes finite junk values
there, so Jensen's inequality is stated for pairs with `q = p` wherever `p ∈ {0, 1}`.

## Main definitions

* `Cslib.Probability.binaryKL`: the binary relative entropy.

## Main results

* `Cslib.Probability.binaryKL_nonneg`, `Cslib.Probability.binaryKL_self`: nonnegativity and
  vanishing on the diagonal.
* `Cslib.Probability.binaryKL_eq_mul_log`: the closed form for `p ∈ (0, 1)`.
* `Cslib.Probability.convexOn_binaryKL`, `Cslib.Probability.convexOn_exp_mul_binaryKL`: for fixed
  `p ∈ [0, 1]`, `binaryKL · p` and `exp (t binaryKL · p)` with `t ≥ 0` are convex on `[0, 1]`.
* `Cslib.Probability.choose_mul_pow_mul_exp_binaryKL_le_one`: a binomial probability is at most
  `exp (-m binaryKL (k / m) p)`.
* `Cslib.Probability.mul_klFun_integral_div_integral_le`: the log-sum inequality in integral form.
* `Cslib.Probability.binaryKL_integral_le_integral`: Jensen's inequality for `binaryKL`.
* `Cslib.Probability.two_mul_sq_le_binaryKL`: Bernoulli Pinsker inequality
  `2 (q - p)² ≤ binaryKL q p`.
* `Cslib.Probability.sub_sq_div_two_mul_le_binaryKL`: quadratic empirical-Bernstein lower bound
  `(p - q)² / (2 p) ≤ binaryKL q p`.
* `Cslib.Probability.abs_sub_le_sqrt_of_binaryKL_le`,
  `Cslib.Probability.le_add_add_sqrt_of_binaryKL_le`,
  `Cslib.Probability.le_add_sqrt_two_mul_add_two_mul_of_binaryKL_le`,
  `Cslib.Probability.le_one_sub_exp_neg_of_binaryKL_zero_le`: analytical inversions of
  `binaryKL q p ≤ c`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006]
* [I. O. Tolstikhin, Y. Seldin, *PAC-Bayes-Empirical-Bernstein Inequality*][TolstikhinSeldin2013]
  (locator unverified)
-/

public section

namespace Cslib.Probability

open InformationTheory Set

/-- The binary relative entropy `q log (q / p) + (1 - q) log ((1 - q) / (1 - p))` of Bernoulli
parameters, in nats. -/
noncomputable def binaryKL (q p : ℝ) : ℝ :=
  p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p))

theorem binaryKL_def (q p : ℝ) :
    binaryKL q p = p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p)) := by
  rw [binaryKL]

theorem binaryKL_nonneg {q p : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ binaryKL q p :=
  add_nonneg (mul_nonneg hp.1 (klFun_nonneg (div_nonneg hq.1 hp.1)))
    (mul_nonneg (sub_nonneg.2 hp.2)
      (klFun_nonneg (div_nonneg (sub_nonneg.2 hq.2) (sub_nonneg.2 hp.2))))

@[simp]
theorem binaryKL_self (p : ℝ) : binaryKL p p = 0 := by
  have h (x : ℝ) : x * klFun (x / x) = 0 := by
    by_cases hx : x = 0 <;> simp [hx, klFun_one]
  rw [binaryKL_def, h, h, add_zero]

/-- For fixed `p`, `binaryKL · p` is continuous. -/
@[fun_prop]
theorem continuous_binaryKL_left (p : ℝ) : Continuous fun q => binaryKL q p := by
  fun_prop [binaryKL]

/-- For `p ∈ (0, 1)`, `binaryKL q p = q log (q / p) + (1 - q) log ((1 - q) / (1 - p))`. -/
theorem binaryKL_eq_mul_log {q p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binaryKL q p = q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := by
  have : 1 - p ≠ 0 := (sub_pos.2 hp1).ne'
  rw [binaryKL_def, klFun_apply, klFun_apply]
  field_simp; ring

private theorem exp_mul_log_eq_pow {y : ℝ} {n : ℕ} (h : 0 < y ∨ n = 0) :
    Real.exp (n * Real.log y) = y ^ n := by
  rcases h with h | rfl
  · rw [← Real.log_pow, Real.exp_log (pow_pos h n)]
  · simp

/-- A binomial probability is at most `exp (-m binaryKL (k / m) p)`:
`C(m, k) p ^ k (1 - p) ^ (m - k) exp (m binaryKL (k / m) p) ≤ 1` for `p ∈ [0, 1]` and `k ≤ m`.
The left side is the probability of `k` successes in `m` trials of success probability `k / m`. -/
theorem choose_mul_pow_mul_exp_binaryKL_le_one {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) {m k : ℕ}
    (hk : k ≤ m) :
    (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * Real.exp (m * binaryKL (k / m) p) ≤ 1 := by
  rcases hp.1.eq_or_lt with rfl | hp0
  · cases k <;> simp
  rcases hp.2.eq_or_lt with rfl | hp1
  · rcases hk.eq_or_lt with rfl | hkm
    · by_cases hk0 : k = 0 <;> simp [hk0]
    · simp [zero_pow (Nat.sub_pos_of_lt hkm).ne']
  set q : ℝ := k / m with hq
  have hmq : (m : ℝ) * q = k := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Nat.le_zero.1 hk]
    · rw [hq, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]
  have hmq' : (m : ℝ) * (1 - q) = ((m - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, mul_one_sub, hmq]
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hq]
    · rw [hq, div_le_one (Nat.cast_pos.2 hm)]; exact_mod_cast hk
  have hexp : Real.exp (m * binaryKL q p) = (q / p) ^ k * ((1 - q) / (1 - p)) ^ (m - k) := by
    rw [binaryKL_eq_mul_log hp0 hp1, mul_add, ← mul_assoc, ← mul_assoc, hmq, hmq',
      Real.exp_add, exp_mul_log_eq_pow, exp_mul_log_eq_pow]
    · exact (Nat.eq_zero_or_pos (m - k)).symm.imp (fun h => div_pos
        (pos_of_mul_pos_right (hmq'.symm ▸ Nat.cast_pos.2 h) (Nat.cast_nonneg m)) (sub_pos.2 hp1))
        id
    · exact (Nat.eq_zero_or_pos k).symm.imp
        (fun h => div_pos (pos_of_mul_pos_right (hmq.symm ▸ Nat.cast_pos.2 h) (Nat.cast_nonneg m))
          hp0) id
  have hterm : (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * Real.exp (m * binaryKL q p) =
      m.choose k * q ^ k * (1 - q) ^ (m - k) := by
    rw [hexp]
    calc (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) *
          ((q / p) ^ k * ((1 - q) / (1 - p)) ^ (m - k))
        = (p * (q / p)) ^ k * ((1 - p) * ((1 - q) / (1 - p))) ^ (m - k) * m.choose k := by
          rw [mul_pow, mul_pow]; ring
      _ = m.choose k * q ^ k * (1 - q) ^ (m - k) := by
        rw [mul_div_cancel₀ _ hp0.ne', mul_div_cancel₀ _ (sub_pos.2 hp1).ne']; ring
  rw [hterm]
  calc (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k)
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j) :=
        Finset.single_le_sum (f := fun j => (m.choose j : ℝ) * q ^ j * (1 - q) ^ (m - j))
          (fun j _ => by have := sub_nonneg.2 hq1; positivity)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    _ = 1 := Cslib.sum_choose_mul_pow_eq_one m q

/-- `q ↦ c klFun (α + β q)` is convex on `[0, 1]` when `c ≥ 0` and `α + β q ≥ 0` there. -/
private theorem convexOn_mul_klFun_affine {c α β : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 ≤ α + β * q) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => c * klFun (α + β * q) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := convexOn_klFun.2 (mem_Ici.2 (hpos x hx)) (mem_Ici.2 (hpos y hy)) ha hb hab
  have hlin : α + β * (a • x + b • y) = a • (α + β * x) + b • (α + β * y) := by
    simp only [smul_eq_mul]
    linear_combination α * hab.symm
  dsimp only
  rw [hlin]
  calc c * klFun (a • (α + β * x) + b • (α + β * y))
      ≤ c * (a • klFun (α + β * x) + b • klFun (α + β * y)) := mul_le_mul_of_nonneg_left h hc
    _ = a • (c * klFun (α + β * x)) + b • (c * klFun (α + β * y)) := by
      simp only [smul_eq_mul]; ring

/-- For fixed `p ∈ [0, 1]`, the binary relative entropy is convex in its first argument. -/
theorem convexOn_binaryKL {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => binaryKL q p := by
  have h1 := convexOn_mul_klFun_affine (c := p) (α := 0) (β := p⁻¹) hp.1
    fun q hq => by simpa using mul_nonneg (inv_nonneg.2 hp.1) hq.1
  have h2 := convexOn_mul_klFun_affine (c := 1 - p) (α := (1 - p)⁻¹) (β := -(1 - p)⁻¹)
    (sub_nonneg.2 hp.2) fun q hq => by
      rw [neg_mul, ← sub_eq_add_neg, ← mul_one_sub]
      exact mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hp.2)) (sub_nonneg.2 hq.2)
  refine (h1.add h2).congr fun q _ => ?_
  simp only [binaryKL_def, Pi.add_apply, zero_add, div_eq_inv_mul, neg_mul, ← sub_eq_add_neg,
    ← mul_one_sub]

/-- For fixed `p ∈ [0, 1]` and `t ≥ 0`, `exp (t binaryKL · p)` is convex on `[0, 1]`. -/
theorem convexOn_exp_mul_binaryKL {p t : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) fun q => Real.exp (t * binaryKL q p) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := (convexOn_binaryKL hp).2 hx hy ha hb hab
  calc Real.exp (t * binaryKL (a • x + b • y) p)
      ≤ Real.exp (a • (t * binaryKL x p) + b • (t * binaryKL y p)) :=
        Real.exp_le_exp.2 (by
          simpa only [smul_eq_mul, mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left h ht)
    _ ≤ a • Real.exp (t * binaryKL x p) + b • Real.exp (t * binaryKL y p) :=
        convexOn_exp.2 trivial trivial ha hb hab

section Jensen

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The tangent line of `klFun` at `t > 0` lies below it on `[0, ∞)`. -/
private theorem klFun_add_log_mul_sub_le {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    klFun t + Real.log t * (x - t) ≤ klFun x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [klFun_apply, klFun_zero]; linarith
  · have h := mul_nonneg ht.le (klFun_nonneg (div_nonneg hx.le ht.le))
    have he : t * klFun (x / t) = x * Real.log x - x * Real.log t + t - x := by
      rw [klFun_apply, Real.log_div hx.ne' ht.ne']; field_simp
    rw [klFun_apply, klFun_apply]; linarith

/-- **The log-sum inequality** [CoverThomas2006, Theorem 2.7.1] in integral form: Jensen for the
perspective of `klFun`: for nonnegative integrable `a` and `b` with `a = 0` wherever `b = 0`,
`(∫ b) klFun ((∫ a) / ∫ b) ≤ ∫ b klFun (a / b)`. -/
theorem mul_klFun_integral_div_integral_le {a b : α → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hab : ∀ x, b x = 0 → a x = 0)
    (hai : Integrable a μ) (hbi : Integrable b μ)
    (hi : Integrable (fun x => b x * klFun (a x / b x)) μ) :
    (∫ x, b x ∂μ) * klFun ((∫ x, a x ∂μ) / ∫ x, b x ∂μ) ≤ ∫ x, b x * klFun (a x / b x) ∂μ := by
  have hnn (x : α) : 0 ≤ b x * klFun (a x / b x) :=
    mul_nonneg (hb x) (klFun_nonneg (div_nonneg (ha x) (hb x)))
  rcases (integral_nonneg (f := b) (μ := μ) hb).eq_or_lt with hB | hB
  · rw [← hB, zero_mul]
    exact integral_nonneg (μ := μ) fun x => hnn x
  rcases (integral_nonneg (f := a) (μ := μ) ha).eq_or_lt with hA | hA
  · have h0 : a =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg (fun x => ha x) hai).1 hA.symm
    rw [← hA, zero_div, klFun_zero, mul_one]
    exact (integral_congr_ae (h0.mono fun x (hx : a x = 0) => by simp [hx, klFun_zero])).le
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  have ht : 0 < A / B := div_pos hA hB
  have hpt (x : α) : b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B)) ≤
      b x * klFun (a x / b x) := by
    rcases (hb x).eq_or_lt with h | h
    · simp [← h, hab x h.symm]
    · have hc : b x * (a x / b x) = a x := mul_div_cancel₀ _ h.ne'
      calc b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B))
          = b x * (klFun (A / B) + Real.log (A / B) * (a x / b x - A / B)) := by
            linear_combination -(Real.log (A / B)) * hc
        _ ≤ b x * klFun (a x / b x) := mul_le_mul_of_nonneg_left
            (klFun_add_log_mul_sub_le ht (div_nonneg (ha x) h.le)) h.le
  have hi1 : Integrable (fun x => b x * klFun (A / B)) μ := hbi.mul_const _
  have hi4 : Integrable (fun x => Real.log (A / B) * (a x - b x * (A / B))) μ :=
    (hai.sub (hbi.mul_const _)).const_mul _
  calc B * klFun (A / B)
      = ∫ x, (b x * klFun (A / B) + Real.log (A / B) * (a x - b x * (A / B))) ∂μ := by
        rw [integral_add hi1 hi4, integral_mul_const, integral_const_mul,
          integral_sub hai (hbi.mul_const _),
          integral_mul_const, mul_div_cancel₀ _ hB.ne', sub_self, mul_zero, add_zero]
    _ ≤ ∫ x, b x * klFun (a x / b x) ∂μ := integral_mono (hi1.add hi4) hi hpt

/-- **Jensen's inequality for the binary relative entropy**: for `q, p` with values in `[0, 1]`
under a probability measure, with `q = 0` wherever `p = 0` and `q = 1` wherever `p = 1`,
`binaryKL (∫ q) (∫ p) ≤ ∫ binaryKL q p`. Without the conditions on `p = 0` and `p = 1`, where the
true divergence is infinite unless `q = p`, the junk values of `binaryKL` are not convex. -/
theorem binaryKL_integral_le_integral [IsProbabilityMeasure μ] {q p : α → ℝ}
    (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ x, p x = 0 → q x = 0) (h1 : ∀ x, p x = 1 → q x = 1)
    (hqm : AEMeasurable q μ) (hpm : AEMeasurable p μ)
    (hkl : Integrable (fun x => binaryKL (q x) (p x)) μ) :
    binaryKL (∫ x, q x ∂μ) (∫ x, p x ∂μ) ≤ ∫ x, binaryKL (q x) (p x) ∂μ := by
  have hqi : Integrable q μ := Integrable.of_mem_Icc 0 1 hqm (ae_of_all _ hq)
  have hpi : Integrable p μ := Integrable.of_mem_Icc 0 1 hpm (ae_of_all _ hp)
  have hn1 (x : α) : 0 ≤ p x * klFun (q x / p x) :=
    mul_nonneg (hp x).1 (klFun_nonneg (div_nonneg (hq x).1 (hp x).1))
  have hn2 (x : α) : 0 ≤ (1 - p x) * klFun ((1 - q x) / (1 - p x)) :=
    mul_nonneg (sub_nonneg.2 (hp x).2)
      (klFun_nonneg (div_nonneg (sub_nonneg.2 (hq x).2) (sub_nonneg.2 (hp x).2)))
  have hi1 : Integrable (fun x => p x * klFun (q x / p x)) μ :=
    hkl.mono' (hpm.mul (measurable_klFun.comp_aemeasurable (hqm.div hpm))).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hn1 x), binaryKL_def]
        exact le_add_of_nonneg_right (hn2 x))
  have hi2 : Integrable (fun x => (1 - p x) * klFun ((1 - q x) / (1 - p x))) μ :=
    hkl.mono' ((aemeasurable_const.sub hpm).mul (measurable_klFun.comp_aemeasurable
      ((aemeasurable_const.sub hqm).div (aemeasurable_const.sub hpm)))).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hn2 x), binaryKL_def]
        exact le_add_of_nonneg_left (hn1 x))
  have j1 := mul_klFun_integral_div_integral_le (fun x => (hq x).1) (fun x => (hp x).1) h0 hqi
    hpi hi1
  have j2 := mul_klFun_integral_div_integral_le (μ := μ) (a := fun x => 1 - q x)
    (b := fun x => 1 - p x) (fun x => sub_nonneg.2 (hq x).2) (fun x => sub_nonneg.2 (hp x).2)
    (fun x h => by rw [h1 x (by linarith), sub_self])
    ((integrable_const 1).sub hqi) ((integrable_const 1).sub hpi) hi2
  rw [integral_sub (integrable_const 1) hqi, integral_sub (integrable_const 1) hpi] at j2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at j2
  simp_rw [binaryKL_def]
  rw [integral_add hi1 hi2]
  exact add_le_add j1 j2

end Jensen

section LowerBounds

open Real

/-- The `p`-derivative of `binaryKL q p` on `(0, 1)` is `(p - q) / (p * (1 - p))`. -/
private theorem hasDerivAt_binaryKL_right {q p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun t => binaryKL q t) ((p - q) / (p * (1 - p))) p := by
  have hlog_div (x y : ℝ) (hy : y ≠ 0) : x * log (x / y) = x * (log x - log y) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [log_div hx hy]
  have heq : (fun t => binaryKL q t) =ᶠ[nhds p]
      fun t => q * (log q - log t) + (1 - q) * (log (1 - q) - log (1 - t)) := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with t ht
    rw [binaryKL_eq_mul_log ht.1 ht.2, hlog_div q t ht.1.ne',
      hlog_div (1 - q) (1 - t) (sub_pos.mpr ht.2).ne']
  have h1p := (sub_pos.mpr hp1).ne'
  have hd₁ := ((hasDerivAt_log hp0.ne').const_sub (log q)).const_mul q
  have hd₂ := ((((hasDerivAt_id p).const_sub 1).log h1p).const_sub (log (1 - q))).const_mul (1 - q)
  refine ((hd₁.add hd₂).congr_deriv ?_).congr_of_eventuallyEq heq
  simp only [id_eq]
  field_simp [hp0.ne', h1p]; ring

private theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ f' t) : f a ≤ f b :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
    (fun t ht => (hd t (by rwa [interior_Icc] at ht)).hasDerivWithinAt)
    (fun t ht => hnn t (by rwa [interior_Icc] at ht)) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

open scoped Cslib.Probability.PMF in
/-- **Bernoulli Pinsker's inequality**: for `q ∈ [0, 1]` and `p ∈ (0, 1)`,
`2 * (q - p) ^ 2 ≤ binaryKL q p`. -/
theorem two_mul_sq_le_binaryKL {q p : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    2 * (q - p) ^ 2 ≤ binaryKL q p := by
  let qCoin := PMF.coin ⟨q, hq⟩
  let pCoin := PMF.coin ⟨p, hp0.le, hp1.le⟩
  have hsupp : qCoin.support ⊆ pCoin.support := fun b _ => by
    cases b <;> simp [_root_.PMF.mem_support_iff, pCoin, PMF.coin_apply, hp0, hp1]
  have hdist : dist qCoin pCoin = |q - p| := by
    have hneg : 1 - q - (1 - p) = -(q - p) := by ring
    simp only [PMF.dist_eq, Fintype.sum_bool, qCoin, pCoin, PMF.coin_apply_toReal,
      Bool.false_eq_true, ite_false, ite_true, hneg, abs_neg]
    ring
  simpa only [hdist, sq_abs, Fintype.sum_bool, qCoin, pCoin, PMF.coin_apply_toReal,
    Bool.false_eq_true, ite_false, ite_true, binaryKL_eq_mul_log hp0 hp1] using
    PMF.two_mul_dist_sq_le_sum_mul_log_div hsupp

/-- **Quadratic empirical-Bernstein lower bound on `binaryKL`**: for `0 ≤ q ≤ p < 1` (`0 < p`),
`(p - q) ^ 2 / (2 * p) ≤ binaryKL q p`. Sharp for small `q` (`O(p)` at `q = 0`), yielding the
fast-rate PAC-Bayes inversion [TolstikhinSeldin2013] (locator unverified). -/
theorem sub_sq_div_two_mul_le_binaryKL {q p : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (p - q) ^ 2 / (2 * p) ≤ binaryKL q p := by
  rcases eq_or_lt_of_le hq0 with rfl | hqpos
  · rw [binaryKL_eq_mul_log hp0 hp1]
    simp only [zero_mul, zero_add, sub_zero, one_mul, one_div, log_inv]
    have hdiv : p ^ 2 / (2 * p) = p / 2 := by field_simp
    linarith [log_le_sub_one_of_pos (sub_pos.mpr hp1)]
  let g : ℝ → ℝ := fun t => binaryKL q t - (t - q) ^ 2 / (2 * t)
  have hderiv : ∀ t ∈ Ioo q 1,
      HasDerivAt g ((t - q) * (t - q + t ^ 2 + t * q) / (2 * t ^ 2 * (1 - t))) t := by
    intro t ht
    have ht0 : 0 < t := hqpos.trans ht.1
    have hd_kl := hasDerivAt_binaryKL_right (q := q) ht0 ht.2
    refine (hd_kl.sub ((((hasDerivAt_id t).sub_const q).pow 2).div
      ((hasDerivAt_id t).const_mul 2) (mul_ne_zero two_ne_zero ht0.ne'))).congr_deriv ?_
    have : 0 < 1 - t := sub_pos.mpr ht.2
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp; ring
  have h := le_of_hasDerivAt_nonneg hqp
    (fun t ht => by
      have ht0 : 0 < t := hqpos.trans_le ht.1
      exact ((hasDerivAt_binaryKL_right ht0 (ht.2.trans_lt hp1)).continuousAt.sub
        (by fun_prop (disch := positivity))).continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1, ht.2.trans hp1⟩)
    fun t ht => div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1.le)
      (by nlinarith [hqpos.trans ht.1, ht.1])) (by positivity [sub_pos.mpr (ht.2.trans hp1)])
  simp only [g, binaryKL_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div] at h
  linarith

/-- Exact Pinsker inversion: for `q ∈ [0, 1]` and `p ∈ (0, 1)`, `binaryKL q p ≤ c` implies
`|p - q| ≤ √(c / 2)`. -/
theorem abs_sub_le_sqrt_of_binaryKL_le {q p c : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hle : binaryKL q p ≤ c) :
    |p - q| ≤ sqrt (c / 2) :=
  abs_sub_comm q p ▸ abs_le_sqrt (by linarith [two_mul_sq_le_binaryKL hq hp0 hp1])

/-- Sharp quadratic inversion of `binaryKL q p ≤ c`: for `0 ≤ q`, `p < 1`, and `0 ≤ c`,
`p ≤ q + c + √(c ^ 2 + 2 * q * c)`. -/
theorem le_add_add_sqrt_of_binaryKL_le {q p c : ℝ} (hq0 : 0 ≤ q) (hp1 : p < 1)
    (hc : 0 ≤ c) (hle : binaryKL q p ≤ c) :
    p ≤ q + c + sqrt (c ^ 2 + 2 * q * c) := by
  rcases le_or_gt p q with hle_pq | hgt
  · linarith [sqrt_nonneg (c ^ 2 + 2 * q * c)]
  have hp_pos : 0 < p := lt_of_le_of_lt hq0 hgt
  have hbern := (sub_sq_div_two_mul_le_binaryKL hq0 hgt.le hp_pos hp1).trans hle
  rw [div_le_iff₀ (mul_pos zero_lt_two hp_pos)] at hbern
  have hsq : (p - (q + c)) ^ 2 ≤ c ^ 2 + 2 * q * c := by nlinarith
  linarith [(abs_le.mp (abs_le_sqrt hsq)).2]

/-- Standard relaxed fast-rate inversion [TolstikhinSeldin2013] (locator unverified):
`binaryKL q p ≤ c ⟹ p ≤ q + √(2 * q * c) + 2 * c`. -/
theorem le_add_sqrt_two_mul_add_two_mul_of_binaryKL_le {q p c : ℝ} (hq0 : 0 ≤ q)
    (hp1 : p < 1) (hc : 0 ≤ c) (hle : binaryKL q p ≤ c) :
    p ≤ q + sqrt (2 * q * c) + 2 * c := by
  have h := le_add_add_sqrt_of_binaryKL_le hq0 hp1 hc hle
  have hsqrt : sqrt (c ^ 2 + 2 * q * c) ≤ c + sqrt (2 * q * c) := by
    refine sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg hc (sqrt_nonneg (2 * q * c)),
      sq_sqrt (mul_nonneg (mul_nonneg zero_le_two hq0) hc)]
  linarith

/-- Zero-empirical-risk inversion: for `p ∈ [0, 1)`, `binaryKL 0 p ≤ c` gives
`p ≤ 1 - exp (-c)` (and hence `p ≤ c`). -/
theorem le_one_sub_exp_neg_of_binaryKL_zero_le {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hle : binaryKL 0 p ≤ c) :
    p ≤ 1 - exp (-c) := by
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · rw [binaryKL_self] at hle; linarith [exp_le_one_iff.mpr (neg_nonpos.mpr hle)]
  · rw [binaryKL_eq_mul_log hp_pos hp1, zero_mul, zero_add, sub_zero, one_mul, one_div,
      log_inv] at hle
    have hlog : -c ≤ log (1 - p) := by linarith
    linarith [exp_log (sub_pos.mpr hp1) ▸ exp_le_exp.mpr hlog]

end LowerBounds

end Cslib.Probability
