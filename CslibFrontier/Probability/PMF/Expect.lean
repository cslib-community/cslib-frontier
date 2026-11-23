/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Density
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Uniform experiments as averages

An experiment that starts by drawing `a` uniformly from a finite type and then runs `f a` outputs
`b` with probability the average over `a` of the probability that `f a` outputs `b`
(`toReal_uniformOfFintype_bind_apply`). In particular, a Boolean function `g` of a uniform sample
is `true` with probability the density of the set where `g` is `true`
(`toReal_uniformOfFintype_map_apply_true`). These translate experiments written with `PMF.bind`
into the vocabulary of `Finset.expect` (`𝔼`) and `Finset.dens`.

## Main results

* `Cslib.Probability.PMF.sum_le_affine`: average pointwise affine bounds.
* `Cslib.Probability.PMF.sum_map_mul`, `.sum_bind_mul`, `.tsum_toReal_map_mul_natCast`: average
  deterministic and random scores (including finite-source pushforwards onto arbitrary codomains).
* `Cslib.Probability.PMF.tsum_map_mul`, `.tsum_bind_mul`: the same laws for extended
  nonnegative scores over arbitrary types.
* `Cslib.Probability.PMF.sq_tsum_le_tsum_sq`: Jensen's inequality `E[g]² ≤ E[g²]` for a
  `[0, 1]`-valued score.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_bind_apply`: a uniform first stage averages the
  second stages.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply`: output probabilities are densities.
* `Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply_true`: the probability that a Boolean
  function of a uniform sample is `true` is a density.
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators ENNReal

/-- Expectation of `k : β → ℝ≥0∞` under `p.map g` equals expectation of `k ∘ g` under `p`. -/
theorem tsum_map_mul {α β : Type*} (p : PMF α) (g : α → β) (k : β → ℝ≥0∞) :
    (∑' b, p.map g b * k b) = ∑' a, p a * k (g a) := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · simp
  · intro b hb
    simp [hb]

/-- Expectation of `k : β → ℝ≥0∞` under `p.bind f` decomposes as an iterated expectation. -/
theorem tsum_bind_mul {α β : Type*} (p : PMF α) (f : α → PMF β) (k : β → ℝ≥0∞) :
    (∑' b, (p.bind f) b * k b) = ∑' a, p a * ∑' b, f a b * k b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact tsum_comm

/-- Averaging a score after a deterministic map averages its composite with that map.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_map_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (score : β → ℝ) :
    ∑ b, ((p.map f) b).toReal * score b = ∑ a, (p a).toReal * score (f a) := by
  classical
  simp only [map_apply_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

/-- Real-valued expectation pushforward for `ℕ`-valued scores from a finite distribution `p` onto
an arbitrary codomain `β`. -/
theorem tsum_toReal_map_mul_natCast {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (c : β → ℕ) :
    (∑' b, ((p.map f) b).toReal * (c b : ℝ)) = ∑ a, (p a).toReal * (c (f a) : ℝ) := by
  have htsum := tsum_map_mul p f (fun b => (c b : ℝ≥0∞))
  conv_rhs at htsum => rw [tsum_fintype]
  have h1 := ENNReal.tsum_toReal_eq (f := fun b => (p.map f) b * (c b : ℝ≥0∞))
    fun b => ENNReal.mul_ne_top (PMF.apply_ne_top _ b) (ENNReal.natCast_ne_top _)
  have h2 := ENNReal.toReal_sum (s := Finset.univ) (f := fun a => p a * (c (f a) : ℝ≥0∞))
    fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top p a) (ENNReal.natCast_ne_top _)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h1 h2
  exact h1.symm.trans ((congrArg ENNReal.toReal htsum).trans h2)

/-- Averaging a score after a random choice averages its conditional scores.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_bind_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (kernel : α → PMF β) (score : β → ℝ) :
    ∑ b, (p.bind kernel b).toReal * score b =
      ∑ a, (p a).toReal * ∑ b, (kernel a b).toReal * score b := by
  simp only [bind_apply_toReal, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The expectation of an affine score is the affine function of its expectation.
Adapted from the cslib `crypto` branch at `5ff69ca`. -/
theorem sum_affine {α : Type*} [Fintype α] (p : PMF α) (a b : ℝ) (score : α → ℝ) :
    (∑ x, (p x).toReal * (a + b * score x)) =
      a + b * ∑ x, (p x).toReal * score x := by
  simp only [mul_add, mul_left_comm _ b, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_toReal, one_mul, ← Finset.mul_sum]

/-- Pointwise affine bounds survive averaging over a finite distribution. -/
theorem sum_le_affine {α : Type*} [Fintype α] (p : PMF α) {a b : ℝ} {score bound : α → ℝ}
    (h : ∀ x, score x ≤ a + b * bound x) :
    (∑ x, (p x).toReal * score x) ≤ a + b * ∑ x, (p x).toReal * bound x :=
  (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg).trans_eq
    (sum_affine p a b bound)

/-- A uniform upper bound on a score also bounds its expectation. -/
theorem sum_mul_le {α : Type*} [Fintype α] (p : PMF α) (score : α → ℝ) (bound : ℝ)
    (hscore : ∀ a, score a ≤ bound) : ∑ a, (p a).toReal * score a ≤ bound :=
  (Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hscore a) ENNReal.toReal_nonneg).trans_eq
    (by rw [← Finset.sum_mul, sum_toReal, one_mul])

/-- Expected absolute difference between two conditional output probabilities at `b`, when both
kernels receive the same finite random input. -/
@[expose] noncomputable def meanAbsDiffAt {ι β : Type*} [Fintype ι] (μ : PMF ι) (b : β)
    (p q : ι → PMF β) : ℝ := ∑ y, (μ y).toReal * |(p y b).toReal - (q y b).toReal|

/-- The probability gap after mixing is bounded by the mean conditional gap. -/
theorem abs_bind_sub_le_meanAbsDiffAt {ι β : Type*} [Fintype ι] (μ : PMF ι) (b : β)
    (p q : ι → PMF β) :
    |(μ.bind p b).toReal - (μ.bind q b).toReal| ≤ meanAbsDiffAt μ b p q := by
  simp only [bind_apply_toReal, meanAbsDiffAt, ← Finset.sum_sub_distrib, ← mul_sub]
  simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
    Finset.abs_sum_le_sum_abs (fun y => (μ y).toReal * ((p y b).toReal - (q y b).toReal))
      Finset.univ

/-- Triangle inequality for the mean conditional probability gap. -/
theorem meanAbsDiffAt_triangle {ι β : Type*} [Fintype ι] (μ : PMF ι) (b : β)
    (p q r : ι → PMF β) :
    meanAbsDiffAt μ b p r ≤ meanAbsDiffAt μ b p q + meanAbsDiffAt μ b q r := by
  unfold meanAbsDiffAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub_le ..) ENNReal.toReal_nonneg

/-- A bound uniform in an independent random choice survives mixing the two kernels. -/
theorem meanAbsDiffAt_bind_le {ι α β : Type*} [Fintype ι] [Finite α] (μ : PMF ι) (ν : PMF α)
    (b : β) (p q : α → ι → PMF β) {B : ℝ} (bound : ∀ j, meanAbsDiffAt μ b (p j) (q j) ≤ B) :
    meanAbsDiffAt μ b (fun y => ν.bind fun j => p j y) (fun y => ν.bind fun j => q j y) ≤ B := by
  let _ := Fintype.ofFinite α
  calc
    _ ≤ ∑ y, (μ y).toReal * meanAbsDiffAt ν b (fun j => p j y) (fun j => q j y) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (abs_bind_sub_le_meanAbsDiffAt ν b _ _) ENNReal.toReal_nonneg
    _ = ∑ j, (ν j).toReal * meanAbsDiffAt μ b (p j) (q j) := by
      simp only [meanAbsDiffAt, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => mul_left_comm ..
    _ ≤ B := sum_mul_le ν _ _ bound

/-- Jensen's inequality `E[g]² ≤ E[g²]` for a function with values in `[0, 1]`. -/
theorem sq_tsum_le_tsum_sq {α : Type*} (μ : PMF α) {g : α → ℝ} (h0 : ∀ a, 0 ≤ g a)
    (h1 : ∀ a, g a ≤ 1) :
    (∑' a, (μ a).toReal * g a) ^ 2 ≤ ∑' a, (μ a).toReal * g a ^ 2 := by
  have hm : Summable fun a => (μ a).toReal := summable_toReal μ
  have hbounded {f : α → ℝ} (f0 : ∀ a, 0 ≤ f a) (f1 : ∀ a, f a ≤ 1) :
      Summable fun a => (μ a).toReal * f a :=
    hm.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (f0 a))
      fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 a)
  have hg := hbounded h0 h1
  have hg2 := hbounded (fun a => sq_nonneg (g a)) fun a => pow_le_one₀ (h0 a) (h1 a)
  set e := ∑' a, (μ a).toReal * g a
  have hexpand : ∑' a, (μ a).toReal * (g a - e) ^ 2 =
      ∑' a, (μ a).toReal * g a ^ 2 - e ^ 2 := by
    have hsplit : (fun a => (μ a).toReal * (g a - e) ^ 2) = fun a =>
        ((μ a).toReal * g a ^ 2 - 2 * e * ((μ a).toReal * g a)) + e ^ 2 * (μ a).toReal := by
      funext a
      ring
    rw [hsplit, (hg2.sub (hg.mul_left (2 * e))).tsum_add (hm.mul_left (e ^ 2)),
      hg2.tsum_sub (hg.mul_left (2 * e)), tsum_mul_left, tsum_mul_left,
      tsum_toReal]
    ring
  have hnonneg : 0 ≤ ∑' a, (μ a).toReal * (g a - e) ^ 2 :=
    tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  linarith

variable {α β : Type*} [Fintype α] [Nonempty α]

/-- An experiment whose first stage draws `a` uniformly outputs `b` with probability the average
over `a` of the probability that the second stage `f a` outputs `b`. -/
theorem toReal_uniformOfFintype_bind_apply (f : α → PMF β) (b : β) :
    ((uniformOfFintype α).bind f b).toReal = 𝔼 a, (f a b).toReal := by
  simp only [bind_apply_toReal, uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, inv_mul_eq_div, Fintype.expect_eq_sum_div_card, sum_div]

/-- The mass of an output of a uniform sample is the density of its fiber. -/
theorem toReal_uniformOfFintype_map_apply [DecidableEq β] (f : α → β) (b : β) :
    ((uniformOfFintype α).map f b).toReal = dens {a | f a = b} := by
  rw [← PMF.bind_pure_comp, toReal_uniformOfFintype_bind_apply]
  have h (a : α) : ((Function.comp PMF.pure f a) b).toReal =
      if f a = b then 1 else 0 := by
    simp only [Function.comp_apply, PMF.pure_apply, eq_comm (a := b)]
    split_ifs <;> rfl
  simp only [h]
  exact Fintype.expect_boole _

/-- A Boolean function `g` of a uniform sample is `true` with probability the density of the set
where `g` is `true`. -/
theorem toReal_uniformOfFintype_map_apply_true (g : α → Bool) :
    ((uniformOfFintype α).map g true).toReal = dens {a | g a = true} :=
  toReal_uniformOfFintype_map_apply g true

end Cslib.Probability.PMF
