/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PoissonBinomial
public import CslibFrontier.Probability.StochasticDomination.Basic
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal

/-!
# Stochastic domination for Poisson-binomial and binomial distributions

Monotonicity of `Cslib.Probability.PMF.coin`, `Cslib.Probability.PMF.poissonBinomial`, and
Mathlib's `ProbabilityTheory.binomial` with respect to first-order stochastic domination,
together with the negative-binomial tail sum
`∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = r / p`.

## Main results

* `Cslib.Probability.PMF.coin_stochasticallyDominates_iff`: `coin q` stochastically dominates
  `coin p` if and only if `(p : ℝ) ≤ q`.
* `Cslib.Probability.PMF.poissonBinomial_stochasticallyDominates_of_forall₂`: parameterwise
  monotonicity of `poissonBinomial`.
* `Cslib.Probability.PMF.poissonBinomial_stochasticallyDominates_replicate`,
  `Cslib.Probability.PMF.replicate_stochasticallyDominates_poissonBinomial`: uniform lower and
  upper binomial bounds for `poissonBinomial`.
* `Cslib.Probability.binomial_stochasticallyDominates_of_le`,
  `Cslib.Probability.binomial_stochasticallyDominates_of_nat_le`: monotonicity of
  `ProbabilityTheory.binomial` in both `p` and `n`.
* `Cslib.Probability.tsum_binomial_real_Iio`: exact waiting-time series
  `∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p` for `0 < (p : ℝ)`.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- `coin q` stochastically dominates `coin p` if and only if `(p : ℝ) ≤ q`. -/
theorem coin_stochasticallyDominates_iff {p q : I} :
    StochasticallyDominates (coin q) (coin p) ↔ (p : ℝ) ≤ q := by
  rw [stochasticallyDominates_bool_iff, coin_apply, coin_apply]
  simp only [↓reduceIte]
  exact ENNReal.ofReal_le_ofReal_iff q.2.1

/-- `coin q` stochastically dominates `coin p` whenever `(p : ℝ) ≤ q`. -/
theorem coin_stochasticallyDominates {p q : I} (hpq : (p : ℝ) ≤ q) :
    StochasticallyDominates (coin q) (coin p) :=
  coin_stochasticallyDominates_iff.mpr hpq

/-- Prepending a larger success probability preserves stochastic domination of Poisson-binomial
distributions. -/
theorem poissonBinomial_stochasticallyDominates_cons {p q : I} {ps qs : List I}
    (hpq : (p : ℝ) ≤ q)
    (hdom : StochasticallyDominates (poissonBinomial qs) (poissonBinomial ps)) :
    StochasticallyDominates (poissonBinomial (q :: qs)) (poissonBinomial (p :: ps)) := by
  rw [poissonBinomial_cons, poissonBinomial_cons]
  refine (coin_stochasticallyDominates hpq).bind
    (fun b => hdom.map fun _ _ hk => by cases b <;> simp [hk]) fun b₁ b₂ hb U hU => ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine (poissonBinomial qs).toOuterMeasure.mono fun k => hU ?_
  cases b₁ <;> cases b₂
  exacts [le_rfl, Nat.le_succ k, absurd hb (by decide), le_rfl]

/-- If `ps` is pointwise bounded by `qs` (`List.Forall₂`), then `poissonBinomial qs`
stochastically dominates `poissonBinomial ps`. -/
theorem poissonBinomial_stochasticallyDominates_of_forall₂ {ps qs : List I}
    (h : List.Forall₂ (fun p q : I => (p : ℝ) ≤ q) ps qs) :
    StochasticallyDominates (poissonBinomial qs) (poissonBinomial ps) := by
  induction h with
  | nil => exact StochasticallyDominates.refl _
  | cons hp _ ih => exact poissonBinomial_stochasticallyDominates_cons hp ih

/-- If every probability in `ps` is at least `p`, then `poissonBinomial ps` stochastically dominates
`poissonBinomial (List.replicate ps.length p)`. -/
theorem poissonBinomial_stochasticallyDominates_replicate {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (p : ℝ) ≤ q) :
    StochasticallyDominates (poissonBinomial ps)
      (poissonBinomial (List.replicate ps.length p)) :=
  poissonBinomial_stochasticallyDominates_of_forall₂ (List.forall₂_iff_get.2
    ⟨by simp, fun i _ hi => by simp [hp _ (List.getElem_mem hi)]⟩)

/-- If every probability in `ps` is at most `p`, then `poissonBinomial (List.replicate ps.length p)`
stochastically dominates `poissonBinomial ps`. -/
theorem replicate_stochasticallyDominates_poissonBinomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (q : ℝ) ≤ p) :
    StochasticallyDominates (poissonBinomial (List.replicate ps.length p))
      (poissonBinomial ps) :=
  poissonBinomial_stochasticallyDominates_of_forall₂ (List.forall₂_iff_get.2
    ⟨by simp, fun i hi _ => by simp [hp _ (List.getElem_mem hi)]⟩)

/-- Adding a `ℕ`-valued step preserves/increases a `PMF ℕ` in stochastic order. -/
theorem bind_add_stochasticallyDominates_left (p q : PMF ℕ) :
    StochasticallyDominates (p.bind fun a => q.map fun b => a + b) p := by
  intro U hU
  simpa only [mul_one] using
    toOuterMeasure_bind_ge_mul_ennreal p (fun a => q.map fun b => a + b) U U (s₂ := 1) le_rfl
      fun a _ ha => by
        rw [PMF.toOuterMeasure_map_apply,
          (PMF.toOuterMeasure_apply_eq_one_iff q ((fun b => a + b) ⁻¹' U)).2
            fun b _ => hU (Nat.le_add_right a b) ha]

/-- Adding more trials increases `poissonBinomial` in stochastic order. -/
theorem poissonBinomial_append_stochasticallyDominates_left (ps qs : List I) :
    StochasticallyDominates (poissonBinomial (ps ++ qs)) (poissonBinomial ps) := by
  rw [poissonBinomial_append]
  exact bind_add_stochasticallyDominates_left (poissonBinomial ps) (poissonBinomial qs)

end Cslib.Probability.PMF

namespace Cslib.Probability

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- `ProbabilityTheory.binomial n q` stochastically dominates `ProbabilityTheory.binomial n p`
whenever `(p : ℝ) ≤ q`. -/
theorem binomial_stochasticallyDominates_of_le (n : ℕ) {p q : I} (hpq : (p : ℝ) ≤ q) :
    StochasticallyDominates (ProbabilityTheory.binomial n q) (ProbabilityTheory.binomial n p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate n q,
    ← PMF.toMeasure_poissonBinomial_replicate n p]
  exact PMF.stochasticallyDominates_iff_toMeasure_nat.mp
    (PMF.poissonBinomial_stochasticallyDominates_of_forall₂
      (List.forall₂_iff_get.2 ⟨by simp, fun _ _ _ => by simpa using hpq⟩))

/-- `ProbabilityTheory.binomial n p` stochastically dominates `ProbabilityTheory.binomial m p`
whenever `m ≤ n`. -/
theorem binomial_stochasticallyDominates_of_nat_le {m n : ℕ} (hmn : m ≤ n) (p : I) :
    StochasticallyDominates (ProbabilityTheory.binomial n p) (ProbabilityTheory.binomial m p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate n p,
    ← PMF.toMeasure_poissonBinomial_replicate m p,
    show n = m + (n - m) by omega, List.replicate_add]
  exact PMF.stochasticallyDominates_iff_toMeasure_nat.mp
    (PMF.poissonBinomial_append_stochasticallyDominates_left _ _)

/-- If every entry of `ps` is at least `p`, then `(poissonBinomial ps).toMeasure` stochastically
dominates `ProbabilityTheory.binomial ps.length p`. -/
theorem toMeasure_poissonBinomial_stochasticallyDominates_binomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (p : ℝ) ≤ q) :
    StochasticallyDominates (PMF.poissonBinomial ps).toMeasure
      (ProbabilityTheory.binomial ps.length p) := by
  rw [← PMF.toMeasure_poissonBinomial_replicate ps.length p]
  exact (PMF.poissonBinomial_stochasticallyDominates_replicate hp).toMeasure

/-- If every entry of `ps` is at most `p`, then `ProbabilityTheory.binomial ps.length p`
stochastically dominates `(poissonBinomial ps).toMeasure`. -/
theorem binomial_stochasticallyDominates_toMeasure_poissonBinomial {ps : List I} {p : I}
    (hp : ∀ q ∈ ps, (q : ℝ) ≤ p) :
    StochasticallyDominates (ProbabilityTheory.binomial ps.length p)
      (PMF.poissonBinomial ps).toMeasure := by
  rw [← PMF.toMeasure_poissonBinomial_replicate ps.length p]
  exact (PMF.replicate_stochasticallyDominates_poissonBinomial hp).toMeasure

/-- Pascal-style recurrence for `(ProbabilityTheory.binomial t p).real (Set.Iio r)`. -/
theorem binomial_real_Iio_succ (t r : ℕ) (p : I) :
    (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) =
      (1 - (p : ℝ)) * (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) +
        (p : ℝ) * (ProbabilityTheory.binomial t p).real (Set.Iio r) := by
  have hsum (n s : ℕ) : (ProbabilityTheory.binomial n p).real (Set.Iio s) =
      ∑ k ∈ Finset.range s, (PMF.poissonBinomial (List.replicate n p) k).toReal := by
    rw [← PMF.toMeasure_poissonBinomial_replicate n p, ← Finset.coe_range, measureReal_def,
      PMF.toMeasure_apply_finset, ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ k]
  simp only [hsum, List.replicate_succ]
  rw [Finset.sum_range_succ' (fun k => (PMF.poissonBinomial (p :: List.replicate t p) k).toReal),
    Finset.sum_range_succ' (fun k => (PMF.poissonBinomial (List.replicate t p) k).toReal)]
  simp only [PMF.poissonBinomial_cons_zero_toReal, PMF.poissonBinomial_cons_succ_toReal,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem binomial_zero_real_Iio_succ (r : ℕ) (p : I) :
    (ProbabilityTheory.binomial 0 p).real (Set.Iio (r + 1)) = 1 := by
  simp [ProbabilityTheory.binomial_zero, Measure.real, Measure.dirac_apply' _ measurableSet_Iio]

/-- Partial sums of `(ProbabilityTheory.binomial t p).real (Set.Iio r)` are bounded by `r / p`. -/
theorem sum_binomial_real_Iio_le (N r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    ∑ t ∈ Finset.range N, (ProbabilityTheory.binomial t p).real (Set.Iio r) ≤ (r : ℝ) / p := by
  rw [le_div_iff₀ hp]
  induction r generalizing N with
  | zero =>
    simp
  | succ r ih =>
    have hrec (t : ℕ) : (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) * (p : ℝ) =
        (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) -
          (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) +
          (ProbabilityTheory.binomial t p).real (Set.Iio r) * (p : ℝ) := by
      linarith [binomial_real_Iio_succ t r p]
    simp_rw [Finset.sum_mul, hrec, Finset.sum_add_distrib, Finset.sum_range_sub',
      ← Finset.sum_mul, binomial_zero_real_Iio_succ]
    push_cast
    linarith [ih N, measureReal_nonneg (μ := ProbabilityTheory.binomial N p) (s := Set.Iio (r + 1))]

/-- Summability of the waiting-time tail probabilities
`(ProbabilityTheory.binomial t p).real (Set.Iio r)` for `0 < (p : ℝ)`. -/
theorem summable_binomial_real_Iio (r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    Summable fun t : ℕ => (ProbabilityTheory.binomial t p).real (Set.Iio r) :=
  summable_of_sum_range_le (fun _ => measureReal_nonneg) fun N => sum_binomial_real_Iio_le N r hp

/-- Exact negative-binomial waiting-time series:
`∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p` for `0 < (p : ℝ)`. -/
theorem tsum_binomial_real_Iio (r : ℕ) {p : I} (hp : 0 < (p : ℝ)) :
    ∑' t : ℕ, (ProbabilityTheory.binomial t p).real (Set.Iio r) = (r : ℝ) / p := by
  rw [eq_div_iff hp.ne']
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have hs1 := summable_binomial_real_Iio (r + 1) hp
    have hs0 := summable_binomial_real_Iio r hp
    have h1 := hs1.tsum_eq_zero_add
    have h2 : ∑' t, (ProbabilityTheory.binomial (t + 1) p).real (Set.Iio (r + 1)) =
        (1 - (p : ℝ)) * ∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio (r + 1)) +
          (p : ℝ) * ∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) := by
      simp_rw [binomial_real_Iio_succ]
      rw [(hs1.mul_left _).tsum_add (hs0.mul_left _), tsum_mul_left, tsum_mul_left]
    rw [binomial_zero_real_Iio_succ] at h1
    push_cast
    linarith

end Cslib.Probability
