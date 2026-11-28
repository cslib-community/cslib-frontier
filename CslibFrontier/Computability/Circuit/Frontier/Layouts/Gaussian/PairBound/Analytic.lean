/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertChecker
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.PlanarVolume
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.Profiles
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.ZeroThreshold
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic Gaussian and polynomial majorant lemmas for matched-pair layouts

This module proves the real-analytic and Gaussian probability bounds consumed by the interval
certificate soundness proof in `Majorant.lean`:

* `starStraddleCost_le`: any `IsAdmissibleStar` triple straddles any threshold with probability at
  most `140367 / 1000000`.
* `arccos_le_starQI`, `arccos_le_crossQI`: soundness of all `7` star and `18` cross concave
  quadratic `arccos` majorants in `Cert.starQI` and `Cert.crossQI`.
* `exists_admissiblePair_wlog`: dihedral order-`8` symmetry reducing `IsAdmissiblePair` to the
  wedge `0 ≤ pairO1 u ∧ pairO1 u ≤ pairO2 u`.
* `pairCost_zero_le_linear`, `pairCost_zero_le_hadamard`: Sheppard linear, drop, spanning-tree, and
  Hadamard variance bounds on `pairCost u 0`.
* `integral_abs_mul_abs_le_sqrt_prod`, `integral_abs_mul_abs_le_div_sqrt`,
  `integral_abs_mul_abs_le_cubic_corr`: bivariate Gaussian absolute-product upper bounds for
  `cexMode ∈ {0, 1, 2}`.
* `pairCost_zero_le_planar_out`, `pairCost_zero_le_planar_in`: conditioned planar quadrilateral and
  interior-cone Gaussian upper bounds on `pairCost u 0`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.PairBound.starStraddleCost`: probability that three vectors
  straddle threshold `t` under `stdGaussian E`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.quadEval`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.quadSlope`: real polynomial and negative-derivative
  evaluators for `Cert.QuadI`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairSab`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairScd`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairRb`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairO1`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairO2`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairTau`: `6`-dimensional Gram coordinates of a
  `4`-tuple of vectors.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.hCub`: convex cubic correlation majorant
  `r + (8 / (3 * π)) * (1 - r) * (1 - r + r ^ 2 / 2)`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.starStraddleCost_le`:
  `IsAdmissibleStar u → starStraddleCost u t ≤ 140367 / 1000000`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.arccos_le_starQI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.arccos_le_crossQI`: soundness of `Cert.starQI` and
  `Cert.crossQI`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.exists_admissiblePair_wlog`: reduction to
  `0 ≤ pairO1 u ∧ pairO1 u ≤ pairO2 u`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost_zero_le_planar_out`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost_zero_le_planar_in`: conditioned planar
  majorants on `pairCost u 0`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

open Cslib.Circuits.Frontier.Switched

/-! ### Part 1: Polynomial `arccos` majorants and `starStraddleCost_le` -/

private noncomputable def qPoly (t : ℝ) : ℝ :=
  1414214 / 1000000 * t + 11786 / 100000 * t ^ 3 + 305 / 10000 * t ^ 5

private noncomputable def qPolyDeriv (t : ℝ) : ℝ :=
  1414214 / 1000000 + 3 * (11786 / 100000) * t ^ 2 + 5 * (305 / 10000) * t ^ 4

private noncomputable def qsPoly (r : ℝ) : ℝ :=
  293982 / 1000000 - 34526 / 10000 * (r - 9571 / 10000) -
    127 / 10 * (r - 9571 / 10000) ^ 2

private noncomputable def qoPoly (r : ℝ) : ℝ :=
  548065 / 1000000 - 192007 / 100000 * (r - 85355 / 100000) -
    185 / 100 * (r - 85355 / 100000) ^ 2

private theorem hasDerivAt_qPoly (t : ℝ) : HasDerivAt qPoly (qPolyDeriv t) t := by
  unfold qPoly qPolyDeriv
  have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one] using hasDerivAt_pow 3 t
  have h5 : HasDerivAt (fun x : ℝ => x ^ 5) (5 * t ^ 4) t := by
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one] using hasDerivAt_pow 5 t
  convert ((h1.const_mul (1414214 / 1000000 : ℝ)).add
    (h3.const_mul (11786 / 100000 : ℝ))).add (h5.const_mul (305 / 10000 : ℝ)) using 1
  ring

private theorem hasDerivAt_two_arctan_div_sqrt {t : ℝ} (ht : t ^ 2 < 2) :
    HasDerivAt (fun x : ℝ => 2 * arctan (x / √(2 - x ^ 2))) (2 / √(2 - t ^ 2)) t := by
  have hpos : 0 < 2 - t ^ 2 := by linarith
  have hspos : 0 < √(2 - t ^ 2) := sqrt_pos.mpr hpos
  have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun x : ℝ => 2 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_pow 2 t) using 1
    ring
  have h3 : HasDerivAt (fun x : ℝ => √(2 - x ^ 2)) (-2 * t / (2 * √(2 - t ^ 2))) t :=
    h2.sqrt hpos.ne'
  have h4 := (h1.div h3 hspos.ne').arctan.const_mul 2
  refine h4.congr_deriv ?_
  dsimp only [Pi.div_apply]
  have hsq : √(2 - t ^ 2) ^ 2 = 2 - t ^ 2 := sq_sqrt hpos.le
  field_simp [hspos.ne']
  rw [hsq]
  ring

private theorem qPolyDeriv_ge {t : ℝ} (ht : t ≤ 45 / 100) (ht0 : 0 ≤ t) :
    2 / √(2 - t ^ 2) ≤ qPolyDeriv t := by
  have hs1 : t ^ 2 ≤ 81 / 400 := by nlinarith
  have hpos : 0 < 2 - t ^ 2 := by linarith
  have hspos : 0 < √(2 - t ^ 2) := sqrt_pos.mpr hpos
  rw [div_le_iff₀ hspos]
  have hqd : 0 ≤ qPolyDeriv t := by unfold qPolyDeriv; positivity
  have hsq : 4 ≤ qPolyDeriv t ^ 2 * (2 - t ^ 2) := by
    set s := t ^ 2
    have hs0 : 0 ≤ s := sq_nonneg t
    have h_s3 : s ^ 3 ≤ 81 / 400 * s ^ 2 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hs1 (sq_nonneg s)
    have h_s4 : s ^ 4 ≤ (81 / 400) ^ 2 * s ^ 2 := by
      calc s ^ 4 = s * s ^ 3 := by ring
        _ ≤ s * (81 / 400 * s ^ 2) := mul_le_mul_of_nonneg_left h_s3 hs0
        _ = 81 / 400 * s ^ 3 := by ring
        _ ≤ 81 / 400 * (81 / 400 * s ^ 2) := mul_le_mul_of_nonneg_left h_s3 (by norm_num)
        _ = (81 / 400) ^ 2 * s ^ 2 := by ring
    have h_s5 : s ^ 5 ≤ (81 / 400) ^ 3 * s ^ 2 := by
      calc s ^ 5 = s * s ^ 4 := by ring
        _ ≤ s * ((81 / 400) ^ 2 * s ^ 2) := mul_le_mul_of_nonneg_left h_s4 hs0
        _ = (81 / 400) ^ 2 * s ^ 3 := by ring
        _ ≤ (81 / 400) ^ 2 * (81 / 400 * s ^ 2) := mul_le_mul_of_nonneg_left h_s3 (by norm_num)
        _ = (81 / 400) ^ 3 * s ^ 2 := by ring
    have heq : qPolyDeriv t = 1414214 / 1000000 + 3 * (11786 / 100000) * s +
        5 * (305 / 10000) * s ^ 2 := by unfold qPolyDeriv; ring
    rw [heq]
    nlinarith [sq_nonneg s]
  have hmul : (qPolyDeriv t * √(2 - t ^ 2)) ^ 2 = qPolyDeriv t ^ 2 * (2 - t ^ 2) := by
    rw [mul_pow, sq_sqrt hpos.le]
  nlinarith [mul_nonneg hqd hspos.le]

private theorem arccos_one_sub_sq_le_qPoly {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 45 / 100) :
    arccos (1 - t ^ 2) ≤ qPoly t := by
  let g : ℝ → ℝ := fun x => 2 * arctan (x / √(2 - x ^ 2))
  have hg_eq : arccos (1 - t ^ 2) = g t := by
    rw [Real.arccos_eq_two_mul_arctan (by nlinarith)]
    have h1 : 1 - (1 - t ^ 2) = t ^ 2 := by ring
    have h2 : 1 + (1 - t ^ 2) = 2 - t ^ 2 := by ring
    rw [h1, h2, sqrt_sq ht0]
  rw [hg_eq]
  have hg_cont : ContinuousOn g (Icc 0 (45 / 100)) := by
    intro x hx
    have hx2 : x ^ 2 < 2 := by nlinarith [hx.1, hx.2]
    exact (hasDerivAt_two_arctan_div_sqrt hx2).continuousAt.continuousWithinAt
  have hq_cont : ContinuousOn qPoly (Icc 0 (45 / 100)) :=
    fun x _ => (hasDerivAt_qPoly x).continuousAt.continuousWithinAt
  exact image_le_of_deriv_right_le_deriv_boundary hg_cont
    (fun x hx => (hasDerivAt_two_arctan_div_sqrt (by nlinarith [hx.1, hx.2.le])).hasDerivWithinAt)
    (by simp only [g, qPoly, zero_div, arctan_zero, mul_zero, zero_pow (by omega : 3 ≠ 0),
      zero_pow (by omega : 5 ≠ 0), add_zero, le_refl]) hq_cont
    (fun x _ => (hasDerivAt_qPoly x).hasDerivWithinAt)
    (fun x hx => qPolyDeriv_ge hx.2.le hx.1) ⟨ht0, ht1⟩

private theorem arccos_le_qs {r : ℝ} (hr0 : 9428 / 10000 ≤ r) (hr1 : r ≤ 1) :
    arccos r ≤ qsPoly r := by
  set t := √(1 - r)
  have ht0 : 0 ≤ t := sqrt_nonneg _
  have ht_sq : t ^ 2 = 1 - r := sq_sqrt (by linarith)
  have ht1 : t ≤ 24 / 100 := by nlinarith
  have hr_eq : r = 1 - t ^ 2 := by linarith
  rw [hr_eq]
  refine (arccos_one_sub_sq_le_qPoly ht0 (by linarith)).trans ?_
  let Q := (1430799608864091091 / 500000000000000000 : ℝ) -
    107535650353943 / 20000000000000 * t - 1271262029 / 100000000 * t ^ 2 - 61 / 2000 * t ^ 3
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    have ht3 : t ^ 3 ≤ 24 / 100 * t ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith [sq_nonneg t]
  have hrem : 0 ≤ qsPoly (1 - t ^ 2) - qPoly t - (t - 20689 / 100000) ^ 2 * Q := by
    unfold qsPoly qPoly
    dsimp only [Q]
    linarith
  linarith [mul_nonneg (sq_nonneg (t - 20689 / 100000)) hQ]

private theorem arccos_le_qo1 {r : ℝ} (hr0 : 79998 / 100000 ≤ r) (hr1 : r ≤ 1) :
    arccos r ≤ qoPoly r := by
  set t := √(1 - r)
  have ht0 : 0 ≤ t := sqrt_nonneg _
  have ht_sq : t ^ 2 = 1 - r := sq_sqrt (by linarith)
  have ht1 : t ≤ 45 / 100 := by nlinarith
  have hr_eq : r = 1 - t ^ 2 := by linarith
  rw [hr_eq]
  refine (arccos_one_sub_sq_le_qPoly ht0 ht1).trans ?_
  let Q := (97070401435204113 / 62500000000000000 : ℝ) -
    7731731110607 / 5000000000000 * t - 93666503 / 50000000 * t ^ 2 - 61 / 2000 * t ^ 3
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    have ht3 : t ^ 3 ≤ 45 / 100 * t ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith [sq_nonneg t]
  have hrem : 0 ≤ qoPoly (1 - t ^ 2) - qPoly t - (t - 38246 / 100000) ^ 2 * Q := by
    unfold qoPoly qPoly
    dsimp only [Q]
    linarith
  linarith [mul_nonneg (sq_nonneg (t - 38246 / 100000)) hQ]

private noncomputable def quadAt (t0 tmax r : ℝ) : ℝ :=
  qPoly t0 - qPolyDeriv t0 / (2 * t0) * (r - (1 - t0 ^ 2)) -
    132 / 100 / (2 * t0 * (tmax + t0) ^ 2) * (r - (1 - t0 ^ 2)) ^ 2

private theorem arccos_le_quadAt {t0 tmax r : ℝ} (ht0 : 0 < t0) (htm : t0 ≤ tmax)
    (hmax : tmax ≤ 45 / 100) (hr0 : 1 - tmax ^ 2 ≤ r) (hr1 : r ≤ 1) :
    arccos r ≤ quadAt t0 tmax r := by
  set t := √(1 - r)
  have ht_nn : 0 ≤ t := sqrt_nonneg _
  have ht_sq : t ^ 2 = 1 - r := sq_sqrt (by linarith)
  have ht_le : t ≤ tmax := by nlinarith
  have ht45 : t ≤ 45 / 100 := ht_le.trans hmax
  have ht045 : t0 ≤ 45 / 100 := htm.trans hmax
  have hr_eq : r = 1 - t ^ 2 := by linarith
  rw [hr_eq]
  refine (arccos_one_sub_sq_le_qPoly ht_nn ht45).trans ?_
  let P : ℝ := 1414214 / 1000000 - 11786 / 100000 * t0 * (2 * t + t0) -
    305 / 10000 * t0 * (2 * t ^ 3 + 4 * t ^ 2 * t0 + 6 * t * t0 ^ 2 + 3 * t0 ^ 3)
  have hP : 132 / 100 ≤ P := by
    have h1 : t0 * (2 * t + t0) ≤ 45 / 100 * (135 / 100) := by nlinarith
    have htsq : t ^ 2 ≤ (45 / 100) ^ 2 := by nlinarith
    have ht0sq : t0 ^ 2 ≤ (45 / 100) ^ 2 := by nlinarith
    have hc1 : t ^ 3 ≤ (45 / 100) ^ 3 := by nlinarith
    have hc2 : t ^ 2 * t0 ≤ (45 / 100) ^ 3 := by nlinarith
    have hc3 : t * t0 ^ 2 ≤ (45 / 100) ^ 3 := by nlinarith
    have hc4 : t0 ^ 3 ≤ (45 / 100) ^ 3 := by nlinarith
    have h2 : t0 * (2 * t ^ 3 + 4 * t ^ 2 * t0 + 6 * t * t0 ^ 2 + 3 * t0 ^ 3) ≤
        45 / 100 * (15 * (45 / 100) ^ 3) := by nlinarith
    dsimp only [P]; linarith
  have hid : 2 * t0 * (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (1 - t ^ 2 - (1 - t0 ^ 2)) -
      qPoly t) = (t - t0) ^ 2 * P := by
    unfold qPoly qPolyDeriv; dsimp only [P]; field_simp [ht0.ne']; ring
  have hsum_pos : 0 < tmax + t0 := by linarith
  have hsq_le : (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2 ≤ (t - t0) ^ 2 * (tmax + t0) ^ 2 := by
    rw [show (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2 = (t - t0) ^ 2 * (t + t0) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  have hcurv : 132 / 100 / (tmax + t0) ^ 2 * (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2 ≤
      (t - t0) ^ 2 * P := by
    have hdiv : 132 / 100 / (tmax + t0) ^ 2 * (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2 ≤
        132 / 100 * (t - t0) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hsum_pos 2)]
      nlinarith
    nlinarith [sq_nonneg (t - t0)]
  have hmul : 2 * t0 * qPoly t ≤ 2 * t0 * quadAt t0 tmax (1 - t ^ 2) := by
    unfold quadAt
    have hrew : 2 * t0 * (132 / 100 / (2 * t0 * (tmax + t0) ^ 2) *
        (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2) =
        132 / 100 / (tmax + t0) ^ 2 * (1 - t ^ 2 - (1 - t0 ^ 2)) ^ 2 := by
      field_simp [ht0.ne', hsum_pos.ne']
    linarith
  exact le_of_mul_le_mul_left hmul (by positivity)

/-- Real quadratic majorant corresponding to a fixed-point `Cert.QuadI` entry at scale `10 ^ 8`. -/
@[expose] noncomputable def quadEval (q : Cert.QuadI) (r : ℝ) : ℝ :=
  (q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (r - (q.r0 : ℝ) / 100000000) -
    (q.c2 : ℝ) / 100000000 * (r - (q.r0 : ℝ) / 100000000) ^ 2

/-- Negative derivative `-quadEval' q r` of `quadEval q` at `r`. -/
@[expose] noncomputable def quadSlope (q : Cert.QuadI) (r : ℝ) : ℝ :=
  (q.c1 : ℝ) / 100000000 + 2 * ((q.c2 : ℝ) / 100000000 * (r - (q.r0 : ℝ) / 100000000))

theorem quadEval_taylor (q : Cert.QuadI) (r m : ℝ) :
    quadEval q r = quadEval q m - quadSlope q m * (r - m) -
      (q.c2 : ℝ) / 100000000 * (r - m) ^ 2 := by
  unfold quadEval quadSlope; ring

theorem quadEval_anti_on {q : Cert.QuadI} {r1 r2 : ℝ} (hc2 : 0 ≤ (q.c2 : ℝ))
    (hsl : 0 ≤ quadSlope q r1) (hle : r1 ≤ r2) :
    quadEval q r2 ≤ quadEval q r1 := by
  rw [quadEval_taylor q r2 r1]
  have h1 : 0 ≤ quadSlope q r1 * (r2 - r1) := mul_nonneg hsl (by linarith)
  have h2 : 0 ≤ (q.c2 : ℝ) / 100000000 * (r2 - r1) ^ 2 :=
    mul_nonneg (div_nonneg hc2 (by norm_num)) (sq_nonneg _)
  linarith

private theorem arccos_le_quadEval_of_witness {q : Cert.QuadI} (t0 tmax : ℝ)
    (hc2_nn : 0 ≤ (q.c2 : ℝ))
    (ht0 : 0 < t0) (htm : t0 ≤ tmax) (hmax : tmax ≤ 45 / 100)
    (hr0_eq : 1 - t0 ^ 2 = (q.r0 : ℝ) / 100000000)
    (hrmin : 1 - tmax ^ 2 ≤ (q.rmin : ℝ) / 100000000)
    (hdc2 : (q.c2 : ℝ) / 100000000 ≤ 132 / 100 / (2 * t0 * (tmax + t0) ^ 2))
    (hlo : qPoly t0 - qPolyDeriv t0 / (2 * t0) *
        ((q.rmin : ℝ) / 100000000 - (q.r0 : ℝ) / 100000000) ≤
      (q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 *
        ((q.rmin : ℝ) / 100000000 - (q.r0 : ℝ) / 100000000))
    (hhi : qPoly t0 - qPolyDeriv t0 / (2 * t0) * (1 - (q.r0 : ℝ) / 100000000) ≤
      (q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (1 - (q.r0 : ℝ) / 100000000))
    {r : ℝ} (hr0 : (q.rmin : ℝ) / 100000000 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ (q.c2 : ℝ) ∧ arccos r ≤ quadEval q r := by
  refine ⟨hc2_nn, (arccos_le_quadAt ht0 htm hmax (hrmin.trans hr0) hr1).trans ?_⟩
  unfold quadAt quadEval
  rw [hr0_eq]
  set rminR := (q.rmin : ℝ) / 100000000
  set r0R := (q.r0 : ℝ) / 100000000
  have hsq : (q.c2 : ℝ) / 100000000 * (r - r0R) ^ 2 ≤
      132 / 100 / (2 * t0 * (tmax + t0) ^ 2) * (r - r0R) ^ 2 :=
    mul_le_mul_of_nonneg_right hdc2 (sq_nonneg _)
  have hlin : qPoly t0 - qPolyDeriv t0 / (2 * t0) * (r - r0R) ≤
      (q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (r - r0R) := by
    rcases eq_or_lt_of_le (hr0.trans hr1) with hreq | hrlt
    · have : r = 1 := by linarith
      subst this; exact hhi
    · have hcomb : ((1 - r) * ((q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (rminR - r0R) -
            (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (rminR - r0R))) +
          (r - rminR) * ((q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (1 - r0R) -
            (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (1 - r0R)))) =
          (1 - rminR) * ((q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (r - r0R) -
            (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (r - r0R))) := by ring
      have hnn1 : 0 ≤ (1 - r) * ((q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (rminR - r0R) -
          (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (rminR - r0R))) :=
        mul_nonneg (by linarith) (by linarith)
      have hnn2 : 0 ≤ (r - rminR) * ((q.c0 : ℝ) / 100000000 - (q.c1 : ℝ) / 100000000 * (1 - r0R) -
          (qPoly t0 - qPolyDeriv t0 / (2 * t0) * (1 - r0R))) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  linarith

theorem arccos_le_starQI {ia : Nat} {q : Cert.QuadI} (hq : Cert.starQI ia = some q)
    {r : ℝ} (hr0 : (q.rmin : ℝ) / 100000000 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ (q.c2 : ℝ) ∧ arccos r ≤ quadEval q r := by
  match ia with
  | 0 =>
    injection hq with hq'; subst hq'
    refine ⟨by norm_num, (arccos_le_qs (by norm_num at hr0; linarith) hr1).trans_eq ?_⟩
    unfold qsPoly quadEval; norm_num
  | 1 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (47 / 200) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 2 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (21 / 100) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 3 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (7 / 40) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 4 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 100) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 5 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (17 / 200) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 6 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (1 / 25) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | n + 7 => cases hq

theorem arccos_le_crossQI {ic : Nat} {q : Cert.QuadI} (hq : Cert.crossQI ic = some q)
    {r : ℝ} (hr0 : (q.rmin : ℝ) / 100000000 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ (q.c2 : ℝ) ∧ arccos r ≤ quadEval q r := by
  match ic with
  | 0 =>
    injection hq with hq'; subst hq'
    refine ⟨by norm_num, (arccos_le_qo1 (by norm_num at hr0; linarith) hr1).trans_eq ?_⟩
    unfold qoPoly quadEval; norm_num
  | 1 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (11 / 25) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 2 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (21 / 50) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 3 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (19 / 50) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 4 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (7 / 20) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 5 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (31 / 100) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 6 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 50) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 7 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (1 / 5) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 8 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 100) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 9 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (3 / 50) (179 / 400)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 10 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (7 / 20) (41 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 11 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 50) (41 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 12 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (1 / 5) (41 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 13 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 50) (9 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 14 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (1 / 5) (9 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 15 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 100) (3 / 10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 16 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (13 / 100) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | 17 =>
    injection hq with hq'; subst hq'
    exact arccos_le_quadEval_of_witness (3 / 50) (6 / 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [qPoly, qPolyDeriv]) (by norm_num [qPoly, qPolyDeriv]) hr0 hr1
  | n + 18 => cases hq

private theorem star_qsPoly_sum_le {r1 r2 r3 : ℝ}
    (hr3 : 9428 / 10000 ≤ r3) (h13 : r3 ≤ 1)
    (hpoly : 4 * (9571 / 10000 : ℝ) ^ 3 -
      9571 / 10000 * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - r1 * r2 * r3 ≤ 0) :
    qsPoly r1 + qsPoly r2 + qsPoly r3 ≤ 2 * (3141592 / 1000000) * (140367 / 1000000) := by
  let x := r1 - 9571 / 10000
  let y := r2 - 9571 / 10000
  let z := r3 - 9571 / 10000
  have hxyz : x * y * z ≤ 429 / 20000 * (x ^ 2 + y ^ 2) := by
    have hz_lo : -143 / 10000 ≤ z := by dsimp only [z]; linarith
    have hz_hi : z ≤ 429 / 10000 := by dsimp only [z]; linarith
    rcases le_or_gt 0 z with hz0 | hz0
    · have h1 : 2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
      have h2 := mul_le_mul_of_nonneg_right h1 hz0
      have h3 := mul_le_mul_of_nonneg_left hz_hi (add_nonneg (sq_nonneg x) (sq_nonneg y))
      linarith [sq_nonneg x, sq_nonneg y]
    · have h1 : -2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x + y)]
      have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ -z)
      have h3 := mul_le_mul_of_nonneg_left (by linarith : -z ≤ 143 / 10000)
        (add_nonneg (sq_nonneg x) (sq_nonneg y))
      have hring : -2 * x * y * -z = 2 * (x * y * z) := by ring
      linarith [sq_nonneg x, sq_nonneg y]
  have hcomb : qsPoly r1 + qsPoly r2 + qsPoly r3 -
      345260000 / 274812123 * (4 * (9571 / 10000 : ℝ) ^ 3 -
        9571 / 10000 * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - r1 * r2 * r3) ≤
      2 * (3141592 / 1000000) * (140367 / 1000000) := by
    have hid : qsPoly r1 + qsPoly r2 + qsPoly r3 -
        345260000 / 274812123 * (4 * (9571 / 10000 : ℝ) ^ 3 -
          9571 / 10000 * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - r1 * r2 * r3) =
        3 * (293982 / 1000000) +
        (-127 / 10 + 345260000 / 274812123 * (9571 / 10000)) * (x ^ 2 + y ^ 2 + z ^ 2) +
        345260000 / 274812123 * (9571 / 10000) * (x * y + x * z + y * z) +
        345260000 / 274812123 * (x * y * z) := by
      unfold qsPoly; dsimp only [x, y, z]; ring
    rw [hid]
    have hsum_sq : x * y + x * z + y * z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  linarith

section StarAndPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Probability under `stdGaussian E` that three vectors `u : Fin 3 → E` straddle threshold `t`. -/
@[expose] noncomputable def starStraddleCost (u : Fin 3 → E) (t : ℝ) : ℝ :=
  (stdGaussian E).real {x | StraddlesOn (fun i : Fin 3 => ⟪u i, x⟫) t univ}

private def bDiff (a b : Bool) : ℕ :=
  if a != b then 1 else 0

private theorem star_bool_le :
    ∀ b0 b1 b2 : Bool,
      2 * (if (b0 && b1 && b2) = false ∧ (b0 || b1 || b2) = true then 1 else 0) ≤
        bDiff b0 b1 + bDiff b0 b2 + bDiff b1 b2 := by
  decide

private theorem bDiff_eq_indicator_uIoc (a b t : ℝ) :
    (bDiff (decide (a < t)) (decide (b < t)) : ℝ) =
      ({z : ℝ × ℝ | t ∈ Ι z.1 z.2}.indicator (1 : (ℝ × ℝ) → ℝ) (a, b)) := by
  by_cases ha : a < t <;> by_cases hb : b < t
  · have hnm : t ∉ Ι a b := by
      rw [mem_uIoc]; rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith
    simp only [bDiff, ha, hb, decide_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_zero, mem_ofPred_eq, hnm, not_false_eq_true, indicator_of_notMem]
  · have hm : t ∈ Ι a b := mem_uIoc.mpr (Or.inl ⟨ha, not_lt.mp hb⟩)
    simp only [bDiff, ha, hb, decide_true, decide_false, Bool.bne_false, ↓reduceIte,
      Nat.cast_one, mem_ofPred_eq, hm, indicator_of_mem, Pi.one_apply]
  · have hm : t ∈ Ι a b := mem_uIoc.mpr (Or.inr ⟨hb, not_lt.mp ha⟩)
    simp only [bDiff, ha, hb, decide_false, decide_true, Bool.false_bne, ↓reduceIte,
      Nat.cast_one, mem_ofPred_eq, hm, indicator_of_mem, Pi.one_apply]
  · have hnm : t ∉ Ι a b := by
      rw [mem_uIoc]; rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact (ha h).elim
      · exact (hb h).elim
    simp only [bDiff, ha, hb, decide_false, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_zero, mem_ofPred_eq, hnm, not_false_eq_true, indicator_of_notMem]

private theorem starStraddleCost_le_sheppard {u : Fin 3 → E} (hu : ∀ i, ‖u i‖ = 1) (t : ℝ) :
    starStraddleCost u t ≤
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 2⟫) / (2 * π) := by
  classical
  set μ := stdGaussian E
  set S : Set E := {x | StraddlesOn (fun i : Fin 3 => ⟪u i, x⟫) t univ}
  set D01 : Set E := {x | t ∈ Ι ⟪u 0, x⟫ ⟪u 1, x⟫}
  set D02 : Set E := {x | t ∈ Ι ⟪u 0, x⟫ ⟪u 2, x⟫}
  set D12 : Set E := {x | t ∈ Ι ⟪u 1, x⟫ ⟪u 2, x⟫}
  have hSm : MeasurableSet S := by
    have heq : S = (⋃ i : Fin 3, {x : E | ⟪u i, x⟫ < t}) ∩
        (⋃ i : Fin 3, {x : E | t ≤ ⟪u i, x⟫}) := by
      ext x; simp only [S, StraddlesOn, mem_ofPred_eq, mem_univ, true_and, mem_inter_iff,
        mem_iUnion]
    rw [heq]
    exact (MeasurableSet.iUnion fun i =>
        measurableSet_lt (by fun_prop : Measurable fun x : E => ⟪u i, x⟫) measurable_const).inter
      (MeasurableSet.iUnion fun i =>
        measurableSet_le measurable_const (by fun_prop : Measurable fun x : E => ⟪u i, x⟫))
  have hDm (i j : Fin 3) : MeasurableSet {x : E | t ∈ Ι ⟪u i, x⟫ ⟪u j, x⟫} :=
    measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) t
  have hpt (x : E) : 2 * S.indicator (1 : E → ℝ) x ≤
      D01.indicator (1 : E → ℝ) x + D02.indicator (1 : E → ℝ) x + D12.indicator (1 : E → ℝ) x := by
    let b (i : Fin 3) : Bool := decide (⟪u i, x⟫ < t)
    have hS_iff : x ∈ S ↔ (b 0 && b 1 && b 2) = false ∧ (b 0 || b 1 || b 2) = true := by
      simp only [S, mem_ofPred_eq, StraddlesOn, mem_univ, true_and, b, ← not_lt]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        fin_cases i <;> fin_cases j <;> simp_all
      · rintro ⟨h1, h2⟩
        by_cases h0 : ⟪u 0, x⟫ < t <;> by_cases h1' : ⟪u 1, x⟫ < t <;>
          by_cases h2' : ⟪u 2, x⟫ < t
        · simp [h0, h1', h2'] at h1
        · exact ⟨⟨0, h0⟩, ⟨2, h2'⟩⟩
        · exact ⟨⟨0, h0⟩, ⟨1, h1'⟩⟩
        · exact ⟨⟨0, h0⟩, ⟨1, h1'⟩⟩
        · exact ⟨⟨1, h1'⟩, ⟨0, h0⟩⟩
        · exact ⟨⟨1, h1'⟩, ⟨0, h0⟩⟩
        · exact ⟨⟨2, h2'⟩, ⟨0, h0⟩⟩
        · simp [h0, h1', h2'] at h2
    have h2 := star_bool_le (b 0) (b 1) (b 2)
    have hcast : (2 : ℝ) * (if (b 0 && b 1 && b 2) = false ∧ (b 0 || b 1 || b 2) = true
        then 1 else 0) ≤ (bDiff (b 0) (b 1) : ℝ) + bDiff (b 0) (b 2) + bDiff (b 1) (b 2) := by
      exact_mod_cast h2
    have hd (i j : Fin 3) : (bDiff (b i) (b j) : ℝ) =
        ({x : E | t ∈ Ι ⟪u i, x⟫ ⟪u j, x⟫}).indicator (1 : E → ℝ) x := by
      rw [bDiff_eq_indicator_uIoc]
      by_cases hm : t ∈ Ι ⟪u i, x⟫ ⟪u j, x⟫ <;>
        simp only [mem_ofPred_eq, hm, not_false_eq_true, indicator_of_mem, indicator_of_notMem,
          Pi.one_apply]
    rw [hd 0 1, hd 0 2, hd 1 2] at hcast
    by_cases hx : x ∈ S
    · have hb := hS_iff.mp hx
      simpa only [D01, D02, D12, hx, hb.1, hb.2, and_self, ↓reduceIte, indicator_of_mem,
        Pi.one_apply] using hcast
    · have hnn : 0 ≤ D01.indicator (1 : E → ℝ) x + D02.indicator (1 : E → ℝ) x +
          D12.indicator (1 : E → ℝ) x :=
        add_nonneg (add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) x)
          (indicator_nonneg (fun _ _ => zero_le_one) x))
          (indicator_nonneg (fun _ _ => zero_le_one) x)
      simpa only [hx, not_false_eq_true, indicator_of_notMem, mul_zero] using hnn
  have hintS : Integrable (S.indicator (1 : E → ℝ)) μ := (integrable_const 1).indicator hSm
  have hint01 : Integrable (D01.indicator (1 : E → ℝ)) μ :=
    (integrable_const 1).indicator (hDm 0 1)
  have hint02 : Integrable (D02.indicator (1 : E → ℝ)) μ :=
    (integrable_const 1).indicator (hDm 0 2)
  have hint12 : Integrable (D12.indicator (1 : E → ℝ)) μ :=
    (integrable_const 1).indicator (hDm 1 2)
  have hint : ∫ x, 2 * S.indicator (1 : E → ℝ) x ∂μ ≤
      ∫ x, (D01.indicator (1 : E → ℝ) x + D02.indicator (1 : E → ℝ) x +
        D12.indicator (1 : E → ℝ) x) ∂μ :=
    integral_mono (hintS.const_mul 2) ((hint01.add hint02).add hint12) hpt
  rw [integral_const_mul, integral_indicator_one hSm,
    integral_add (f := fun x => D01.indicator (1 : E → ℝ) x + D02.indicator (1 : E → ℝ) x)
      (hint01.add hint02) hint12,
    integral_add hint01 hint02, integral_indicator_one (hDm 0 1),
    integral_indicator_one (hDm 0 2), integral_indicator_one (hDm 1 2)] at hint
  have hsh (i j : Fin 3) : μ.real {x | t ∈ Ι ⟪u i, x⟫ ⟪u j, x⟫} ≤ arccos ⟪u i, u j⟫ / π := by
    refine (measureReal_stdGaussian_mem_uIoc_le_angle ((hu i).trans (hu j).symm) t).trans_eq ?_
    rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one (hu i) (hu j)]
  have h01 := hsh 0 1; have h02 := hsh 0 2; have h12 := hsh 1 2
  have hpi : 0 < π := pi_pos
  change 2 * starStraddleCost u t ≤ _ at hint
  have hdiv : arccos ⟪u 0, u 1⟫ / π + arccos ⟪u 0, u 2⟫ / π + arccos ⟪u 1, u 2⟫ / π =
      2 * ((arccos ⟪u 0, u 1⟫ + arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 2⟫) / (2 * π)) := by ring
  linarith

/-- **Unmatched-vertex star majorant.** Any admissible triple of unit vectors straddles any
threshold `t` with probability at most `140367 / 1000000`. -/
theorem starStraddleCost_le {u : Fin 3 → E} (h : IsAdmissibleStar u) (t : ℝ) :
    starStraddleCost u t ≤ 140367 / 1000000 := by
  rcases h with ⟨hu, hr01, hr02, hr12, hpoly⟩
  have h1 (i j : Fin 3) : ⟪u i, u j⟫ ≤ 1 :=
    (real_inner_le_norm _ _).trans_eq (by rw [hu i, hu j, mul_one])
  have hq01 := arccos_le_qs hr01 (h1 0 1)
  have hq02 := arccos_le_qs hr02 (h1 0 2)
  have hq12 := arccos_le_qs hr12 (h1 1 2)
  have hsh := starStraddleCost_le_sheppard hu t
  have hpi : (3141592 / 1000000 : ℝ) < π := by linarith [pi_gt_d20]
  have hsos := star_qsPoly_sum_le hr12 (h1 1 2) hpoly
  have hsum : arccos ⟪u 0, u 1⟫ + arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 2⟫ ≤
      2 * π * (140367 / 1000000) := by
    nlinarith
  exact hsh.trans ((div_le_iff₀ (by positivity)).mpr (by linarith))

/-! ### Part 2: `6`-dimensional Gram coordinates and dihedral `D_4` symmetry -/

/-- Intra-edge inner product `⟪u 0, u 1⟫` of the first matched star. -/
@[expose] noncomputable def pairSab (u : Fin 4 → E) : ℝ := ⟪u 0, u 1⟫

/-- Intra-edge inner product `⟪u 2, u 3⟫` of the second matched star. -/
@[expose] noncomputable def pairScd (u : Fin 4 → E) : ℝ := ⟪u 2, u 3⟫

/-- Mean cross-edge inner product `(⟪u 0, u 2⟫ + ⟪u 1, u 3⟫ + ⟪u 0, u 3⟫ + ⟪u 1, u 2⟫) / 4`. -/
@[expose] noncomputable def pairRb (u : Fin 4 → E) : ℝ :=
  (⟪u 0, u 2⟫ + ⟪u 1, u 3⟫ + ⟪u 0, u 3⟫ + ⟪u 1, u 2⟫) / 4

/-- First antisymmetric cross-edge Gram coordinate of a matched pair. -/
@[expose] noncomputable def pairO1 (u : Fin 4 → E) : ℝ :=
  (⟪u 0, u 2⟫ - ⟪u 1, u 3⟫ + ⟪u 0, u 3⟫ - ⟪u 1, u 2⟫) / 4

/-- Second antisymmetric cross-edge Gram coordinate of a matched pair. -/
@[expose] noncomputable def pairO2 (u : Fin 4 → E) : ℝ :=
  (⟪u 0, u 2⟫ - ⟪u 1, u 3⟫ - ⟪u 0, u 3⟫ + ⟪u 1, u 2⟫) / 4

/-- Balanced twist cross-edge Gram coordinate of a matched pair. -/
@[expose] noncomputable def pairTau (u : Fin 4 → E) : ℝ :=
  (⟪u 0, u 2⟫ + ⟪u 1, u 3⟫ - ⟪u 0, u 3⟫ - ⟪u 1, u 2⟫) / 4

private def perm01 : Fin 4 → Fin 4
  | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3

private def perm23 : Fin 4 → Fin 4
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2

private def permPairs : Fin 4 → Fin 4
  | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1

private theorem schurPairIneq_perm01 {sab scd sac sbd sad sbc σ : ℝ}
    (h : schurPairIneq sab scd sac sbd sad sbc (-σ)) :
    schurPairIneq sab scd sbc sad sbd sac σ := by
  unfold schurPairIneq at h ⊢
  dsimp only at h ⊢
  linarith [show (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 - scd) -
          (2 * (3 / 14 * ((sbc + sad + sbd + sac) / 4) +
            σ * (8 / 35) * ((sbc + sad - sbd - sac) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sbc - sad + sbd - sac) / 4) +
            σ * (8 / 35) * ((sbc - sad - sbd + sac) / 4))) ^ 2 =
      (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 - scd) -
          (2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))) ^ 2 by ring,
    show (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * (3 / 14 * ((sbc - sad - sbd + sac) / 4) +
            σ * (8 / 35) * ((sbc - sad + sbd - sac) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sbc + sad - sbd - sac) / 4) +
            σ * (8 / 35) * ((sbc + sad + sbd + sac) / 4))) ^ 2 =
      (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4))) ^ 2 by ring,
    show ((1322905 / 1000000 + sab) *
          (2 * (3 / 14 * ((sbc + sad + sbd + sac) / 4) +
            σ * (8 / 35) * ((sbc + sad - sbd - sac) / 4))) *
          (2 * (3 / 14 * ((sbc - sad - sbd + sac) / 4) +
            σ * (8 / 35) * ((sbc - sad + sbd - sac) / 4))) +
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sbc - sad + sbd - sac) / 4) +
            σ * (8 / 35) * ((sbc - sad - sbd + sac) / 4))) *
          (2 * (3 / 14 * ((sbc + sad - sbd - sac) / 4) +
            σ * (8 / 35) * ((sbc + sad + sbd + sac) / 4)))) ^ 2 =
      ((1322905 / 1000000 + sab) *
          (2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))) *
          (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) +
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))) *
          (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4)))) ^ 2 by ring]

private theorem schurPairIneq_perm23 {sab scd sac sbd sad sbc σ : ℝ}
    (h : schurPairIneq sab scd sac sbd sad sbc (-σ)) :
    schurPairIneq sab scd sad sbc sac sbd σ := by
  unfold schurPairIneq at h ⊢
  dsimp only at h ⊢
  linarith [show (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 - scd) -
          (2 * (3 / 14 * ((sad + sbc + sac + sbd) / 4) +
            σ * (8 / 35) * ((sad + sbc - sac - sbd) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sad - sbc + sac - sbd) / 4) +
            σ * (8 / 35) * ((sad - sbc - sac + sbd) / 4))) ^ 2 =
      (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 - scd) -
          (2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))) ^ 2 by ring,
    show (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * (3 / 14 * ((sad - sbc - sac + sbd) / 4) +
            σ * (8 / 35) * ((sad - sbc + sac - sbd) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sad + sbc - sac - sbd) / 4) +
            σ * (8 / 35) * ((sad + sbc + sac + sbd) / 4))) ^ 2 =
      (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) ^ 2) -
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4))) ^ 2 by ring,
    show ((1322905 / 1000000 + sab) *
          (2 * (3 / 14 * ((sad + sbc + sac + sbd) / 4) +
            σ * (8 / 35) * ((sad + sbc - sac - sbd) / 4))) *
          (2 * (3 / 14 * ((sad - sbc - sac + sbd) / 4) +
            σ * (8 / 35) * ((sad - sbc + sac - sbd) / 4))) +
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sad - sbc + sac - sbd) / 4) +
            σ * (8 / 35) * ((sad - sbc - sac + sbd) / 4))) *
          (2 * (3 / 14 * ((sad + sbc - sac - sbd) / 4) +
            σ * (8 / 35) * ((sad + sbc + sac + sbd) / 4)))) ^ 2 =
      ((1322905 / 1000000 + sab) *
          (2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))) *
          (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) +
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))) *
          (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
            -σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4)))) ^ 2 by ring]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isAdmissiblePair_comp_perm01 {u : Fin 4 → E} (h : IsAdmissiblePair u) :
    IsAdmissiblePair (u ∘ perm01) := by
  rcases h with ⟨hu, hab, hcd, hac, had, hbc, hbd, hs1, hs2, hs3, hs4⟩
  have c10 : ⟪u 1, u 0⟫ = ⟪u 0, u 1⟫ := real_inner_comm _ _
  refine ⟨fun i => hu (perm01 i), ?_, hcd, hbc, hbd, hac, had, ?_, ?_, ?_, ?_⟩
  · change (9428 / 10000 : ℝ) ≤ ⟪u 1, u 0⟫; rwa [c10]
  · change schurPairIneq ⟪u 1, u 0⟫ ⟪u 2, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ ⟪u 1, u 3⟫ ⟪u 0, u 2⟫ 1
    rw [c10]; exact schurPairIneq_perm01 hs2
  · change schurPairIneq ⟪u 1, u 0⟫ ⟪u 2, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ ⟪u 1, u 3⟫ ⟪u 0, u 2⟫ (-1)
    rw [c10]; exact schurPairIneq_perm01 (by simpa only [neg_neg] using hs1)
  · change schurPairIneq ⟪u 2, u 3⟫ ⟪u 1, u 0⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ 1
    rw [c10]; exact schurPairIneq_perm23 hs4
  · change schurPairIneq ⟪u 2, u 3⟫ ⟪u 1, u 0⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ (-1)
    rw [c10]; exact schurPairIneq_perm23 (by simpa only [neg_neg] using hs3)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isAdmissiblePair_comp_perm23 {u : Fin 4 → E} (h : IsAdmissiblePair u) :
    IsAdmissiblePair (u ∘ perm23) := by
  rcases h with ⟨hu, hab, hcd, hac, had, hbc, hbd, hs1, hs2, hs3, hs4⟩
  have c32 : ⟪u 3, u 2⟫ = ⟪u 2, u 3⟫ := real_inner_comm _ _
  refine ⟨fun i => hu (perm23 i), hab, ?_, had, hac, hbd, hbc, ?_, ?_, ?_, ?_⟩
  · change (9428 / 10000 : ℝ) ≤ ⟪u 3, u 2⟫; rwa [c32]
  · change schurPairIneq ⟪u 0, u 1⟫ ⟪u 3, u 2⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ 1
    rw [c32]; exact schurPairIneq_perm23 hs2
  · change schurPairIneq ⟪u 0, u 1⟫ ⟪u 3, u 2⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ (-1)
    rw [c32]; exact schurPairIneq_perm23 (by simpa only [neg_neg] using hs1)
  · change schurPairIneq ⟪u 3, u 2⟫ ⟪u 0, u 1⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ ⟪u 1, u 3⟫ ⟪u 0, u 2⟫ 1
    rw [c32]; exact schurPairIneq_perm01 hs4
  · change schurPairIneq ⟪u 3, u 2⟫ ⟪u 0, u 1⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ ⟪u 1, u 3⟫ ⟪u 0, u 2⟫ (-1)
    rw [c32]; exact schurPairIneq_perm01 (by simpa only [neg_neg] using hs3)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isAdmissiblePair_comp_permPairs {u : Fin 4 → E} (h : IsAdmissiblePair u) :
    IsAdmissiblePair (u ∘ permPairs) := by
  rcases h with ⟨hu, hab, hcd, hac, had, hbc, hbd, hs1, hs2, hs3, hs4⟩
  have c02 : ⟪u 2, u 0⟫ = ⟪u 0, u 2⟫ := real_inner_comm _ _
  have c13 : ⟪u 3, u 1⟫ = ⟪u 1, u 3⟫ := real_inner_comm _ _
  have c03 : ⟪u 3, u 0⟫ = ⟪u 0, u 3⟫ := real_inner_comm _ _
  have c12 : ⟪u 2, u 1⟫ = ⟪u 1, u 2⟫ := real_inner_comm _ _
  refine ⟨fun i => hu (permPairs i), hcd, hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change _ ≤ ⟪u 2, u 0⟫; rwa [c02]
  · change _ ≤ ⟪u 2, u 1⟫; rwa [c12]
  · change _ ≤ ⟪u 3, u 0⟫; rwa [c03]
  · change _ ≤ ⟪u 3, u 1⟫; rwa [c13]
  · change schurPairIneq ⟪u 2, u 3⟫ ⟪u 0, u 1⟫ ⟪u 2, u 0⟫ ⟪u 3, u 1⟫ ⟪u 2, u 1⟫ ⟪u 3, u 0⟫ 1
    rwa [c02, c13, c12, c03]
  · change schurPairIneq ⟪u 2, u 3⟫ ⟪u 0, u 1⟫ ⟪u 2, u 0⟫ ⟪u 3, u 1⟫ ⟪u 2, u 1⟫ ⟪u 3, u 0⟫ (-1)
    rwa [c02, c13, c12, c03]
  · change schurPairIneq ⟪u 0, u 1⟫ ⟪u 2, u 3⟫ ⟪u 2, u 0⟫ ⟪u 3, u 1⟫ ⟪u 3, u 0⟫ ⟪u 2, u 1⟫ 1
    rwa [c02, c13, c12, c03]
  · change schurPairIneq ⟪u 0, u 1⟫ ⟪u 2, u 3⟫ ⟪u 2, u 0⟫ ⟪u 3, u 1⟫ ⟪u 3, u 0⟫ ⟪u 2, u 1⟫ (-1)
    rwa [c02, c13, c12, c03]

private theorem twoVertexCost_perm01 :
    ∀ b0 b1 b2 b3 : Bool, twoVertexCost b1 b0 b2 b3 = twoVertexCost b0 b1 b2 b3 := by decide

private theorem twoVertexCost_perm23 :
    ∀ b0 b1 b2 b3 : Bool, twoVertexCost b0 b1 b3 b2 = twoVertexCost b0 b1 b2 b3 := by decide

private theorem twoVertexCost_permPairs :
    ∀ b0 b1 b2 b3 : Bool, twoVertexCost b2 b3 b0 b1 = twoVertexCost b0 b1 b2 b3 := by decide

private theorem pairCost_comp_perm01 (u : Fin 4 → E) (t : ℝ) :
    pairCost (u ∘ perm01) t = pairCost u t := by
  rw [pairCost_eq_integral_twoVertexCost, pairCost_eq_integral_twoVertexCost]
  congr 1 with x
  exact_mod_cast twoVertexCost_perm01 _ _ _ _

private theorem pairCost_comp_perm23 (u : Fin 4 → E) (t : ℝ) :
    pairCost (u ∘ perm23) t = pairCost u t := by
  rw [pairCost_eq_integral_twoVertexCost, pairCost_eq_integral_twoVertexCost]
  congr 1 with x
  exact_mod_cast twoVertexCost_perm23 _ _ _ _

private theorem pairCost_comp_permPairs (u : Fin 4 → E) (t : ℝ) :
    pairCost (u ∘ permPairs) t = pairCost u t := by
  rw [pairCost_eq_integral_twoVertexCost, pairCost_eq_integral_twoVertexCost]
  congr 1 with x
  exact_mod_cast twoVertexCost_permPairs _ _ _ _

/-- **Dihedral `D_4` symmetry reduction.** Every `IsAdmissiblePair u` can be reindexed to an
admissible `4`-tuple `v` with identical `pairCost · 0` satisfying `0 ≤ pairO1 v ≤ pairO2 v`. -/
theorem exists_admissiblePair_wlog {u : Fin 4 → E} (h : IsAdmissiblePair u) :
    ∃ v : Fin 4 → E, IsAdmissiblePair v ∧ pairCost u 0 = pairCost v 0 ∧
      0 ≤ pairO1 v ∧ pairO1 v ≤ pairO2 v := by
  have step1 : ∃ u1 : Fin 4 → E, IsAdmissiblePair u1 ∧ pairCost u 0 = pairCost u1 0 ∧
      0 ≤ pairO1 u1 := by
    rcases le_or_gt 0 (pairO1 u) with ho1 | ho1
    · exact ⟨u, h, rfl, ho1⟩
    · refine ⟨u ∘ perm01, isAdmissiblePair_comp_perm01 h, (pairCost_comp_perm01 u 0).symm, ?_⟩
      unfold pairO1 at ho1 ⊢
      change 0 ≤ (⟪u 1, u 2⟫ - ⟪u 0, u 3⟫ + ⟪u 1, u 3⟫ - ⟪u 0, u 2⟫) / 4
      linarith
  obtain ⟨u1, hu1, hc1, ho1⟩ := step1
  have step2 : ∃ u2 : Fin 4 → E, IsAdmissiblePair u2 ∧ pairCost u 0 = pairCost u2 0 ∧
      0 ≤ pairO1 u2 ∧ 0 ≤ pairO2 u2 := by
    rcases le_or_gt 0 (pairO2 u1) with ho2 | ho2
    · exact ⟨u1, hu1, hc1, ho1, ho2⟩
    · refine ⟨u1 ∘ perm23, isAdmissiblePair_comp_perm23 hu1,
        hc1.trans (pairCost_comp_perm23 u1 0).symm, ?_, ?_⟩
      · unfold pairO1 at ho1 ⊢
        change 0 ≤ (⟪u1 0, u1 3⟫ - ⟪u1 1, u1 2⟫ + ⟪u1 0, u1 2⟫ - ⟪u1 1, u1 3⟫) / 4
        linarith
      · unfold pairO2 at ho2 ⊢
        change 0 ≤ (⟪u1 0, u1 3⟫ - ⟪u1 1, u1 2⟫ - ⟪u1 0, u1 2⟫ + ⟪u1 1, u1 3⟫) / 4
        linarith
  obtain ⟨u2, hu2, hc2, ho1', ho2'⟩ := step2
  rcases le_or_gt (pairO1 u2) (pairO2 u2) with hle | hgt
  · exact ⟨u2, hu2, hc2, ho1', hle⟩
  · have c20 : ⟪u2 2, u2 0⟫ = ⟪u2 0, u2 2⟫ := real_inner_comm _ _
    have c31 : ⟪u2 3, u2 1⟫ = ⟪u2 1, u2 3⟫ := real_inner_comm _ _
    have c21 : ⟪u2 2, u2 1⟫ = ⟪u2 1, u2 2⟫ := real_inner_comm _ _
    have c30 : ⟪u2 3, u2 0⟫ = ⟪u2 0, u2 3⟫ := real_inner_comm _ _
    refine ⟨u2 ∘ permPairs, isAdmissiblePair_comp_permPairs hu2,
      hc2.trans (pairCost_comp_permPairs u2 0).symm, ?_, ?_⟩
    · unfold pairO1; unfold pairO2 at ho2'
      change 0 ≤ (⟪u2 2, u2 0⟫ - ⟪u2 3, u2 1⟫ + ⟪u2 2, u2 1⟫ - ⟪u2 3, u2 0⟫) / 4
      rw [c20, c31, c21, c30]
      linarith
    · unfold pairO1 pairO2 at hgt ⊢
      change (⟪u2 2, u2 0⟫ - ⟪u2 3, u2 1⟫ + ⟪u2 2, u2 1⟫ - ⟪u2 3, u2 0⟫) / 4 ≤
        (⟪u2 2, u2 0⟫ - ⟪u2 3, u2 1⟫ - ⟪u2 2, u2 1⟫ + ⟪u2 3, u2 0⟫) / 4
      rw [c20, c31, c21, c30]
      linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem admissiblePair_root_bounds {u : Fin 4 → E} (h : IsAdmissiblePair u)
    (ho1 : 0 ≤ pairO1 u) (ho12 : pairO1 u ≤ pairO2 u) :
    (94280000 / 100000000 : ℝ) ≤ pairSab u ∧ pairSab u ≤ 1 ∧
    (94280000 / 100000000 : ℝ) ≤ pairScd u ∧ pairScd u ≤ 1 ∧
    (79998000 / 100000000 : ℝ) ≤ pairRb u ∧ pairRb u ≤ 1 ∧
    0 ≤ pairO1 u ∧ pairO1 u ≤ 10001000 / 100000000 ∧
    0 ≤ pairO2 u ∧ pairO2 u ≤ 10001000 / 100000000 ∧
    -(10001000 / 100000000 : ℝ) ≤ pairTau u ∧ pairTau u ≤ 10001000 / 100000000 ∧
    ⟪u 0, u 2⟫ = pairRb u + pairO1 u + pairO2 u + pairTau u ∧
    ⟪u 1, u 3⟫ = pairRb u - pairO1 u - pairO2 u + pairTau u ∧
    ⟪u 0, u 3⟫ = pairRb u + pairO1 u - pairO2 u - pairTau u ∧
    ⟪u 1, u 2⟫ = pairRb u - pairO1 u + pairO2 u - pairTau u ∧
    (79998000 / 100000000 : ℝ) ≤ ⟪u 0, u 2⟫ ∧ ⟪u 0, u 2⟫ ≤ 1 ∧
    (79998000 / 100000000 : ℝ) ≤ ⟪u 1, u 3⟫ ∧ ⟪u 1, u 3⟫ ≤ 1 ∧
    (79998000 / 100000000 : ℝ) ≤ ⟪u 0, u 3⟫ ∧ ⟪u 0, u 3⟫ ≤ 1 ∧
    (79998000 / 100000000 : ℝ) ≤ ⟪u 1, u 2⟫ ∧ ⟪u 1, u 2⟫ ≤ 1 := by
  rcases h with ⟨hu, hab, hcd, hac, had, hbc, hbd, _⟩
  have h1 (i j : Fin 4) : ⟪u i, u j⟫ ≤ 1 :=
    (real_inner_le_norm _ _).trans_eq (by rw [hu i, hu j, mul_one])
  have h01 := h1 0 1; have h23 := h1 2 3
  have h02 := h1 0 2; have h13 := h1 1 3; have h03 := h1 0 3; have h12 := h1 1 2
  dsimp only [pairSab, pairScd, pairRb, pairO1, pairO2, pairTau] at ho1 ho12 ⊢
  refine ⟨by linarith, h01, by linarith, h23, by linarith, by linarith,
    ho1, by linarith, by linarith, by linarith, by linarith, by linarith,
    by ring, by ring, by ring, by ring,
    by linarith, h02, by linarith, h13, by linarith, h03, by linarith, h12⟩

/-! ### Part 3: Zero-threshold Boolean inequalities and Sheppard bounds -/

private theorem twoVertexCost_four_eq :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 =
        2 * (bDiff b0 b1 + bDiff b2 b3) +
        (bDiff b0 b2 + bDiff b1 b3 + bDiff b0 b3 + bDiff b1 b2) +
        2 * (bDiff b0 b1 * bDiff b2 b3) := by decide

private theorem twoVertexCost_le_33 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        3 * (bDiff b0 b1 + bDiff b2 b3) +
        (bDiff b0 b2 + bDiff b1 b3 + bDiff b0 b3 + bDiff b1 b2) := by decide

private theorem twoVertexCost_le_42 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        4 * bDiff b0 b1 + 2 * bDiff b2 b3 +
        (bDiff b0 b2 + bDiff b1 b3 + bDiff b0 b3 + bDiff b1 b2) := by decide

private theorem twoVertexCost_le_24 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        2 * bDiff b0 b1 + 4 * bDiff b2 b3 +
        (bDiff b0 b2 + bDiff b1 b3 + bDiff b0 b3 + bDiff b1 b2) := by decide

private theorem twoVertexCost_le_drop02 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        3 * (bDiff b0 b1 + bDiff b2 b3) +
        2 * bDiff b1 b3 + bDiff b0 b3 + bDiff b1 b2 := by decide

private theorem twoVertexCost_le_drop13 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        3 * (bDiff b0 b1 + bDiff b2 b3) +
        2 * bDiff b0 b2 + bDiff b0 b3 + bDiff b1 b2 := by decide

private theorem twoVertexCost_le_drop03 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        3 * (bDiff b0 b1 + bDiff b2 b3) +
        2 * bDiff b1 b2 + bDiff b0 b2 + bDiff b1 b3 := by decide

private theorem twoVertexCost_le_drop12 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤
        3 * (bDiff b0 b1 + bDiff b2 b3) +
        2 * bDiff b0 b3 + bDiff b0 b2 + bDiff b1 b3 := by decide

private theorem twoVertexCost_le_tree02 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤ 4 * (bDiff b0 b1 + bDiff b2 b3 + bDiff b0 b2) := by decide

private theorem twoVertexCost_le_tree13 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤ 4 * (bDiff b0 b1 + bDiff b2 b3 + bDiff b1 b3) := by decide

private theorem twoVertexCost_le_tree03 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤ 4 * (bDiff b0 b1 + bDiff b2 b3 + bDiff b0 b3) := by decide

private theorem twoVertexCost_le_tree12 :
    ∀ b0 b1 b2 b3 : Bool,
      4 * twoVertexCost b0 b1 b2 b3 ≤ 4 * (bDiff b0 b1 + bDiff b2 b3 + bDiff b1 b2) := by decide

private theorem integral_bDiff_zero {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∫ x, (bDiff (decide (⟪a, x⟫ < 0)) (decide (⟪b, x⟫ < 0)) : ℝ) ∂stdGaussian E =
      arccos ⟪a, b⟫ / π := by
  set S : Set E := {x | (0 : ℝ) ∈ Ι ⟪a, x⟫ ⟪b, x⟫}
  have hSm : MeasurableSet S := measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0
  have hcongr : (fun x : E => (bDiff (decide (⟪a, x⟫ < 0)) (decide (⟪b, x⟫ < 0)) : ℝ)) =
      S.indicator (1 : E → ℝ) := by
    funext x
    rw [bDiff_eq_indicator_uIoc]
    by_cases hm : (0 : ℝ) ∈ Ι ⟪a, x⟫ ⟪b, x⟫ <;>
      simp only [S, mem_ofPred_eq, hm, not_false_eq_true, indicator_of_mem, indicator_of_notMem,
        Pi.one_apply]
  rw [hcongr, integral_indicator_one hSm]
  exact measureReal_stdGaussian_zero_mem_uIoc_eq_arccos ha hb

private theorem integrable_bDiff_zero (a b : E) :
    Integrable (fun x : E => (bDiff (decide (⟪a, x⟫ < 0)) (decide (⟪b, x⟫ < 0)) : ℝ))
      (stdGaussian E) := by
  set S : Set E := {x | (0 : ℝ) ∈ Ι ⟪a, x⟫ ⟪b, x⟫}
  have hSm : MeasurableSet S := measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0
  have hcongr : (fun x : E => (bDiff (decide (⟪a, x⟫ < 0)) (decide (⟪b, x⟫ < 0)) : ℝ)) =
      S.indicator (1 : E → ℝ) := by
    funext x
    rw [bDiff_eq_indicator_uIoc]
    by_cases hm : (0 : ℝ) ∈ Ι ⟪a, x⟫ ⟪b, x⟫ <;>
      simp only [S, mem_ofPred_eq, hm, not_false_eq_true, indicator_of_mem, indicator_of_notMem,
        Pi.one_apply]
  rw [hcongr]
  exact (integrable_const 1).indicator hSm

private theorem integral_bDiff_prod_eq_rect {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1) :
    ∫ x, ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
        bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℕ) : ℝ) ∂stdGaussian E =
      (stdGaussian E).real {x | |⟪(1 / 2 : ℝ) • (u 0 + u 1), x⟫| <
          |⟪(1 / 2 : ℝ) • (u 0 - u 1), x⟫| ∧
        |⟪(1 / 2 : ℝ) • (u 2 + u 3), x⟫| < |⟪(1 / 2 : ℝ) • (u 2 - u 3), x⟫|} := by
  set R : Set E := {x | |⟪(1 / 2 : ℝ) • (u 0 + u 1), x⟫| < |⟪(1 / 2 : ℝ) • (u 0 - u 1), x⟫| ∧
      |⟪(1 / 2 : ℝ) • (u 2 + u 3), x⟫| < |⟪(1 / 2 : ℝ) • (u 2 - u 3), x⟫|}
  have hRm : MeasurableSet R :=
    (measurableSet_lt (by fun_prop : Measurable fun x : E => |⟪(1 / 2 : ℝ) • (u 0 + u 1), x⟫|)
      (by fun_prop : Measurable fun x : E => |⟪(1 / 2 : ℝ) • (u 0 - u 1), x⟫|)).inter
    (measurableSet_lt (by fun_prop : Measurable fun x : E => |⟪(1 / 2 : ℝ) • (u 2 + u 3), x⟫|)
      (by fun_prop : Measurable fun x : E => |⟪(1 / 2 : ℝ) • (u 2 - u 3), x⟫|))
  have hne (i : Fin 4) : ∀ᵐ x ∂stdGaussian E, ⟪u i, x⟫ ≠ 0 :=
    stdGaussian_inner_ne_zero_ae (norm_ne_zero_iff.mp (by rw [hu i]; exact one_ne_zero))
  have hae : (fun x : E => ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
        bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℕ) : ℝ)) =ᵐ[stdGaussian E]
      R.indicator (1 : E → ℝ) := by
    filter_upwards [hne 0, hne 1, hne 2, hne 3] with x h0 h1 h2 h3
    have hpair (i j : Fin 4) (hi : ⟪u i, x⟫ ≠ 0) (hj : ⟪u j, x⟫ ≠ 0) :
        (bDiff (decide (⟪u i, x⟫ < 0)) (decide (⟪u j, x⟫ < 0)) = 1) ↔
          |⟪(1 / 2 : ℝ) • (u i + u j), x⟫| < |⟪(1 / 2 : ℝ) • (u i - u j), x⟫| := by
      simp only [real_inner_smul_left, inner_add_left, inner_sub_left]
      set a := ⟪u i, x⟫; set b := ⟪u j, x⟫
      have hsq : |1 / 2 * (a + b)| < |1 / 2 * (a - b)| ↔
          (1 / 2 * (a + b)) ^ 2 < (1 / 2 * (a - b)) ^ 2 :=
        sq_lt_sq.symm
      rw [hsq]
      rcases lt_or_gt_of_ne hi with ha | ha <;> rcases lt_or_gt_of_ne hj with hb | hb
      · simp only [bDiff, ha, hb, decide_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          zero_ne_one, false_iff]; nlinarith
      · simp only [bDiff, ha, hb.not_gt, decide_true, decide_false, Bool.bne_false, ↓reduceIte,
          true_iff]; nlinarith
      · simp only [bDiff, ha.not_gt, hb, decide_false, decide_true, Bool.false_bne, ↓reduceIte,
          true_iff]; nlinarith
      · simp only [bDiff, ha.not_gt, hb.not_gt, decide_false, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, zero_ne_one, false_iff]; nlinarith
    have hb01 : bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) ≤ 1 := by
      unfold bDiff; split_ifs <;> omega
    have hb23 : bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) ≤ 1 := by
      unfold bDiff; split_ifs <;> omega
    by_cases hm : x ∈ R
    · have e01 := (hpair 0 1 h0 h1).mpr hm.1
      have e23 := (hpair 2 3 h2 h3).mpr hm.2
      simp only [hm, e01, e23, mul_one, Nat.cast_one, indicator_of_mem, Pi.one_apply]
    · have hnot : ¬(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) = 1 ∧
          bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) = 1) := by
        rintro ⟨e01, e23⟩
        exact hm ⟨(hpair 0 1 h0 h1).mp e01, (hpair 2 3 h2 h3).mp e23⟩
      have hprod : bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
          bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) = 0 := by
        interval_cases h01' : bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) <;>
          interval_cases h23' : bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) <;>
          simp_all
      simp only [hm, not_false_eq_true, hprod, Nat.cast_zero, indicator_of_notMem]
  rw [integral_congr_ae hae, integral_indicator_one hRm]

private noncomputable def sixLinear (u : Fin 4 → E) (c01 c23 c02 c13 c03 c12 : ℝ) (x : E) : ℝ :=
  c01 * bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) +
  c23 * bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) +
  c02 * bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0)) +
  c13 * bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) +
  c03 * bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) +
  c12 * bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0))

private theorem integrable_sixLinear (u : Fin 4 → E) (c01 c23 c02 c13 c03 c12 : ℝ) :
    Integrable (sixLinear u c01 c23 c02 c13 c03 c12) (stdGaussian E) := by
  unfold sixLinear
  exact ((((((integrable_bDiff_zero (u 0) (u 1)).const_mul c01).add
    ((integrable_bDiff_zero (u 2) (u 3)).const_mul c23)).add
    ((integrable_bDiff_zero (u 0) (u 2)).const_mul c02)).add
    ((integrable_bDiff_zero (u 1) (u 3)).const_mul c13)).add
    ((integrable_bDiff_zero (u 0) (u 3)).const_mul c03)).add
    ((integrable_bDiff_zero (u 1) (u 2)).const_mul c12)

private theorem integral_sixLinear {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    (c01 c23 c02 c13 c03 c12 : ℝ) :
    ∫ x, sixLinear u c01 c23 c02 c13 c03 c12 x ∂stdGaussian E =
      c01 * (arccos ⟪u 0, u 1⟫ / π) + c23 * (arccos ⟪u 2, u 3⟫ / π) +
      c02 * (arccos ⟪u 0, u 2⟫ / π) + c13 * (arccos ⟪u 1, u 3⟫ / π) +
      c03 * (arccos ⟪u 0, u 3⟫ / π) + c12 * (arccos ⟪u 1, u 2⟫ / π) := by
  have hd (i j : Fin 4) := integrable_bDiff_zero (u i) (u j)
  unfold sixLinear
  have h1 : Integrable (fun x => c01 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))) +
      c23 * ↑(bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)))) (stdGaussian E) :=
    ((hd 0 1).const_mul c01).add ((hd 2 3).const_mul c23)
  have h2 : Integrable (fun x => c01 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))) +
      c23 * ↑(bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))) +
      c02 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0)))) (stdGaussian E) :=
    h1.add ((hd 0 2).const_mul c02)
  have h3 : Integrable (fun x => c01 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))) +
      c23 * ↑(bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))) +
      c02 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0))) +
      c13 * ↑(bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)))) (stdGaussian E) :=
    h2.add ((hd 1 3).const_mul c13)
  have h4 : Integrable (fun x => c01 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))) +
      c23 * ↑(bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))) +
      c02 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0))) +
      c13 * ↑(bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))) +
      c03 * ↑(bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)))) (stdGaussian E) :=
    h3.add ((hd 0 3).const_mul c03)
  rw [integral_add h4 ((hd 1 2).const_mul c12), integral_add h3 ((hd 0 3).const_mul c03),
    integral_add h2 ((hd 1 3).const_mul c13), integral_add h1 ((hd 0 2).const_mul c02),
    integral_add ((hd 0 1).const_mul c01) ((hd 2 3).const_mul c23),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_bDiff_zero (hu 0) (hu 1), integral_bDiff_zero (hu 2) (hu 3),
    integral_bDiff_zero (hu 0) (hu 2), integral_bDiff_zero (hu 1) (hu 3),
    integral_bDiff_zero (hu 0) (hu 3), integral_bDiff_zero (hu 1) (hu 2)]

private theorem pairCost_zero_eq_ch_add_half_rect {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1) :
    pairCost u 0 =
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
      (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) / (4 * π) +
      1 / 2 * (stdGaussian E).real {x | |⟪(1 / 2 : ℝ) • (u 0 + u 1), x⟫| <
          |⟪(1 / 2 : ℝ) • (u 0 - u 1), x⟫| ∧
        |⟪(1 / 2 : ℝ) • (u 2 + u 3), x⟫| < |⟪(1 / 2 : ℝ) • (u 2 - u 3), x⟫|} := by
  have hsum_int := integrable_sixLinear u 2 2 1 1 1 1
  have hprod_int : Integrable (fun x : E =>
      ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
        bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℕ) : ℝ)) (stdGaussian E) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · have hm01 := (integrable_bDiff_zero (u 0) (u 1)).aestronglyMeasurable
      have hm23 := (integrable_bDiff_zero (u 2) (u 3)).aestronglyMeasurable
      exact (hm01.mul hm23).congr (ae_of_all _ fun x => by simp only [Pi.mul_apply, Nat.cast_mul])
    · have h01 : bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) ≤ 1 := by
        unfold bDiff; split_ifs <;> omega
      have h23 : bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) ≤ 1 := by
        unfold bDiff; split_ifs <;> omega
      rw [Real.norm_eq_abs, Nat.abs_cast]
      exact_mod_cast Nat.mul_le_mul h01 h23
  have hpt (x : E) : (4 : ℝ) * (twoVertexCost (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))
        (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℝ) =
      sixLinear u 2 2 1 1 1 1 x +
      2 * ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
        bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℕ) : ℝ) := by
    have hb : (4 : ℝ) * (twoVertexCost (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))
        (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℝ) =
        2 * ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) : ℝ) +
            bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))) +
        ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0)) : ℝ) +
          bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) +
          bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) +
          bDiff (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0))) +
        2 * ((bDiff (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0)) *
          bDiff (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℕ) : ℝ) := by
      exact_mod_cast twoVertexCost_four_eq (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))
        (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))
    unfold sixLinear
    linarith
  have h4 : 4 * pairCost u 0 = ∫ x, 4 * (twoVertexCost (decide (⟪u 0, x⟫ < 0))
      (decide (⟪u 1, x⟫ < 0)) (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0)) : ℝ)
      ∂stdGaussian E := by
    rw [pairCost_eq_integral_twoVertexCost, integral_const_mul]
  rw [funext hpt, integral_add hsum_int (hprod_int.const_mul 2),
    integral_sixLinear hu 2 2 1 1 1 1, integral_const_mul, integral_bDiff_prod_eq_rect hu] at h4
  linarith [show 2 * (arccos ⟪u 0, u 1⟫ / π) + 2 * (arccos ⟪u 2, u 3⟫ / π) =
      4 * ((arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π)) by ring,
    show 1 * (arccos ⟪u 0, u 2⟫ / π) + 1 * (arccos ⟪u 1, u 3⟫ / π) +
      1 * (arccos ⟪u 0, u 3⟫ / π) + 1 * (arccos ⟪u 1, u 2⟫ / π) =
      4 * ((arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ +
        arccos ⟪u 1, u 2⟫) / (4 * π)) by ring]

private theorem pairCost_zero_le_sixLinear {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    (c01 c23 c02 c13 c03 c12 : ℝ)
    (hbool : ∀ b0 b1 b2 b3 : Bool,
      4 * (twoVertexCost b0 b1 b2 b3 : ℝ) ≤
        c01 * bDiff b0 b1 + c23 * bDiff b2 b3 + c02 * bDiff b0 b2 +
        c13 * bDiff b1 b3 + c03 * bDiff b0 b3 + c12 * bDiff b1 b2) :
    pairCost u 0 ≤
      (c01 * arccos ⟪u 0, u 1⟫ + c23 * arccos ⟪u 2, u 3⟫ + c02 * arccos ⟪u 0, u 2⟫ +
       c13 * arccos ⟪u 1, u 3⟫ + c03 * arccos ⟪u 0, u 3⟫ + c12 * arccos ⟪u 1, u 2⟫) /
      (4 * π) := by
  have hint_c := (integrable_twoVertexCost u 0).const_mul 4
  have hrhs := integrable_sixLinear u c01 c23 c02 c13 c03 c12
  have hmono := integral_mono hint_c hrhs fun x =>
    hbool (decide (⟪u 0, x⟫ < 0)) (decide (⟪u 1, x⟫ < 0))
      (decide (⟪u 2, x⟫ < 0)) (decide (⟪u 3, x⟫ < 0))
  rw [integral_const_mul, ← pairCost_eq_integral_twoVertexCost,
    integral_sixLinear hu c01 c23 c02 c13 c03 c12] at hmono
  have hpi : 0 < π := pi_pos
  rw [le_div_iff₀ (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hmono hpi.le
  have hring : (c01 * (arccos ⟪u 0, u 1⟫ / π) + c23 * (arccos ⟪u 2, u 3⟫ / π) +
      c02 * (arccos ⟪u 0, u 2⟫ / π) + c13 * (arccos ⟪u 1, u 3⟫ / π) +
      c03 * (arccos ⟪u 0, u 3⟫ / π) + c12 * (arccos ⟪u 1, u 2⟫ / π)) * π =
      c01 * arccos ⟪u 0, u 1⟫ + c23 * arccos ⟪u 2, u 3⟫ + c02 * arccos ⟪u 0, u 2⟫ +
      c13 * arccos ⟪u 1, u 3⟫ + c03 * arccos ⟪u 0, u 3⟫ + c12 * arccos ⟪u 1, u 2⟫ := by
    field_simp [hpi.ne']
  linarith

theorem pairCost_zero_le_shep_mode {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    {va vb vc0 vc1 vc2 vc3 : ℝ}
    (ha : arccos ⟪u 0, u 1⟫ ≤ va) (hb : arccos ⟪u 2, u 3⟫ ≤ vb)
    (hc0 : arccos ⟪u 0, u 2⟫ ≤ vc0) (hc1 : arccos ⟪u 1, u 3⟫ ≤ vc1)
    (hc2 : arccos ⟪u 0, u 3⟫ ≤ vc2) (hc3 : arccos ⟪u 1, u 2⟫ ≤ vc3) :
    pairCost u 0 ≤ (3 * (va + vb) + (vc0 + vc1 + vc2 + vc3)) / (4 * π) ∧
    pairCost u 0 ≤ (4 * va + 2 * vb + (vc0 + vc1 + vc2 + vc3)) / (4 * π) ∧
    pairCost u 0 ≤ (2 * va + 4 * vb + (vc0 + vc1 + vc2 + vc3)) / (4 * π) ∧
    pairCost u 0 ≤ (3 * (va + vb) + 2 * vc1 + vc2 + vc3) / (4 * π) ∧
    pairCost u 0 ≤ (3 * (va + vb) + 2 * vc0 + vc2 + vc3) / (4 * π) ∧
    pairCost u 0 ≤ (3 * (va + vb) + 2 * vc3 + vc0 + vc1) / (4 * π) ∧
    pairCost u 0 ≤ (3 * (va + vb) + 2 * vc2 + vc0 + vc1) / (4 * π) ∧
    pairCost u 0 ≤ (4 * (va + vb + vc0)) / (4 * π) ∧
    pairCost u 0 ≤ (4 * (va + vb + vc1)) / (4 * π) ∧
    pairCost u 0 ≤ (4 * (va + vb + vc2)) / (4 * π) ∧
    pairCost u 0 ≤ (4 * (va + vb + vc3)) / (4 * π) := by
  have hpi : 0 < 4 * π := by positivity
  have mk {c01 c23 c02 c13 c03 c12 : ℕ}
      (hb_ineq : ∀ b0 b1 b2 b3 : Bool, 4 * twoVertexCost b0 b1 b2 b3 ≤
        c01 * bDiff b0 b1 + c23 * bDiff b2 b3 + c02 * bDiff b0 b2 +
        c13 * bDiff b1 b3 + c03 * bDiff b0 b3 + c12 * bDiff b1 b2) :
      pairCost u 0 ≤
        ((c01 : ℝ) * va + c23 * vb + c02 * vc0 + c13 * vc1 + c03 * vc2 + c12 * vc3) / (4 * π) := by
    refine (pairCost_zero_le_sixLinear hu c01 c23 c02 c13 c03 c12 fun b0 b1 b2 b3 => ?_).trans
      (div_le_div_of_nonneg_right ?_ hpi.le)
    · exact_mod_cast hb_ineq b0 b1 b2 b3
    · gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mk (c01 := 3) (c23 := 3) (c02 := 1) (c13 := 1) (c03 := 1) (c12 := 1)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_33 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 4) (c23 := 2) (c02 := 1) (c13 := 1) (c03 := 1) (c12 := 1)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_42 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 2) (c23 := 4) (c02 := 1) (c13 := 1) (c03 := 1) (c12 := 1)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_24 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 3) (c23 := 3) (c02 := 0) (c13 := 2) (c03 := 1) (c12 := 1)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_drop02 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 3) (c23 := 3) (c02 := 2) (c13 := 0) (c03 := 1) (c12 := 1)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_drop13 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 3) (c23 := 3) (c02 := 1) (c13 := 1) (c03 := 0) (c12 := 2)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_drop03 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 3) (c23 := 3) (c02 := 1) (c13 := 1) (c03 := 2) (c12 := 0)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_drop12 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 4) (c23 := 4) (c02 := 4) (c13 := 0) (c03 := 0) (c12 := 0)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_tree02 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 4) (c23 := 4) (c02 := 0) (c13 := 4) (c03 := 0) (c12 := 0)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_tree13 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 4) (c23 := 4) (c02 := 0) (c13 := 0) (c03 := 4) (c12 := 0)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_tree03 b0 b1 b2 b3]).trans_eq (by ring)
  · refine (mk (c01 := 4) (c23 := 4) (c02 := 0) (c13 := 0) (c03 := 0) (c12 := 4)
      fun b0 b1 b2 b3 => by linarith [twoVertexCost_le_tree12 b0 b1 b2 b3]).trans_eq (by ring)

theorem pairCost_zero_le_hadamard {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    {va vb : ℝ} (ha : arccos ⟪u 0, u 1⟫ ≤ va) (hb : arccos ⟪u 2, u 3⟫ ≤ vb)
    (qc : Cert.QuadI)
    (hc0 : arccos ⟪u 0, u 2⟫ ≤ quadEval qc ⟪u 0, u 2⟫)
    (hc1 : arccos ⟪u 1, u 3⟫ ≤ quadEval qc ⟪u 1, u 3⟫)
    (hc2 : arccos ⟪u 0, u 3⟫ ≤ quadEval qc ⟪u 0, u 3⟫)
    (hc3 : arccos ⟪u 1, u 2⟫ ≤ quadEval qc ⟪u 1, u 2⟫) :
    pairCost u 0 ≤
      (3 * (va + vb) + 4 * (quadEval qc (pairRb u) -
        (qc.c2 : ℝ) / 100000000 * (pairO1 u ^ 2 + pairO2 u ^ 2 + pairTau u ^ 2))) / (4 * π) := by
  refine (pairCost_zero_le_shep_mode hu ha hb hc0 hc1 hc2 hc3).1.trans_eq ?_
  congr 2
  unfold quadEval pairRb pairO1 pairO2 pairTau
  ring

end StarAndPair

/-! ### Part 4: Gaussian moments, cubic correlation bound, and planar conditioned bounds -/

private theorem integral_Ioi_mul_exp_half :
    ∫ x in Ioi (0 : ℝ), x * exp (-2⁻¹ * x ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := ((2⁻¹ : ℝ) : ℂ)) (by norm_num)
  have h' : ((∫ x in Ioi (0 : ℝ), x * exp (-2⁻¹ * x ^ 2) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast at h ⊢
    exact h.trans (by norm_num)
  exact_mod_cast h'

private theorem integral_Ioi_cube_mul_exp_half :
    ∫ x in Ioi (0 : ℝ), x ^ 3 * exp (-2⁻¹ * x ^ 2) = 2 := by
  let F : ℝ → ℝ := fun x => -(x ^ 2 + 2) * exp (-2⁻¹ * x ^ 2)
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (x ^ 3 * exp (-2⁻¹ * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 + 2)) (-2 * x) x := by
      convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x (2 : ℝ))).neg using 1
      ring
    have h2 : HasDerivAt (fun y : ℝ => exp (-2⁻¹ * y ^ 2)) (-x * exp (-2⁻¹ * x ^ 2)) x := by
      convert ((hasDerivAt_pow 2 x).const_mul (-2⁻¹ : ℝ)).exp using 1
      ring
    convert h1.mul h2 using 1
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ 3 * exp (-2⁻¹ * x ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (-1 : ℝ) < 3)).congr_fun (fun x _ => ?_) measurableSet_Ioi
    dsimp only
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
  have hlim : Tendsto F atTop (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (nhds 0) :=
      tendsto_exp_atBot.comp ((tendsto_id).const_mul_atTop_of_neg (by norm_num))
    have h2 := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 2⁻¹) 2
      ).tendsto_zero_of_tendsto h0
    have h_zero_0 := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 2⁻¹) 0
      ).tendsto_zero_of_tendsto h0
    have heq : (fun x : ℝ => -(x ^ (2 : ℝ) * exp (-2⁻¹ * x ^ 2)) -
        2 * (x ^ (0 : ℝ) * exp (-2⁻¹ * x ^ 2))) =ᶠ[atTop] F := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
      rw [rpow_two, rpow_zero]
      dsimp only [F]
      ring
    simpa only [neg_zero, mul_zero, sub_zero] using
      (h2.neg.sub (h_zero_0.const_mul 2)).congr' heq
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hftc]
  dsimp only [F]
  rw [show (-2⁻¹ : ℝ) * 0 ^ 2 = 0 by norm_num, exp_zero]
  norm_num

private theorem integral_abs_pow_gaussianReal_std (k : ℕ) (hk : (-1 : ℝ) < k) {I : ℝ}
    (hI : ∫ x in Ioi (0 : ℝ), x ^ k * exp (-2⁻¹ * x ^ 2) = I) :
    ∫ x, |x| ^ k ∂gaussianReal 0 1 = √(2 / π) * I := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, smul_eq_mul]
  let f : ℝ → ℝ := fun x => (√(2 * π))⁻¹ * exp (-2⁻¹ * x ^ 2) * |x| ^ k
  have hf_int : Integrable f := by
    have hfull : Integrable fun x : ℝ => |x| ^ k * exp (-2⁻¹ * x ^ 2) := by
      refine (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2⁻¹) hk).norm.congr
        (ae_of_all _ fun x => ?_)
      dsimp only
      rw [rpow_natCast, Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le, abs_pow]
    exact (hfull.const_mul (√(2 * π))⁻¹).congr (ae_of_all _ fun x => by dsimp only [f]; ring)
  have heq_f : (fun x => (√(2 * π))⁻¹ * exp (-(x ^ 2) / 2) * |x| ^ k) = f := by
    funext x; dsimp only [f]
    rw [show -(x ^ 2) / 2 = -2⁻¹ * x ^ 2 by ring]
  rw [heq_f, ← integral_add_compl (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))) hf_int,
    compl_Ioi]
  have hneg : ∫ x in Iic (0 : ℝ), f x = ∫ x in Ioi (0 : ℝ), f x := by
    have hcomp := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at hcomp
    rw [← hcomp]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by
      dsimp only [f]; rw [neg_sq, abs_neg]
  have hpos : ∫ x in Ioi (0 : ℝ), f x = (√(2 * π))⁻¹ * I := by
    have hcongr : EqOn f (fun x => (√(2 * π))⁻¹ * (x ^ k * exp (-2⁻¹ * x ^ 2))) (Ioi 0) := by
      intro x hx
      have hx0 : 0 < x := hx
      dsimp only [f]
      rw [abs_of_pos hx0]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, hI]
  rw [hpos, hneg, hpos]
  have hpi : 0 < π := pi_pos
  rw [sqrt_div zero_le_two, sqrt_mul zero_le_two]
  field_simp [sqrt_ne_zero'.mpr hpi, (sqrt_pos.mpr zero_lt_two).ne']
  rw [sq_sqrt zero_le_two]
  ring

private theorem integral_abs_gaussianReal (v : ℝ≥0) :
    ∫ x, |x| ∂gaussianReal 0 v = √(2 / π) * √(v : ℝ) := by
  have hstd : ∫ x, |x| ∂gaussianReal 0 1 = √(2 / π) := by
    have h := integral_abs_pow_gaussianReal_std 1 (by norm_num)
      (by simpa only [pow_one] using integral_Ioi_mul_exp_half)
    simpa only [pow_one, mul_one] using h
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => √(v : ℝ) * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    push_cast
    simp only [sq_sqrt (NNReal.coe_nonneg v)]
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : (fun x : ℝ => |√(v : ℝ) * x|) = fun x => √(v : ℝ) * |x| := by
    funext x; rw [abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  rw [hpt, integral_const_mul, hstd, mul_comm]

private theorem integral_abs_cube_gaussianReal_std :
    ∫ x, |x| ^ 3 ∂gaussianReal 0 1 = 2 * √(2 / π) := by
  rw [integral_abs_pow_gaussianReal_std 3 (by norm_num) integral_Ioi_cube_mul_exp_half, mul_comm]

private theorem integral_abs_cube_gaussianReal (v : ℝ≥0) :
    ∫ x, |x| ^ 3 ∂gaussianReal 0 v = 2 * √(2 / π) * √(v : ℝ) ^ 3 := by
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => √(v : ℝ) * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    push_cast
    simp only [sq_sqrt (NNReal.coe_nonneg v)]
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : (fun x : ℝ => |√(v : ℝ) * x| ^ 3) = fun x => √(v : ℝ) ^ 3 * |x| ^ 3 := by
    funext x; rw [abs_mul, abs_of_nonneg (sqrt_nonneg _), mul_pow]
  rw [hpt, integral_const_mul, integral_abs_cube_gaussianReal_std]
  ring

private theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  simpa only [id_eq, sub_zero] using h

private theorem integrable_sq_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

private theorem integrable_abs_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x|) (gaussianReal 0 v) :=
  ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl).norm

private theorem integrable_abs_cube_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x| ^ 3) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) 3).integrable_norm_pow (by norm_num)
  simpa only [id_eq, Real.norm_eq_abs] using h

private theorem integral_hat_le_sq (c : ℝ) :
    ∫ w, max 0 (|c| - |w|) = c ^ 2 := by
  set a := |c|
  have ha : 0 ≤ a := abs_nonneg c
  have hsupp : (fun w : ℝ => max 0 (a - |w|)) =
      (Ioc (-a) a).indicator fun w => a - |w| := by
    funext w
    by_cases hw : w ∈ Ioc (-a) a
    · rw [indicator_of_mem hw]
      have habs : |w| ≤ a := abs_le.mpr ⟨hw.1.le, hw.2⟩
      exact max_eq_right (by linarith)
    · rw [indicator_of_notMem hw]
      have habs : a ≤ |w| := by
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hw
        rcases hw with hw | hw
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      exact max_eq_left (by linarith)
  have hcont : Continuous fun w : ℝ => a - |w| := by fun_prop
  rw [hsupp, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-a) 0) (hcont.intervalIntegrable 0 a)]
  have hleft : ∫ w in (-a)..0, (a - |w|) = a ^ 2 / 2 := by
    have heq : EqOn (fun w => a - |w|) (fun w => a + w) (uIcc (-a) 0) := by
      intro w hw
      rw [uIcc_of_le (by linarith)] at hw
      dsimp only
      rw [abs_of_nonpos hw.2]; ring
    rw [intervalIntegral.integral_congr heq]
    have hd : ∀ x ∈ uIcc (-a) 0,
        HasDerivAt (fun y => a * y + y ^ 2 / 2) (a + x) x := fun x _ => by
      refine (((hasDerivAt_id x).const_mul a).add
        ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
      ring
    have hint_l : IntervalIntegrable (fun w => a + w) volume (-a) 0 :=
      (continuous_const.add continuous_id).intervalIntegrable (-a) 0
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_l]
    ring
  have hright : ∫ w in (0 : ℝ)..a, (a - |w|) = a ^ 2 / 2 := by
    have heq : EqOn (fun w => a - |w|) (fun w => a - w) (uIcc 0 a) := by
      intro w hw
      rw [uIcc_of_le ha] at hw
      dsimp only
      rw [abs_of_nonneg hw.1]
    rw [intervalIntegral.integral_congr heq]
    have hd : ∀ x ∈ uIcc 0 a,
        HasDerivAt (fun y => a * y - y ^ 2 / 2) (a - x) x := fun x _ => by
      refine (((hasDerivAt_id x).const_mul a).sub
        ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
      ring
    have hint_r : IntervalIntegrable (fun w => a - w) volume 0 a :=
      (continuous_const.sub continuous_id).intervalIntegrable 0 a
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_r]
    ring
  rw [hleft, hright, add_halves, sq_abs]

private theorem integrable_hat (c : ℝ) : Integrable fun w : ℝ => max 0 (|c| - |w|) := by
  set a := |c|
  have hcont : Continuous fun w : ℝ => a - |w| := by fun_prop
  have hint : IntegrableOn (fun w : ℝ => a - |w|) (Icc (-a) a) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  refine ((integrable_indicator_iff measurableSet_Icc).mpr hint).congr (ae_of_all _ fun w => ?_)
  by_cases hw : w ∈ Icc (-a) a
  · rw [indicator_of_mem hw]
    have habs : |w| ≤ a := abs_le.mpr hw
    exact (max_eq_right (by linarith)).symm
  · rw [indicator_of_notMem hw]
    have habs : a ≤ |w| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hw
      rcases hw with hw | hw
      · rw [abs_of_neg (by linarith [abs_nonneg c])]; linarith
      · rw [abs_of_pos (by linarith [abs_nonneg c])]; linarith
    exact (max_eq_left (by linarith)).symm

private theorem integral_abs_add_gaussianReal_le {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    ∫ w, |c + w| ∂gaussianReal 0 v ≤ √(2 / π) * √(v : ℝ) + c ^ 2 / √(2 * π * v) := by
  have hint_pos : Integrable (fun w : ℝ => |c + w|) (gaussianReal 0 v) :=
    ((integrable_const c).add ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl)).norm
  have hint_neg : Integrable (fun w : ℝ => |c - w|) (gaussianReal 0 v) :=
    ((integrable_const c).sub ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl)).norm
  have hsymm : ∫ w, |c - w| ∂gaussianReal 0 v = ∫ w, |c + w| ∂gaussianReal 0 v := by
    conv_lhs => rw [← gaussianReal_zero_map_neg v]
    rw [integral_map (by fun_prop) (by fun_prop)]
    congr with w; ring_nf
  have hpt (w : ℝ) : (|c + w| + |c - w|) / 2 = |w| + max 0 (|c| - |w|) := by
    rcases abs_cases (c + w) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases (c - w) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      rcases abs_cases w with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
      rcases abs_cases c with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
      simp only [max_def] <;> split_ifs <;> linarith
  have hint_hat_g : Integrable (fun w : ℝ => max 0 (|c| - |w|)) (gaussianReal 0 v) := by
    refine Integrable.mono' (integrable_const |c|) (by fun_prop) (ae_of_all _ fun w => ?_)
    have h0 : 0 ≤ max 0 (|c| - |w|) := le_max_left _ _
    have h1 : max 0 (|c| - |w|) ≤ |c| := max_le (abs_nonneg c) (by linarith [abs_nonneg w])
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have havg : ∫ w, |c + w| ∂gaussianReal 0 v =
      ∫ w, |w| ∂gaussianReal 0 v + ∫ w, max 0 (|c| - |w|) ∂gaussianReal 0 v := by
    have h1 : ∫ w, (|c + w| + |c - w|) / 2 ∂gaussianReal 0 v =
        ∫ w, |c + w| ∂gaussianReal 0 v := by
      rw [integral_div, integral_add hint_pos hint_neg, hsymm]
      ring
    rw [← h1, funext hpt, integral_add (integrable_abs_gaussianReal v) hint_hat_g]
  have hhat_le : ∫ w, max 0 (|c| - |w|) ∂gaussianReal 0 v ≤ c ^ 2 / √(2 * π * v) := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [smul_eq_mul]
    have hmono : ∫ w, gaussianPDFReal 0 v w * max 0 (|c| - |w|) ≤
        ∫ w, (√(2 * π * v))⁻¹ * max 0 (|c| - |w|) := by
      refine integral_mono ?_ ((integrable_hat c).const_mul _) fun w =>
        mul_le_mul_of_nonneg_right (gaussianPDFReal_le 0 v w) (le_max_left _ _)
      exact Integrable.mono' ((integrable_hat c).const_mul (√(2 * π * v))⁻¹) (by fun_prop)
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
            abs_of_nonneg (le_max_left _ _)]
          exact mul_le_mul_of_nonneg_right (gaussianPDFReal_le 0 v w) (le_max_left _ _))
    rw [integral_const_mul, integral_hat_le_sq] at hmono
    exact hmono.trans_eq (inv_mul_eq_div _ _)
  rw [havg, integral_abs_gaussianReal]
  linarith

/-- Convex cubic correlation majorant on `[0, 1]`. -/
@[expose] noncomputable def hCub (r : ℝ) : ℝ :=
  r + 8 / (3 * π) * (1 - r) * (1 - r + r ^ 2 / 2)

section PlanarAndMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem orth_decomp {w₁ w₂ : E}
    (hdet : 0 < ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) :
    0 < ‖w₁‖ ^ 2 ∧ ‖w₁‖₊ ^ 2 ≠ 0 ∧
    ∃ w_perp : E, ⟪w₁, w_perp⟫ = 0 ∧
      ‖w_perp‖ ^ 2 = (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) / ‖w₁‖ ^ 2 ∧
      ‖w_perp‖₊ ^ 2 ≠ 0 ∧
      ∀ x : E, ⟪w₂, x⟫ = (⟪w₁, w₂⟫ / ‖w₁‖ ^ 2) * ⟪w₁, x⟫ + ⟪w_perp, x⟫ := by
  have hK00 : 0 < ‖w₁‖ ^ 2 := by
    by_contra h
    have hk0 : ‖w₁‖ ^ 2 = 0 := le_antisymm (not_lt.mp h) (sq_nonneg _)
    rw [hk0, zero_mul, zero_sub] at hdet
    linarith [sq_nonneg ⟪w₁, w₂⟫]
  have hw1_ne : ‖w₁‖ ≠ 0 := fun h => by simp only [h, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, lt_self_iff_false] at hK00
  have hv1_ne : ‖w₁‖₊ ^ 2 ≠ 0 := fun h => by
    have hc : ((‖w₁‖₊ ^ 2 : ℝ≥0) : ℝ) = 0 := by exact_mod_cast h
    rw [NNReal.coe_pow, coe_nnNorm] at hc; linarith
  let α := ⟪w₁, w₂⟫ / ‖w₁‖ ^ 2
  let w_perp := w₂ - α • w₁
  have horth : ⟪w₁, w_perp⟫ = 0 := by
    simp only [w_perp, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, α]
    field_simp [hw1_ne]; ring
  have hw_sq : ‖w_perp‖ ^ 2 = (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) / ‖w₁‖ ^ 2 := by
    dsimp only [w_perp, α]
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm w₁ w₂]
    field_simp [hw1_ne]; ring
  have hv2_ne : ‖w_perp‖₊ ^ 2 ≠ 0 := by
    have hv2_pos : 0 < ‖w_perp‖ ^ 2 := hw_sq ▸ div_pos hdet hK00
    intro h
    have hc : ((‖w_perp‖₊ ^ 2 : ℝ≥0) : ℝ) = 0 := by exact_mod_cast h
    rw [NNReal.coe_pow, coe_nnNorm] at hc; linarith
  refine ⟨hK00, hv1_ne, w_perp, horth, hw_sq, hv2_ne, fun x => ?_⟩
  simp only [w_perp, α, inner_sub_left, real_inner_smul_left]
  ring

private theorem integrable_abs_mul_abs_inner (w₁ w₂ : E) :
    Integrable (fun x : E => |⟪w₁, x⟫| * |⟪w₂, x⟫|) (stdGaussian E) := by
  have hm1 : Integrable (fun x : E => ⟪w₁, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w₁) ▸
      integrable_sq_gaussianReal (‖w₁‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hm2 : Integrable (fun x : E => ⟪w₂, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w₂) ▸
      integrable_sq_gaussianReal (‖w₂‖₊ ^ 2)).comp_measurable (by fun_prop)
  refine Integrable.mono' ((hm1.add hm2).div_const 2) (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change |⟪w₁, x⟫| * |⟪w₂, x⟫| ≤ (⟪w₁, x⟫ ^ 2 + ⟪w₂, x⟫ ^ 2) / 2
  nlinarith [sq_nonneg (|⟪w₁, x⟫| - |⟪w₂, x⟫|), sq_abs ⟪w₁, x⟫, sq_abs ⟪w₂, x⟫]

private theorem integral_sq_inner_stdGaussian (w : E) :
    ∫ x, ⟪w, x⟫ ^ 2 ∂stdGaussian E = ‖w‖ ^ 2 := by
  have h := integral_map (μ := stdGaussian E) (φ := fun x : E => ⟪w, x⟫)
    (by fun_prop) (f := fun z : ℝ => z ^ 2) (by fun_prop)
  rw [stdGaussian_map_inner, integral_sq_gaussianReal, NNReal.coe_pow, coe_nnNorm] at h
  exact h.symm

private theorem integral_abs_mul_abs_le_half_sum (w₁ w₂ : E) :
    ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E ≤ (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) / 2 := by
  have hm1 : Integrable (fun x : E => ⟪w₁, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w₁) ▸
      integrable_sq_gaussianReal (‖w₁‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hm2 : Integrable (fun x : E => ⟪w₂, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w₂) ▸
      integrable_sq_gaussianReal (‖w₂‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hmono : ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E ≤
      ∫ x, (⟪w₁, x⟫ ^ 2 + ⟪w₂, x⟫ ^ 2) / 2 ∂stdGaussian E :=
    integral_mono (integrable_abs_mul_abs_inner w₁ w₂) ((hm1.add hm2).div_const 2) fun x => by
      nlinarith [sq_nonneg (|⟪w₁, x⟫| - |⟪w₂, x⟫|), sq_abs ⟪w₁, x⟫, sq_abs ⟪w₂, x⟫]
  rw [integral_div, integral_add hm1 hm2, integral_sq_inner_stdGaussian,
    integral_sq_inner_stdGaussian] at hmono
  exact hmono

theorem integral_abs_mul_abs_le_sqrt_prod (w₁ w₂ : E) :
    ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E ≤ √(‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) := by
  by_cases hw1 : ‖w₁‖ = 0
  · rw [norm_eq_zero.mp hw1]; simp only [inner_zero_left, abs_zero, zero_mul, integral_zero,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sqrt_zero, le_refl]
  · by_cases hw2 : ‖w₂‖ = 0
    · rw [norm_eq_zero.mp hw2]; simp only [inner_zero_left, abs_zero, mul_zero, integral_zero,
        norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sqrt_zero, le_refl]
    · have hp1 : 0 < ‖w₁‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw1)
      have hp2 : 0 < ‖w₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw2)
      set t := √(‖w₂‖ / ‖w₁‖)
      have ht : 0 < t := sqrt_pos.mpr (div_pos hp2 hp1)
      have htsq : t ^ 2 = ‖w₂‖ / ‖w₁‖ := sq_sqrt (div_nonneg hp2.le hp1.le)
      have hscale : (fun x : E => |⟪w₁, x⟫| * |⟪w₂, x⟫|) =
          fun x => |⟪t • w₁, x⟫| * |⟪t⁻¹ • w₂, x⟫| := by
        funext x
        simp only [real_inner_smul_left, abs_mul, abs_of_pos ht, abs_of_pos (inv_pos.mpr ht)]
        field_simp [ht.ne']
      rw [hscale]
      refine (integral_abs_mul_abs_le_half_sum (t • w₁) (t⁻¹ • w₂)).trans_eq ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
        abs_of_pos (inv_pos.mpr ht), mul_pow, mul_pow, inv_pow, htsq,
        sqrt_mul (sq_nonneg _), sqrt_sq hp1.le, sqrt_sq hp2.le]
      field_simp [hp1.ne', hp2.ne']
      ring

theorem integral_abs_mul_abs_le_div_sqrt {w₁ w₂ : E}
    (hdet : 0 < ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) :
    ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E ≤
      2 / π * (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) / √(‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) := by
  obtain ⟨hK00_pos, _, w_perp, horth, hw_perp_sq, hv2_ne, hpt_eq⟩ := orth_decomp hdet
  set K00 := ‖w₁‖ ^ 2
  set K11 := ‖w₂‖ ^ 2
  set K01 := ⟪w₁, w₂⟫
  set detK := K00 * K11 - K01 ^ 2
  let α := K01 / K00
  have hprod_law := stdGaussian_map_inner_prod (E := E) horth
  let φ : ℝ × ℝ → ℝ := fun p => |p.1| * |α * p.1 + p.2|
  have hφ_int :
      Integrable φ ((gaussianReal 0 (‖w₁‖₊ ^ 2)).prod (gaussianReal 0 (‖w_perp‖₊ ^ 2))) := by
    have hpull : Integrable (φ ∘ fun x : E => (⟪w₁, x⟫, ⟪w_perp, x⟫)) (stdGaussian E) := by
      refine (integrable_abs_mul_abs_inner w₁ w₂).congr (ae_of_all _ fun x => ?_)
      simp only [Function.comp_apply, φ, α, K01, K00, hpt_eq x]
    rwa [← hprod_law, integrable_map_measure (by fun_prop : Continuous φ).aestronglyMeasurable
      (by fun_prop)]
  have hexp : ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E =
      ∫ p, φ p ∂(gaussianReal 0 (‖w₁‖₊ ^ 2)).prod (gaussianReal 0 (‖w_perp‖₊ ^ 2)) := by
    rw [← hprod_law, integral_map (by fun_prop) (by fun_prop : Continuous φ).aestronglyMeasurable]
    congr with x; simp only [φ, α, K01, K00, hpt_eq x]
  rw [hexp, integral_prod _ hφ_int]
  have hslice (z : ℝ) : ∫ w, |z| * |α * z + w| ∂gaussianReal 0 (‖w_perp‖₊ ^ 2) ≤
      √(2 / π) * √(‖w_perp‖ ^ 2) * |z| + α ^ 2 / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3 := by
    rw [integral_const_mul]
    have h1 := integral_abs_add_gaussianReal_le hv2_ne (α * z)
    have hcoe : ((‖w_perp‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖w_perp‖ ^ 2 := by rw [NNReal.coe_pow, coe_nnNorm]
    rw [hcoe] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 (abs_nonneg z)
    have hring : |z| * (√(2 / π) * √(‖w_perp‖ ^ 2) + (α * z) ^ 2 / √(2 * π * ‖w_perp‖ ^ 2)) =
        √(2 / π) * √(‖w_perp‖ ^ 2) * |z| + α ^ 2 / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3 := by
      have hz2 : z ^ 2 * |z| = |z| ^ 3 := by rw [← sq_abs z]; ring
      calc |z| * (√(2 / π) * √(‖w_perp‖ ^ 2) + (α * z) ^ 2 / √(2 * π * ‖w_perp‖ ^ 2))
          = √(2 / π) * √(‖w_perp‖ ^ 2) * |z| +
              α ^ 2 / √(2 * π * ‖w_perp‖ ^ 2) * (z ^ 2 * |z|) := by ring
        _ = _ := by rw [hz2]
    linarith
  have hint_rhs : Integrable (fun z : ℝ =>
      √(2 / π) * √(‖w_perp‖ ^ 2) * |z| + α ^ 2 / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3)
      (gaussianReal 0 (‖w₁‖₊ ^ 2)) :=
    ((integrable_abs_gaussianReal _).const_mul _).add
      ((integrable_abs_cube_gaussianReal _).const_mul _)
  have hmono := integral_mono hφ_int.integral_prod_left hint_rhs hslice
  rw [integral_add ((integrable_abs_gaussianReal _).const_mul _)
      ((integrable_abs_cube_gaussianReal _).const_mul _),
    integral_const_mul, integral_const_mul, integral_abs_gaussianReal,
    integral_abs_cube_gaussianReal] at hmono
  have hc1 : ((‖w₁‖₊ ^ 2 : ℝ≥0) : ℝ) = K00 := by rw [NNReal.coe_pow, coe_nnNorm]
  rw [hc1, hw_perp_sq] at hmono
  refine hmono.trans_eq ?_
  have hpi : 0 < π := pi_pos
  have hsK : 0 < √K00 := sqrt_pos.mpr hK00_pos
  have hsD : 0 < √detK := sqrt_pos.mpr hdet
  have hsq_div : √(detK / K00) = √detK / √K00 := sqrt_div hdet.le _
  have hsq_2pi : √(2 * π * (detK / K00)) = √2 * √π * √detK / √K00 := by
    rw [sqrt_mul (by positivity), sqrt_mul zero_le_two, hsq_div, mul_div_assoc]
  rw [hsq_div, hsq_2pi, sqrt_div zero_le_two]
  dsimp only [α]
  have hs2 : 0 < √2 := sqrt_pos.mpr zero_lt_two
  have hspi : 0 < √π := sqrt_pos.mpr hpi
  field_simp [hsK.ne', hsD.ne', hs2.ne', hspi.ne', hK00_pos.ne', hpi.ne']
  rw [show √K00 ^ 4 = (√K00 ^ 2) ^ 2 by ring, sq_sqrt zero_le_two, sq_sqrt hpi.le,
    sq_sqrt hK00_pos.le, sq_sqrt hdet.le]
  dsimp only [detK]; ring

private theorem integral_parab_cap {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, max 0 (c ^ 2 - x ^ 2) = 4 / 3 * c ^ 3 := by
  have hsupp : (fun x : ℝ => max 0 (c ^ 2 - x ^ 2)) =
      (Ioc (-c) c).indicator fun x => c ^ 2 - x ^ 2 := by
    funext x
    by_cases hx : x ∈ Ioc (-c) c
    · rw [indicator_of_mem hx]
      have hsq : x ^ 2 ≤ c ^ 2 := by nlinarith [hx.1, hx.2]
      exact max_eq_right (by linarith)
    · rw [indicator_of_notMem hx]
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
      have hsq : c ^ 2 ≤ x ^ 2 := by rcases hx with hx | hx <;> nlinarith
      exact max_eq_left (by linarith)
  have hcont : Continuous fun x : ℝ => c ^ 2 - x ^ 2 := by fun_prop
  rw [hsupp, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hd : ∀ x ∈ uIcc (-c) c,
      HasDerivAt (fun y => c ^ 2 * y - y ^ 3 / 3) (c ^ 2 - x ^ 2) x := fun x _ => by
    refine (((hasDerivAt_id x).const_mul (c ^ 2)).sub
      ((hasDerivAt_pow 3 x).div_const 3)).congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable (-c) c)]
  ring

private theorem integrable_parab_cap (c : ℝ) : Integrable fun x : ℝ => max 0 (c ^ 2 - x ^ 2) := by
  have hcont : Continuous fun x : ℝ => c ^ 2 - x ^ 2 := by fun_prop
  have hint : IntegrableOn (fun x : ℝ => c ^ 2 - x ^ 2) (Icc (-|c|) |c|) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  refine ((integrable_indicator_iff measurableSet_Icc).mpr hint).congr (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ Icc (-|c|) |c|
  · rw [indicator_of_mem hx]
    have hsq : x ^ 2 ≤ c ^ 2 := by nlinarith [hx.1, hx.2, sq_abs c]
    exact (max_eq_right (by linarith)).symm
  · rw [indicator_of_notMem hx]
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    have hsq : c ^ 2 ≤ x ^ 2 := by
      rcases hx with hx | hx <;> nlinarith [abs_nonneg c, sq_abs c]
    exact (max_eq_left (by linarith)).symm

private theorem integral_abs_mul_abs_unit_le_hCub {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1)
    (hρ0 : 0 ≤ ⟪e₁, e₂⟫) :
    ∫ x, |⟪e₁, x⟫| * |⟪e₂, x⟫| ∂stdGaussian E ≤ hCub ⟪e₁, e₂⟫ := by
  set ρ := ⟪e₁, e₂⟫
  have hρ1 : ρ ≤ 1 := (real_inner_le_norm _ _).trans_eq (by rw [h1, h2, mul_one])
  rcases eq_or_lt_of_le hρ1 with hρ_eq | hρ_lt
  · have hdiff : ‖e₁ - e₂‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, h1, h2]; dsimp only [ρ] at hρ_eq; linarith
    have heq : e₁ = e₂ := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff))
    rw [heq]
    have hsq : (fun x : E => |⟪e₂, x⟫| * |⟪e₂, x⟫|) = fun x => ⟪e₂, x⟫ ^ 2 := by
      funext x; rw [← sq, sq_abs]
    rw [hsq, integral_sq_inner_stdGaussian, h2, hρ_eq]
    unfold hCub; norm_num
  · let s_v := (1 / 2 : ℝ) • (e₁ + e₂)
    let d_v := (1 / 2 : ℝ) • (e₁ - e₂)
    have horth : ⟪s_v, d_v⟫ = 0 := by
      simp only [s_v, d_v, real_inner_smul_left, real_inner_smul_right, inner_add_left,
        inner_sub_right, real_inner_self_eq_norm_sq, h1, h2, real_inner_comm e₂ e₁]
      ring
    have hs_sq : ‖s_v‖ ^ 2 = (1 + ρ) / 2 := by
      dsimp only [s_v, ρ]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, h1, h2]
      ring
    have hd_sq : ‖d_v‖ ^ 2 = (1 - ρ) / 2 := by
      dsimp only [d_v, ρ]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, h1, h2]
      ring
    have hs_pos : 0 < ‖s_v‖ := by
      have : 0 < ‖s_v‖ ^ 2 := hs_sq ▸ by linarith
      nlinarith [norm_nonneg s_v]
    have hd_pos : 0 < ‖d_v‖ := by
      have : 0 < ‖d_v‖ ^ 2 := hd_sq ▸ by linarith
      nlinarith [norm_nonneg d_v]
    let u_s := ‖s_v‖⁻¹ • s_v
    let u_d := ‖d_v‖⁻¹ • d_v
    have hus_n : ‖u_s‖₊ ^ 2 = 1 := by
      ext; push_cast
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs_pos.ne', one_pow]
    have hud_n : ‖u_d‖₊ ^ 2 = 1 := by
      ext; push_cast
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd_pos.ne', one_pow]
    have husd : ⟪u_s, u_d⟫ = 0 := by
      simp only [u_s, u_d, real_inner_smul_left, real_inner_smul_right, horth, mul_zero]
    have hpt (x : E) : |⟪e₁, x⟫| * |⟪e₂, x⟫| =
        |(1 + ρ) / 2 * ⟪u_s, x⟫ ^ 2 - (1 - ρ) / 2 * ⟪u_d, x⟫ ^ 2| := by
      have hsx : ⟪s_v, x⟫ = ‖s_v‖ * ⟪u_s, x⟫ := by
        simp only [u_s, real_inner_smul_left]; field_simp [hs_pos.ne']
      have hdx : ⟪d_v, x⟫ = ‖d_v‖ * ⟪u_d, x⟫ := by
        simp only [u_d, real_inner_smul_left]; field_simp [hd_pos.ne']
      have hprod_id : ⟪e₁, x⟫ * ⟪e₂, x⟫ = ⟪s_v, x⟫ ^ 2 - ⟪d_v, x⟫ ^ 2 := by
        simp only [s_v, d_v, real_inner_smul_left, inner_add_left, inner_sub_left]; ring
      rw [← abs_mul, hprod_id, hsx, hdx, mul_pow, mul_pow, hs_sq, hd_sq]
    let a := (1 + ρ) / 2
    let b := (1 - ρ) / 2
    have ha_pos : 0 < a := by dsimp only [a]; linarith
    have hb_pos : 0 < b := by dsimp only [b]; linarith
    let ψ : ℝ × ℝ → ℝ := fun p => |a * p.1 ^ 2 - b * p.2 ^ 2|
    have hlaw : (stdGaussian E).map (fun x => (⟪u_s, x⟫, ⟪u_d, x⟫)) =
        (gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [stdGaussian_map_inner_prod (E := E) husd, hus_n, hud_n]
    have hψ_int : Integrable ψ ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have hpull : Integrable (ψ ∘ fun x : E => (⟪u_s, x⟫, ⟪u_d, x⟫)) (stdGaussian E) :=
        (integrable_abs_mul_abs_inner e₁ e₂).congr (ae_of_all _ fun x => hpt x)
      rwa [← hlaw, integrable_map_measure (by fun_prop : Continuous ψ).aestronglyMeasurable
        (by fun_prop)]
    have hexp : ∫ x, |⟪e₁, x⟫| * |⟪e₂, x⟫| ∂stdGaussian E =
        ∫ p, ψ p ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [← hlaw, integral_map (by fun_prop) (by fun_prop : Continuous ψ).aestronglyMeasurable]
      congr with x; exact hpt x
    rw [hexp, integral_prod _ hψ_int]
    set r_ba := √(b / a)
    have hr_ba_nn : 0 ≤ r_ba := sqrt_nonneg _
    have hr_ba_sq : r_ba ^ 2 = b / a := sq_sqrt (div_nonneg hb_pos.le ha_pos.le)
    have hswap : ∫ y, (∫ z, ψ (y, z) ∂gaussianReal 0 1) ∂gaussianReal 0 1 =
        ∫ z, (∫ y, ψ (y, z) ∂gaussianReal 0 1) ∂gaussianReal 0 1 :=
      integral_integral_swap hψ_int
    rw [hswap]
    have hinner (z : ℝ) : ∫ y, ψ (y, z) ∂gaussianReal 0 1 ≤
        a - b * z ^ 2 + 2 * a * (√(2 * π))⁻¹ * (4 / 3 * (r_ba * |z|) ^ 3) := by
      set c := r_ba * |z|
      have hc_nn : 0 ≤ c := mul_nonneg hr_ba_nn (abs_nonneg z)
      have hc_sq : a * c ^ 2 = b * z ^ 2 := by
        dsimp only [c]; rw [mul_pow, hr_ba_sq, sq_abs]; field_simp [ha_pos.ne']
      have hpt_y (y : ℝ) : ψ (y, z) = a * y ^ 2 - b * z ^ 2 + 2 * a * max 0 (c ^ 2 - y ^ 2) := by
        dsimp only [ψ]
        rw [← hc_sq]
        rcases le_or_gt (c ^ 2) (y ^ 2) with hcy | hcy
        · rw [abs_of_nonneg (by nlinarith), max_eq_left (by linarith)]; ring
        · rw [abs_of_neg (by nlinarith), max_eq_right (by linarith)]; ring
      have hcap_g : Integrable (fun y : ℝ => max 0 (c ^ 2 - y ^ 2)) (gaussianReal 0 1) := by
        refine Integrable.mono' (integrable_const (c ^ 2)) (by fun_prop) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        exact max_le (sq_nonneg c) (by linarith [sq_nonneg y])
      have hlin_g : Integrable (fun y : ℝ => a * y ^ 2 - b * z ^ 2) (gaussianReal 0 1) :=
        ((integrable_sq_gaussianReal 1).const_mul a).sub (integrable_const _)
      rw [funext hpt_y, integral_add hlin_g (hcap_g.const_mul (2 * a)),
        integral_sub ((integrable_sq_gaussianReal 1).const_mul a) (integrable_const _),
        integral_const_mul, integral_sq_gaussianReal, NNReal.coe_one, mul_one,
        integral_const, probReal_univ, one_smul, integral_const_mul]
      have hcap_le : ∫ y, max 0 (c ^ 2 - y ^ 2) ∂gaussianReal 0 1 ≤
          (√(2 * π))⁻¹ * (4 / 3 * c ^ 3) := by
        rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
        simp only [smul_eq_mul]
        have hmono : ∫ y, gaussianPDFReal 0 1 y * max 0 (c ^ 2 - y ^ 2) ≤
            ∫ y, (√(2 * π * (1 : ℝ≥0)))⁻¹ * max 0 (c ^ 2 - y ^ 2) := by
          refine integral_mono ?_ ((integrable_parab_cap c).const_mul _) fun y =>
            mul_le_mul_of_nonneg_right (gaussianPDFReal_le 0 1 y) (le_max_left _ _)
          exact Integrable.mono' ((integrable_parab_cap c).const_mul _) (by fun_prop)
            (ae_of_all _ fun y => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
                abs_of_nonneg (le_max_left _ _)]
              exact mul_le_mul_of_nonneg_right (gaussianPDFReal_le 0 1 y) (le_max_left _ _))
        rw [integral_const_mul, integral_parab_cap hc_nn] at hmono
        simpa only [NNReal.coe_one, mul_one] using hmono
      linarith [mul_le_mul_of_nonneg_left hcap_le (by positivity : 0 ≤ 2 * a)]
    have hsub_int : Integrable (fun z : ℝ => a - b * z ^ 2) (gaussianReal 0 1) :=
      (integrable_const a).sub ((integrable_sq_gaussianReal 1).const_mul b)
    have hrew : (fun z : ℝ => a - b * z ^ 2 +
          2 * a * (√(2 * π))⁻¹ * (4 / 3 * (r_ba * |z|) ^ 3)) =
        fun z => (a - b * z ^ 2) +
          (2 * a * (√(2 * π))⁻¹ * (4 / 3 * r_ba ^ 3)) * |z| ^ 3 := by
      funext z; ring
    have hint_rhs : Integrable (fun z : ℝ =>
        a - b * z ^ 2 + 2 * a * (√(2 * π))⁻¹ * (4 / 3 * (r_ba * |z|) ^ 3))
        (gaussianReal 0 1) := by
      rw [hrew]
      exact hsub_int.add ((integrable_abs_cube_gaussianReal 1).const_mul _)
    have hmono := integral_mono hψ_int.integral_prod_right hint_rhs hinner
    rw [hrew, integral_add hsub_int ((integrable_abs_cube_gaussianReal 1).const_mul _),
      integral_sub (integrable_const a) ((integrable_sq_gaussianReal 1).const_mul b),
      integral_const, probReal_univ, one_smul, integral_const_mul, integral_sq_gaussianReal,
      NNReal.coe_one, mul_one, integral_const_mul, integral_abs_cube_gaussianReal_std] at hmono
    refine hmono.trans ?_
    have hpi : 0 < π := pi_pos
    have hs2 : 0 < √2 := sqrt_pos.mpr zero_lt_two
    have hspi : 0 < √π := sqrt_pos.mpr hpi
    have hr3 : a * r_ba ^ 3 = b * r_ba := by
      rw [show r_ba ^ 3 = r_ba ^ 2 * r_ba by ring, hr_ba_sq]; field_simp [ha_pos.ne']
    have hsimp : a - b + 2 * a * (√(2 * π))⁻¹ * (4 / 3 * r_ba ^ 3) * (2 * √(2 / π)) =
        ρ + 8 / (3 * π) * (1 - ρ) * r_ba := by
      rw [sqrt_mul zero_le_two, sqrt_div zero_le_two]
      have h1 : 2 * a * (4 / 3 * r_ba ^ 3) = 8 / 3 * (a * r_ba ^ 3) := by ring
      calc a - b + 2 * a * (√2 * √π)⁻¹ * (4 / 3 * r_ba ^ 3) * (2 * (√2 / √π))
          = (a - b) + (2 * a * (4 / 3 * r_ba ^ 3)) * ((√2 * √π)⁻¹ * (2 * (√2 / √π))) := by ring
        _ = ρ + (8 / 3 * (b * r_ba)) * (2 / π) := by
            rw [h1, hr3]
            congr 1
            · dsimp only [a, b]; ring
            · congr 1
              field_simp [hs2.ne', hspi.ne', hpi.ne']
              exact (sq_sqrt hpi.le).symm
        _ = ρ + 8 / (3 * π) * (1 - ρ) * r_ba := by dsimp only [b]; ring
    rw [hsimp]
    unfold hCub
    have hr_le : r_ba ≤ 1 - ρ + ρ ^ 2 / 2 := by
      have hpoly : b / a ≤ (1 - ρ + ρ ^ 2 / 2) ^ 2 := by
        rw [div_le_iff₀ ha_pos]
        dsimp only [a, b]
        have hid : (1 - ρ + ρ ^ 2 / 2) ^ 2 * ((1 + ρ) / 2) - (1 - ρ) / 2 =
            ρ ^ 3 / 8 * ((ρ - 3 / 2) ^ 2 + 7 / 4) := by ring
        have hnn : 0 ≤ ρ ^ 3 / 8 * ((ρ - 3 / 2) ^ 2 + 7 / 4) := by positivity
        linarith
      have hpoly_nn : 0 ≤ 1 - ρ + ρ ^ 2 / 2 := by linarith [sq_nonneg ρ]
      exact (sqrt_le_iff.mpr ⟨hpoly_nn, hpoly⟩)
    gcongr

private theorem hCub_le_max {r0 r1 ρ : ℝ} (h0 : r0 ≤ ρ) (h1 : ρ ≤ r1) (hr1 : r1 ≤ 1) :
    hCub ρ ≤ max (hCub r0) (hCub r1) := by
  rcases eq_or_lt_of_le (h0.trans h1) with heq | hlt
  · have : ρ = r0 := by linarith
    subst this; exact le_max_left _ _
  · have hid : (r1 - r0) * hCub ρ - ((r1 - ρ) * hCub r0 + (ρ - r0) * hCub r1) =
        -(4 / (3 * π)) * (r1 - r0) * (ρ - r0) * (r1 - ρ) * (3 - (r0 + r1 + ρ)) := by
      unfold hCub; ring
    have hpi : 0 < π := pi_pos
    have hnp : -(4 / (3 * π)) * (r1 - r0) * (ρ - r0) * (r1 - ρ) * (3 - (r0 + r1 + ρ)) ≤ 0 := by
      have hp : 0 ≤ (4 / (3 * π)) * (r1 - r0) * (ρ - r0) * (r1 - ρ) * (3 - (r0 + r1 + ρ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (by linarith)) (by linarith)) (by linarith)
      linarith
    have hconv : (r1 - r0) * hCub ρ ≤ (r1 - ρ) * hCub r0 + (ρ - r0) * hCub r1 := by linarith
    have hm1 : (r1 - ρ) * hCub r0 ≤ (r1 - ρ) * max (hCub r0) (hCub r1) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have hm2 : (ρ - r0) * hCub r1 ≤ (ρ - r0) * max (hCub r0) (hCub r1) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    have htot : (r1 - r0) * hCub ρ ≤ (r1 - r0) * max (hCub r0) (hCub r1) := by linarith
    exact le_of_mul_le_mul_left htot (by linarith)

theorem integral_abs_mul_abs_le_cubic_corr {w₁ w₂ : E} {r0 r1 : ℝ}
    (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1) (hr1 : r1 ≤ 1)
    (hKK : 0 < ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2)
    (hlo : r0 ^ 2 * (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) ≤ ⟪w₁, w₂⟫ ^ 2)
    (hhi : ⟪w₁, w₂⟫ ^ 2 ≤ r1 ^ 2 * (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2)) :
    ∫ x, |⟪w₁, x⟫| * |⟪w₂, x⟫| ∂stdGaussian E ≤
      √(‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) * max (hCub r0) (hCub r1) := by
  have hw1 : 0 < ‖w₁‖ := by
    by_contra h; have h0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hKK; norm_num at hKK
  have hw2 : 0 < ‖w₂‖ := by
    by_contra h; have h0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hKK; norm_num at hKK
  let e₁ := ‖w₁‖⁻¹ • w₁
  let sgn : ℝ := if 0 ≤ ⟪w₁, w₂⟫ then 1 else -1
  have hsgn_sq : sgn ^ 2 = 1 := by dsimp only [sgn]; split_ifs <;> norm_num
  have hsgn_abs : |sgn| = 1 := by dsimp only [sgn]; split_ifs <;> norm_num
  let e₂ := (sgn * ‖w₂‖⁻¹) • w₂
  have he1 : ‖e₁‖ = 1 := by
    dsimp only [e₁]; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw1.ne']
  have he2 : ‖e₂‖ = 1 := by
    dsimp only [e₂]; rw [norm_smul, Real.norm_eq_abs, abs_mul, hsgn_abs, one_mul,
      abs_inv, abs_of_pos hw2, inv_mul_cancel₀ hw2.ne']
  have hρ_eq : ⟪e₁, e₂⟫ = |⟪w₁, w₂⟫| / (‖w₁‖ * ‖w₂‖) := by
    dsimp only [e₁, e₂, sgn]
    rw [real_inner_smul_left, real_inner_smul_right]
    split_ifs with h
    · rw [abs_of_nonneg h]; field_simp [hw1.ne', hw2.ne']
    · rw [abs_of_neg (not_le.mp h)]; field_simp [hw1.ne', hw2.ne']
  have hρ0 : 0 ≤ ⟪e₁, e₂⟫ := by rw [hρ_eq]; positivity
  have hρ_sq : ⟪e₁, e₂⟫ ^ 2 * (‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) = ⟪w₁, w₂⟫ ^ 2 := by
    rw [hρ_eq, div_pow, sq_abs, mul_pow]; field_simp [hw1.ne', hw2.ne']
  have hr0_le : r0 ≤ ⟪e₁, e₂⟫ := by
    have : r0 ^ 2 ≤ ⟪e₁, e₂⟫ ^ 2 := le_of_mul_le_mul_right (by linarith) hKK
    nlinarith [sq_nonneg (⟪e₁, e₂⟫ - r0)]
  have hr1_ge : ⟪e₁, e₂⟫ ≤ r1 := by
    have : ⟪e₁, e₂⟫ ^ 2 ≤ r1 ^ 2 := le_of_mul_le_mul_right (by linarith) hKK
    nlinarith [sq_nonneg (r1 - ⟪e₁, e₂⟫), hr0.trans hr01]
  have hscale : (fun x : E => |⟪w₁, x⟫| * |⟪w₂, x⟫|) =
      fun x => √(‖w₁‖ ^ 2 * ‖w₂‖ ^ 2) * (|⟪e₁, x⟫| * |⟪e₂, x⟫|) := by
    funext x
    dsimp only [e₁, e₂]
    rw [real_inner_smul_left, real_inner_smul_left, abs_mul, abs_mul, abs_mul, hsgn_abs, one_mul,
      abs_inv, abs_inv, abs_of_pos hw1, abs_of_pos hw2, sqrt_mul (sq_nonneg _),
      sqrt_sq hw1.le, sqrt_sq hw2.le]
    field_simp [hw1.ne', hw2.ne']
  rw [hscale, integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    ((integral_abs_mul_abs_unit_le_hCub he1 he2 hρ0).trans (hCub_le_max hr0_le hr1_ge hr1))
    (sqrt_nonneg _)

private theorem integral_sq_indicator_abs_lt_le {w₁ w₂ : E} {k : ℝ} (hk : 0 ≤ k)
    (hdet : 0 < ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2) :
    ∫ x, ({x : E | |⟪w₂, x⟫| < k * |⟪w₁, x⟫|}).indicator
        (fun x => ⟪w₁, x⟫ ^ 2) x ∂stdGaussian E ≤
      4 * k * (‖w₁‖ ^ 2) ^ 2 / (π * √(‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 - ⟪w₁, w₂⟫ ^ 2)) := by
  obtain ⟨hK00_pos, _, w_perp, horth, hw_perp_sq, hv2_ne, hpt_eq⟩ := orth_decomp hdet
  set K00 := ‖w₁‖ ^ 2
  set K11 := ‖w₂‖ ^ 2
  set K01 := ⟪w₁, w₂⟫
  set detK := K00 * K11 - K01 ^ 2
  let α := K01 / K00
  have hprod_law := stdGaussian_map_inner_prod (E := E) horth
  let ψ : ℝ × ℝ → ℝ := fun p =>
    ({q : ℝ × ℝ | |α * q.1 + q.2| < k * |q.1|}).indicator (fun q => q.1 ^ 2) p
  have hS_meas : MeasurableSet {q : ℝ × ℝ | |α * q.1 + q.2| < k * |q.1|} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hψ_meas : Measurable ψ :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => q.1 ^ 2).indicator hS_meas
  have hψ_int :
      Integrable ψ ((gaussianReal 0 (‖w₁‖₊ ^ 2)).prod (gaussianReal 0 (‖w_perp‖₊ ^ 2))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => p.1 ^ 2)
        ((gaussianReal 0 (‖w₁‖₊ ^ 2)).prod (gaussianReal 0 (‖w_perp‖₊ ^ 2))) :=
      (integrable_sq_gaussianReal _).comp_fst _
    refine Integrable.mono' hdom hψ_meas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    dsimp only [ψ]
    by_cases hp : p ∈ {q : ℝ × ℝ | |α * q.1 + q.2| < k * |q.1|}
    · rw [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · rw [indicator_of_notMem hp, norm_zero]; exact sq_nonneg _
  have hexp : ∫ x, ({x : E | |⟪w₂, x⟫| < k * |⟪w₁, x⟫|}).indicator
        (fun x => ⟪w₁, x⟫ ^ 2) x ∂stdGaussian E =
      ∫ p, ψ p ∂(gaussianReal 0 (‖w₁‖₊ ^ 2)).prod (gaussianReal 0 (‖w_perp‖₊ ^ 2)) := by
    rw [← hprod_law, integral_map (by fun_prop) hψ_meas.aestronglyMeasurable]
    congr with x
    dsimp only [ψ, α, K01, K00]
    by_cases hx : |⟪w₂, x⟫| < k * |⟪w₁, x⟫|
    · have hx' : (⟪w₁, x⟫, ⟪w_perp, x⟫) ∈
          {q : ℝ × ℝ | |(⟪w₁, w₂⟫ / ‖w₁‖ ^ 2) * q.1 + q.2| < k * |q.1|} := by
        change |(⟪w₁, w₂⟫ / ‖w₁‖ ^ 2) * ⟪w₁, x⟫ + ⟪w_perp, x⟫| < k * |⟪w₁, x⟫|
        rwa [← hpt_eq x]
      simp only [mem_ofPred_eq, hx, hx', indicator_of_mem]
    · have hx' : (⟪w₁, x⟫, ⟪w_perp, x⟫) ∉
          {q : ℝ × ℝ | |(⟪w₁, w₂⟫ / ‖w₁‖ ^ 2) * q.1 + q.2| < k * |q.1|} := by
        change ¬|(⟪w₁, w₂⟫ / ‖w₁‖ ^ 2) * ⟪w₁, x⟫ + ⟪w_perp, x⟫| < k * |⟪w₁, x⟫|
        rwa [← hpt_eq x]
      simp only [mem_ofPred_eq, hx, hx', not_false_eq_true, indicator_of_notMem]
  rw [hexp, integral_prod _ hψ_int]
  have hslice (z : ℝ) : ∫ w, ψ (z, w) ∂gaussianReal 0 (‖w_perp‖₊ ^ 2) ≤
      2 * k / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3 := by
    let Sz : Set ℝ := {w | |α * z + w| < k * |z|}
    have hSz_eq : Sz = Ioo (-α * z - k * |z|) (-α * z + k * |z|) := by
      ext w; simp only [Sz, mem_ofPred_eq, abs_lt, mem_Ioo]
      constructor <;> intro hw <;> constructor <;> linarith
    have hSz_m : MeasurableSet Sz := hSz_eq ▸ measurableSet_Ioo
    have hfn : (fun w => ψ (z, w)) = fun w => z ^ 2 * Sz.indicator (1 : ℝ → ℝ) w := by
      funext w; dsimp only [ψ, Sz]
      by_cases hw : |α * z + w| < k * |z| <;>
        simp only [mem_ofPred_eq, hw, not_false_eq_true, indicator_of_mem, indicator_of_notMem,
          Pi.one_apply, mul_one, mul_zero]
    rw [hfn, integral_const_mul, integral_indicator_one hSz_m]
    have hmeas_le : (gaussianReal 0 (‖w_perp‖₊ ^ 2)).real Sz ≤
        2 * k * |z| / √(2 * π * ‖w_perp‖ ^ 2) := by
      rw [measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      refine (gaussianReal_le_ofReal_mul_volume 0 hv2_ne Sz).trans ?_
      have hcoe : ((‖w_perp‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖w_perp‖ ^ 2 := by rw [NNReal.coe_pow, coe_nnNorm]
      rw [hcoe, hSz_eq, Real.volume_Ioo,
        show -α * z + k * |z| - (-α * z - k * |z|) = 2 * k * |z| by ring,
        ← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div]
    have hmul := mul_le_mul_of_nonneg_left hmeas_le (sq_nonneg z)
    have hz3 : z ^ 2 * (2 * k * |z| / √(2 * π * ‖w_perp‖ ^ 2)) =
        2 * k / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3 := by
      rw [← sq_abs z]; ring
    linarith
  have hint_rhs : Integrable (fun z : ℝ => 2 * k / √(2 * π * ‖w_perp‖ ^ 2) * |z| ^ 3)
      (gaussianReal 0 (‖w₁‖₊ ^ 2)) := (integrable_abs_cube_gaussianReal _).const_mul _
  have hmono := integral_mono hψ_int.integral_prod_left hint_rhs hslice
  rw [integral_const_mul, integral_abs_cube_gaussianReal] at hmono
  have hc1 : ((‖w₁‖₊ ^ 2 : ℝ≥0) : ℝ) = K00 := by rw [NNReal.coe_pow, coe_nnNorm]
  rw [hc1, hw_perp_sq] at hmono
  refine hmono.trans_eq ?_
  have hpi : 0 < π := pi_pos
  have hsK : 0 < √K00 := sqrt_pos.mpr hK00_pos
  have hsD : 0 < √detK := sqrt_pos.mpr hdet
  have hs2 : 0 < √2 := sqrt_pos.mpr zero_lt_two
  have hspi : 0 < √π := sqrt_pos.mpr hpi
  have hsq_div : √(detK / K00) = √detK / √K00 := sqrt_div hdet.le _
  have hsq_2pi : √(2 * π * (detK / K00)) = √2 * √π * √detK / √K00 := by
    rw [sqrt_mul (by positivity), sqrt_mul zero_le_two, hsq_div, mul_div_assoc]
  have hsK3 : √K00 ^ 3 = K00 * √K00 := by
    rw [show √K00 ^ 3 = √K00 ^ 2 * √K00 by ring, sq_sqrt hK00_pos.le]
  rw [hsq_2pi, sqrt_div zero_le_two, hsK3]
  field_simp [hsK.ne', hsD.ne', hs2.ne', hspi.ne', hK00_pos.ne', hpi.ne']
  ring_nf
  rw [sq_sqrt hpi.le, sq_sqrt hK00_pos.le]
  ring

private theorem measureReal_planar_proj_le_of_volume_le {p_x p_y : E}
    (hD : 0 < ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {V : ℝ} (hV : 0 ≤ V)
    (hvol : volume S ≤ ENNReal.ofReal V) :
    (stdGaussian E).real {x | (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ S} ≤
      V / (2 * π * √(‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2)) := by
  obtain ⟨hvx_pos, hv1_ne, p_perp, horth, hp_perp_sq, hv2_ne, hpt_eq⟩ := orth_decomp hD
  set vx := ‖p_x‖ ^ 2
  set vy := ‖p_y‖ ^ 2
  set rb := ⟪p_x, p_y⟫
  set D := vx * vy - rb ^ 2
  let β := rb / vx
  let S' : Set (ℝ × ℝ) := {q | (q.1, β * q.1 + q.2) ∈ S}
  have hS'_m : MeasurableSet S' := hS.preimage (by fun_prop)
  have hmap_eq : stdGaussian E {x | (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ S} =
      ((gaussianReal 0 (‖p_x‖₊ ^ 2)).prod (gaussianReal 0 (‖p_perp‖₊ ^ 2))) S' := by
    rw [← stdGaussian_map_inner_prod horth, Measure.map_apply (by fun_prop) hS'_m]
    congr 1; ext x; simp only [S', β, rb, vx, mem_preimage, mem_ofPred_eq, hpt_eq x]
  rw [measureReal_def, hmap_eq, Measure.prod_apply hS'_m]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have hslice (z₁ : ℝ) : gaussianReal 0 (‖p_perp‖₊ ^ 2) (Prod.mk z₁ ⁻¹' S') ≤
      ENNReal.ofReal (√(2 * π * (D / vx)))⁻¹ * volume (Prod.mk z₁ ⁻¹' S) := by
    have hpre : Prod.mk z₁ ⁻¹' S' = (fun z₂ => β * z₁ + z₂) ⁻¹' (Prod.mk z₁ ⁻¹' S) := rfl
    rw [hpre]
    refine (gaussianReal_le_ofReal_mul_volume 0 hv2_ne _).trans ?_
    have hc2 : ((‖p_perp‖₊ ^ 2 : ℝ≥0) : ℝ) = D / vx := by
      rw [NNReal.coe_pow, coe_nnNorm, hp_perp_sq]
    rw [hc2, measure_preimage_add volume (β * z₁) (Prod.mk z₁ ⁻¹' S)]
  have h1 : ∫⁻ z₁, gaussianReal 0 (‖p_perp‖₊ ^ 2) (Prod.mk z₁ ⁻¹' S')
        ∂gaussianReal 0 (‖p_x‖₊ ^ 2) ≤
      ENNReal.ofReal (√(2 * π * (D / vx)))⁻¹ *
        ∫⁻ z₁, volume (Prod.mk z₁ ⁻¹' S) ∂gaussianReal 0 (‖p_x‖₊ ^ 2) := by
    rw [← lintegral_const_mul _ (measurable_measure_prodMk_left hS)]
    exact lintegral_mono hslice
  have h2 : ∫⁻ z₁, volume (Prod.mk z₁ ⁻¹' S) ∂gaussianReal 0 (‖p_x‖₊ ^ 2) ≤
      ENNReal.ofReal (√(2 * π * vx))⁻¹ * volume S := by
    rw [gaussianReal_of_var_ne_zero 0 hv1_ne,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 _)
        (measurable_measure_prodMk_left hS)]
    have hc1 : ((‖p_x‖₊ ^ 2 : ℝ≥0) : ℝ) = vx := by rw [NNReal.coe_pow, coe_nnNorm]
    calc ∫⁻ z₁, gaussianPDF 0 (‖p_x‖₊ ^ 2) z₁ * volume (Prod.mk z₁ ⁻¹' S)
        ≤ ∫⁻ z₁, ENNReal.ofReal (√(2 * π * vx))⁻¹ * volume (Prod.mk z₁ ⁻¹' S) := by
          refine lintegral_mono fun z₁ => mul_le_mul_of_nonneg_right ?_ bot_le
          rw [gaussianPDF, ← hc1]
          exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le 0 _ z₁)
      _ = ENNReal.ofReal (√(2 * π * vx))⁻¹ * ∫⁻ z₁, volume (Prod.mk z₁ ⁻¹' S) :=
          lintegral_const_mul _ (measurable_measure_prodMk_left hS)
      _ = ENNReal.ofReal (√(2 * π * vx))⁻¹ * volume S := by
          rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 bot_le).trans ?_)
  rw [← mul_assoc]
  refine (mul_le_mul_of_nonneg_left hvol bot_le).trans_eq ?_
  have hpi : 0 < π := pi_pos
  have hsD : 0 < √D := sqrt_pos.mpr hD
  have hsvx : 0 < √vx := sqrt_pos.mpr hvx_pos
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hmul_inv : (√(2 * π * (D / vx)))⁻¹ * (√(2 * π * vx))⁻¹ = (2 * π * √D)⁻¹ := by
    have h2pi_pos : 0 < 2 * π := by positivity
    have hs2pi : 0 < √(2 * π) := sqrt_pos.mpr h2pi_pos
    rw [sqrt_mul h2pi_pos.le, sqrt_div hD.le, sqrt_mul h2pi_pos.le]
    field_simp [hs2pi.ne', hsD.ne', hsvx.ne', hpi.ne']
    ring_nf
    exact (sq_sqrt (by positivity)).symm
  rw [hmul_inv, inv_mul_eq_div]

private theorem indepFun_planar_residual {p_x p_y w_u w_v : E}
    (h1 : ⟪p_x, w_u⟫ = 0) (h2 : ⟪p_x, w_v⟫ = 0) (h3 : ⟪p_y, w_u⟫ = 0) (h4 : ⟪p_y, w_v⟫ = 0) :
    IndepFun (fun x => (⟪p_x, x⟫, ⟪p_y, x⟫)) (fun x => (⟪w_u, x⟫, ⟪w_v, x⟫)) (stdGaussian E) := by
  let u1 : Fin 2 → E := ![p_x, p_y]
  let u2 : Fin 2 → E := ![w_u, w_v]
  let L₁ : E →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i => innerSL ℝ (u1 i)
  let L₂ : E →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun j => innerSL ℝ (u2 j)
  have hlaw : HasGaussianLaw (fun x => (fun i => ⟪u1 i, x⟫, fun j => ⟪u2 j, x⟫))
      (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (L₁.prod L₂)
  have hind : IndepFun (fun x i => ⟪u1 i, x⟫) (fun x j => ⟪u2 j, x⟫) (stdGaussian E) := by
    refine hlaw.indepFun_of_covariance_eval fun i j => ?_
    have hcov := covarianceBilin_apply_eq_cov (μ := stdGaussian E) IsGaussian.memLp_two_id
      (u1 i) (u2 j)
    rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ] at hcov
    rw [← hcov]
    fin_cases i <;> fin_cases j <;> simp [u1, u2, h1, h2, h3, h4]
  exact hind.comp (by fun_prop : Measurable fun f : Fin 2 → ℝ => (f 0, f 1))
    (by fun_prop : Measurable fun f : Fin 2 → ℝ => (f 0, f 1))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem orth_residuals_calc {p_x p_y d_x d_y : E} {vx vy rb o1 o2 tau : ℝ}
    (hpx : ‖p_x‖ ^ 2 = vx) (hpy : ‖p_y‖ ^ 2 = vy)
    (hdx : ‖d_x‖ ^ 2 = 1 - vx) (hdy : ‖d_y‖ ^ 2 = 1 - vy)
    (hpxy : ⟪p_x, p_y⟫ = rb) (hpd_xx : ⟪p_x, d_x⟫ = 0) (hpd_yy : ⟪p_y, d_y⟫ = 0)
    (hpd_xy : ⟪p_x, d_y⟫ = o2) (hpd_yx : ⟪p_y, d_x⟫ = o1) (hdd_xy : ⟪d_x, d_y⟫ = tau)
    (hD : 0 < vx * vy - rb ^ 2) :
    let D := vx * vy - rb ^ 2
    let b1 := o1 / D
    let b2 := o2 / D
    let w_u := d_x + (b1 * rb) • p_x - (b1 * vx) • p_y
    let w_v := d_y - (b2 * vy) • p_x + (b2 * rb) • p_y
    ⟪p_x, w_u⟫ = 0 ∧ ⟪p_x, w_v⟫ = 0 ∧ ⟪p_y, w_u⟫ = 0 ∧ ⟪p_y, w_v⟫ = 0 ∧
    ‖w_u‖ ^ 2 = 1 - vx - o1 ^ 2 * vx / D ∧
    ‖w_v‖ ^ 2 = 1 - vy - o2 ^ 2 * vy / D ∧
    ⟪w_u, w_v⟫ = tau + o1 * o2 * rb / D ∧
    ∀ x : E,
      (|⟪p_x, x⟫| < |⟪d_x, x⟫| ∧ |⟪p_y, x⟫| < |⟪d_y, x⟫| ↔
        (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ planarRectSet b1 b2 rb vx vy ⟪w_u, x⟫ ⟪w_v, x⟫) := by
  intro D b1 b2 w_u w_v
  have cyx : ⟪p_y, p_x⟫ = ⟪p_x, p_y⟫ := real_inner_comm _ _
  have ho1 : ⟪p_x, w_u⟫ = 0 := by
    dsimp only [w_u]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hpx, hpxy, hpd_xx]; ring
  have ho2 : ⟪p_x, w_v⟫ = 0 := by
    dsimp only [w_v, b2]
    rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hpx, hpxy, hpd_xy]
    dsimp only [D]; field_simp [hD.ne']; ring
  have ho3 : ⟪p_y, w_u⟫ = 0 := by
    dsimp only [w_u, b1]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hpy, cyx, hpxy, hpd_yx]
    dsimp only [D]; field_simp [hD.ne']; ring
  have ho4 : ⟪p_y, w_v⟫ = 0 := by
    dsimp only [w_v]
    rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hpy, cyx, hpxy, hpd_yy]; ring
  have hwu_sq : ‖w_u‖ ^ 2 = 1 - vx - o1 ^ 2 * vx / D := by
    have hdx_eq : d_x = w_u + ((-(b1 * rb)) • p_x + (b1 * vx) • p_y) := by
      simp only [w_u, neg_smul, sub_eq_add_neg]; abel
    have horth_u : ⟪w_u, (-(b1 * rb)) • p_x + (b1 * vx) • p_y⟫ = 0 := by
      have c1 : ⟪w_u, p_x⟫ = ⟪p_x, w_u⟫ := real_inner_comm _ _
      have c2 : ⟪w_u, p_y⟫ = ⟪p_y, w_u⟫ := real_inner_comm _ _
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        c1, ho1, c2, ho3]
      ring
    have hcomb_sq : ‖(-(b1 * rb)) • p_x + (b1 * vx) • p_y‖ ^ 2 = o1 ^ 2 * vx / D := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left,
        real_inner_smul_right, hpx, hpy, hpxy]
      dsimp only [b1, D]; field_simp [hD.ne']; ring
    have hpyth : ‖d_x‖ ^ 2 = ‖w_u‖ ^ 2 + ‖(-(b1 * rb)) • p_x + (b1 * vx) • p_y‖ ^ 2 := by
      conv_lhs => rw [hdx_eq]
      rw [norm_add_sq_real, horth_u]; ring
    linarith [hdx, hcomb_sq]
  have hwv_sq : ‖w_v‖ ^ 2 = 1 - vy - o2 ^ 2 * vy / D := by
    have hdy_eq : d_y = w_v + ((b2 * vy) • p_x - (b2 * rb) • p_y) := by
      dsimp only [w_v]; abel
    have horth_v : ⟪w_v, (b2 * vy) • p_x - (b2 * rb) • p_y⟫ = 0 := by
      have c1 : ⟪w_v, p_x⟫ = ⟪p_x, w_v⟫ := real_inner_comm _ _
      have c2 : ⟪w_v, p_y⟫ = ⟪p_y, w_v⟫ := real_inner_comm _ _
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        c1, ho2, c2, ho4]
      ring
    have hcomb_sq : ‖(b2 * vy) • p_x - (b2 * rb) • p_y‖ ^ 2 = o2 ^ 2 * vy / D := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left,
        real_inner_smul_right, hpx, hpy, hpxy]
      dsimp only [b2, D]; field_simp [hD.ne']; ring
    have hpyth : ‖d_y‖ ^ 2 = ‖w_v‖ ^ 2 + ‖(b2 * vy) • p_x - (b2 * rb) • p_y‖ ^ 2 := by
      conv_lhs => rw [hdy_eq]
      rw [norm_add_sq_real, horth_v]; ring
    linarith [hdy, hcomb_sq]
  have hwuv : ⟪w_u, w_v⟫ = tau + o1 * o2 * rb / D := by
    have h1 : ⟪w_u, w_v⟫ = ⟪w_u, d_y⟫ := by
      have c1 : ⟪w_u, p_x⟫ = ⟪p_x, w_u⟫ := real_inner_comm _ _
      have c2 : ⟪w_u, p_y⟫ = ⟪p_y, w_u⟫ := real_inner_comm _ _
      dsimp only [w_v]
      rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        c1, ho1, c2, ho3]; ring
    rw [h1]
    dsimp only [w_u, b1]
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hdd_xy, hpd_xy, hpd_yy]; ring
  refine ⟨ho1, ho2, ho3, ho4, hwu_sq, hwv_sq, hwuv, fun x => ?_⟩
  simp only [planarRectSet, mem_ofPred_eq, w_u, w_v, inner_add_left, inner_sub_left,
    real_inner_smul_left]
  have e1 : ⟪d_x, x⟫ + b1 * rb * ⟪p_x, x⟫ - b1 * vx * ⟪p_y, x⟫ - b1 * rb * ⟪p_x, x⟫ +
      b1 * vx * ⟪p_y, x⟫ = ⟪d_x, x⟫ := by ring
  have e2 : ⟪d_y, x⟫ - b2 * vy * ⟪p_x, x⟫ + b2 * rb * ⟪p_y, x⟫ + b2 * vy * ⟪p_x, x⟫ -
      b2 * rb * ⟪p_y, x⟫ = ⟪d_y, x⟫ := by ring
  rw [e1, e2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Orthogonal regression residuals `(w_u, w_v)` for `u : Fin 4 → E` when `D > 0`. -/
theorem pair_orth_residuals {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    (hD : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) :
    let vx := (1 + pairSab u) / 2
    let vy := (1 + pairScd u) / 2
    let rb := pairRb u
    let D := vx * vy - rb ^ 2
    let b1 := pairO1 u / D
    let b2 := pairO2 u / D
    let p_x := (1 / 2 : ℝ) • (u 0 + u 1)
    let p_y := (1 / 2 : ℝ) • (u 2 + u 3)
    let d_x := (1 / 2 : ℝ) • (u 0 - u 1)
    let d_y := (1 / 2 : ℝ) • (u 2 - u 3)
    let w_u := d_x + (b1 * rb) • p_x - (b1 * vx) • p_y
    let w_v := d_y - (b2 * vy) • p_x + (b2 * rb) • p_y
    ‖p_x‖ ^ 2 = vx ∧ ‖p_y‖ ^ 2 = vy ∧ ⟪p_x, p_y⟫ = rb ∧
    ⟪p_x, w_u⟫ = 0 ∧ ⟪p_x, w_v⟫ = 0 ∧ ⟪p_y, w_u⟫ = 0 ∧ ⟪p_y, w_v⟫ = 0 ∧
    ‖w_u‖ ^ 2 = (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D ∧
    ‖w_v‖ ^ 2 = (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D ∧
    ⟪w_u, w_v⟫ = pairTau u + pairO1 u * pairO2 u * rb / D ∧
    ∀ x : E,
      (|⟪p_x, x⟫| < |⟪d_x, x⟫| ∧ |⟪p_y, x⟫| < |⟪d_y, x⟫| ↔
        (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ planarRectSet b1 b2 rb vx vy ⟪w_u, x⟫ ⟪w_v, x⟫) := by
  intro vx vy rb D b1 b2 p_x p_y d_x d_y w_u w_v
  have hpx : ‖p_x‖ ^ 2 = vx := by
    dsimp only [p_x, vx, pairSab]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, hu 0, hu 1]; ring
  have hpy : ‖p_y‖ ^ 2 = vy := by
    dsimp only [p_y, vy, pairScd]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, hu 2, hu 3]; ring
  have hdx : ‖d_x‖ ^ 2 = 1 - vx := by
    dsimp only [d_x, vx, pairSab]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, hu 0, hu 1]; ring
  have hdy : ‖d_y‖ ^ 2 = 1 - vy := by
    dsimp only [d_y, vy, pairScd]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real, hu 2, hu 3]; ring
  have hpxy : ⟪p_x, p_y⟫ = rb := by
    dsimp only [p_x, p_y, rb, pairRb]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right]; ring
  have hpd_xx : ⟪p_x, d_x⟫ = 0 := by
    dsimp only [p_x, d_x]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hu 0, hu 1, real_inner_comm (u 1) (u 0)]; ring
  have hpd_yy : ⟪p_y, d_y⟫ = 0 := by
    dsimp only [p_y, d_y]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hu 2, hu 3, real_inner_comm (u 3) (u 2)]; ring
  have hpd_xy : ⟪p_x, d_y⟫ = pairO2 u := by
    dsimp only [p_x, d_y, pairO2]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right]; ring
  have hpd_yx : ⟪p_y, d_x⟫ = pairO1 u := by
    dsimp only [p_y, d_x, pairO1]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
      real_inner_comm (u 2), real_inner_comm (u 3)]; ring
  have hdd_xy : ⟪d_x, d_y⟫ = pairTau u := by
    dsimp only [d_x, d_y, pairTau]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]; ring
  obtain ⟨ho1, ho2, ho3, ho4, hwu_sq, hwv_sq, hwuv, hiff⟩ :=
    orth_residuals_calc hpx hpy hdx hdy hpxy hpd_xx hpd_yy hpd_xy hpd_yx hdd_xy hD
  refine ⟨hpx, hpy, hpxy, ho1, ho2, ho3, ho4, ?_, ?_, hwuv, hiff⟩
  · refine hwu_sq.trans ?_; dsimp only [vx]; ring
  · refine hwv_sq.trans ?_; dsimp only [vy]; ring

private theorem measureReal_planarRect_cond_le {p_x p_y w_u w_v : E} {b1 b2 rb vx vy : ℝ}
    (h1 : ⟪p_x, w_u⟫ = 0) (h2 : ⟪p_x, w_v⟫ = 0) (h3 : ⟪p_y, w_u⟫ = 0) (h4 : ⟪p_y, w_v⟫ = 0)
    (hD : 0 < ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2)
    {g : ℝ × ℝ → ℝ} (hg_int : Integrable (fun x => g (⟪w_u, x⟫, ⟪w_v, x⟫)) (stdGaussian E))
    (hg_nn : ∀ q, 0 ≤ g q)
    (hvol : ∀ ξ η, volume (planarRectSet b1 b2 rb vx vy ξ η) ≤ ENNReal.ofReal (g (ξ, η))) :
    (stdGaussian E).real {x | (⟪p_x, x⟫, ⟪p_y, x⟫) ∈
        planarRectSet b1 b2 rb vx vy ⟪w_u, x⟫ ⟪w_v, x⟫} ≤
      (∫ x, g (⟪w_u, x⟫, ⟪w_v, x⟫) ∂stdGaussian E) /
        (2 * π * √(‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2)) := by
  set μ := stdGaussian E
  let X : E → ℝ × ℝ := fun x => (⟪p_x, x⟫, ⟪p_y, x⟫)
  let Y : E → ℝ × ℝ := fun x => (⟪w_u, x⟫, ⟪w_v, x⟫)
  have hXm : Measurable X := by fun_prop
  have hYm : Measurable Y := by fun_prop
  let Q : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | q.2 ∈ planarRectSet b1 b2 rb vx vy q.1.1 q.1.2}
  have hQm : MeasurableSet Q :=
    (measurableSet_planarRectSet_quad b1 b2 rb vx vy).preimage measurable_swap
  have hind := (indepFun_planar_residual h1 h2 h3 h4).symm.map_prod_eq_prod_map_map
    hYm.aemeasurable hXm.aemeasurable
  have heq : μ.real {x | X x ∈ planarRectSet b1 b2 rb vx vy (Y x).1 (Y x).2} =
      ((μ.map Y).prod (μ.map X)).real Q := by
    rw [measureReal_def, measureReal_def, ← hind, Measure.map_apply (hYm.prodMk hXm) hQm]
    rfl
  rw [heq, real_prod_eq_integral (μ.map Y) (μ.map X) hQm]
  have hslice_m : Measurable fun r : ℝ × ℝ => (μ.map X).real (Prod.mk r ⁻¹' Q) :=
    measurable_prod_slice (μ.map X) hQm
  rw [integral_map hYm.aemeasurable hslice_m.aestronglyMeasurable]
  set D := ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2
  have hpt (x : E) : (μ.map X).real (Prod.mk (Y x) ⁻¹' Q) ≤
      g (Y x) / (2 * π * √D) := by
    have hm_fib : MeasurableSet (planarRectSet b1 b2 rb vx vy (Y x).1 (Y x).2) :=
      measurableSet_planarRectSet _ _ _ _ _ _ _
    have hfib_eq : Prod.mk (Y x) ⁻¹' Q = planarRectSet b1 b2 rb vx vy (Y x).1 (Y x).2 := rfl
    have hmap_fib : (μ.map X).real (Prod.mk (Y x) ⁻¹' Q) =
        μ.real {z | X z ∈ planarRectSet b1 b2 rb vx vy (Y x).1 (Y x).2} := by
      rw [hfib_eq, measureReal_def, measureReal_def, Measure.map_apply hXm hm_fib]; rfl
    rw [hmap_fib]
    exact measureReal_planar_proj_le_of_volume_le hD hm_fib (hg_nn (Y x)) (hvol (Y x).1 (Y x).2)
  have hint_lhs : Integrable (fun x => (μ.map X).real (Prod.mk (Y x) ⁻¹' Q)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hslice_m.comp hYm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hmono := integral_mono hint_lhs (hg_int.div_const (2 * π * √D)) hpt
  rwa [integral_div] at hmono

theorem pairCost_zero_le_planar_out {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    (ho1 : 0 ≤ pairO1 u) (ho2 : 0 ≤ pairO2 u) (hrb : 0 < pairRb u)
    {C_ex : ℝ} (_hC_ex : 0 ≤ C_ex)
    (hD : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)
    (hx1 : pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u < 1)
    (hx2 : pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u < 1)
    (hvxy : (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) ≤ 2 * pairRb u ^ 2)
    (hdetM : 0 <
      (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2))
    (hcorr : ∀ w_u w_v : E,
      ‖w_u‖ ^ 2 = (1 - pairSab u) / 2 - pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ‖w_v‖ ^ 2 = (1 - pairScd u) / 2 - pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ⟪w_u, w_v⟫ = pairTau u + pairO1 u * pairO2 u * pairRb u /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ∫ x, |⟪w_u, x⟫| * |⟪w_v, x⟫| ∂stdGaussian E ≤ C_ex * √(‖w_u‖ ^ 2 * ‖w_v‖ ^ 2)) :
    let vx := (1 + pairSab u) / 2
    let vy := (1 + pairScd u) / 2
    let rb := pairRb u
    let D := vx * vy - rb ^ 2
    let u1 := pairO1 u / D
    let u2 := pairO2 u / D
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM := (1 - x1) * (1 - x2) - P
    let K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
    let K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
    pairCost u 0 ≤
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
      (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) / (4 * π) +
      (pairCxMax u2 vy x1 x2 detM * K00 + pairCxMax u1 vx x2 x1 detM * K11 +
        pairCAB x1 x2 P detM * (C_ex * √(K00 * K11))) / (4 * π * √D) := by
  intro vx vy rb D u1 u2 x1 x2 P detM K00 K11
  obtain ⟨hpx, hpy, hpxy, ho_1, ho_2, ho_3, ho_4, hwu_sq, hwv_sq, hwuv, hiff⟩ :=
    pair_orth_residuals hu hD
  set p_x := (1 / 2 : ℝ) • (u 0 + u 1)
  set p_y := (1 / 2 : ℝ) • (u 2 + u 3)
  set d_x := (1 / 2 : ℝ) • (u 0 - u 1)
  set d_y := (1 / 2 : ℝ) • (u 2 - u 3)
  set w_u := d_x + (u1 * rb) • p_x - (u1 * vx) • p_y
  set w_v := d_y - (u2 * vy) • p_x + (u2 * rb) • p_y
  have hvx_nn : 0 ≤ vx := (sq_nonneg ‖p_x‖).trans_eq hpx
  have hvy_nn : 0 ≤ vy := (sq_nonneg ‖p_y‖).trans_eq hpy
  have hu1_nn : 0 ≤ u1 := div_nonneg ho1 hD.le
  have hu2_nn : 0 ≤ u2 := div_nonneg ho2 hD.le
  have habs_u1 : |u1| = u1 := abs_of_nonneg hu1_nn
  have habs_u2 : |u2| = u2 := abs_of_nonneg hu2_nn
  have hcx_nn : 0 ≤ pairCxMax u2 vy x1 x2 detM := by
    unfold pairCxMax pairCxp
    refine le_trans ?_ (le_max_left _ _)
    have h1mx1 : 0 < 1 - x1 := by linarith
    have h1mx2 : 0 < 1 - x2 := by linarith
    have h1px1 : 0 < 1 + x1 := by linarith [mul_nonneg hu1_nn hrb.le]
    have h1px2 : 0 < 1 + x2 := by linarith [mul_nonneg hu2_nn hrb.le]
    positivity
  have hce_nn : 0 ≤ pairCxMax u1 vx x2 x1 detM := by
    unfold pairCxMax pairCxp
    refine le_trans ?_ (le_max_left _ _)
    have h1mx1 : 0 < 1 - x1 := by linarith
    have h1mx2 : 0 < 1 - x2 := by linarith
    have h1px1 : 0 < 1 + x1 := by linarith [mul_nonneg hu1_nn hrb.le]
    have h1px2 : 0 < 1 + x2 := by linarith [mul_nonneg hu2_nn hrb.le]
    positivity
  have hcAB_nn : 0 ≤ pairCAB x1 x2 P detM := by
    unfold pairCAB
    have hx1_nn : 0 ≤ x1 := mul_nonneg hu1_nn hrb.le
    have hx2_nn : 0 ≤ x2 := mul_nonneg hu2_nn hrb.le
    have h1x1 : 0 < 1 - x1 ^ 2 := by nlinarith
    have h1x2 : 0 < 1 - x2 ^ 2 := by nlinarith
    have h1mx1 : 0 < 1 - x1 := by linarith
    have h1mx2 : 0 < 1 - x2 := by linarith
    have hP_nn : 0 ≤ P := by dsimp only [P]; positivity
    positivity
  let g : ℝ × ℝ → ℝ := fun q =>
    pairCxMax u2 vy x1 x2 detM * q.1 ^ 2 + pairCxMax u1 vx x2 x1 detM * q.2 ^ 2 +
      pairCAB x1 x2 P detM * (|q.1| * |q.2|)
  have hm1 : Integrable (fun x : E => ⟪w_u, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w_u) ▸
      integrable_sq_gaussianReal (‖w_u‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hm2 : Integrable (fun x : E => ⟪w_v, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w_v) ▸
      integrable_sq_gaussianReal (‖w_v‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hm12 : Integrable (fun x : E =>
      pairCxMax u2 vy x1 x2 detM * ⟪w_u, x⟫ ^ 2 +
        pairCxMax u1 vx x2 x1 detM * ⟪w_v, x⟫ ^ 2) (stdGaussian E) :=
    (hm1.const_mul _).add (hm2.const_mul _)
  have hg_int : Integrable (fun x => g (⟪w_u, x⟫, ⟪w_v, x⟫)) (stdGaussian E) :=
    hm12.add ((integrable_abs_mul_abs_inner w_u w_v).const_mul _)
  have hD_p : 0 < ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2 := by rwa [hpx, hpy, hpxy]
  have hcond := measureReal_planarRect_cond_le (b1 := u1) (b2 := u2) (rb := rb) (vx := vx)
    (vy := vy) ho_1 ho_2 ho_3 ho_4 hD_p hg_int
    (fun q => by dsimp only [g]; positivity) fun ξ η => by
      have hv := volume_planarRectSet_le_out hrb hvx_nn hvy_nn
        (by rwa [habs_u1]) (by rwa [habs_u2]) hvxy (by rwa [habs_u1, habs_u2]) ξ η
      simpa only [habs_u1, habs_u2, g] using hv
  have hset_eq : {x : E | |⟪p_x, x⟫| < |⟪d_x, x⟫| ∧ |⟪p_y, x⟫| < |⟪d_y, x⟫|} =
      {x : E | (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ planarRectSet u1 u2 rb vx vy ⟪w_u, x⟫ ⟪w_v, x⟫} := by
    ext x; exact hiff x
  rw [pairCost_zero_eq_ch_add_half_rect hu, hset_eq]
  have hg_eval : ∫ x, g (⟪w_u, x⟫, ⟪w_v, x⟫) ∂stdGaussian E ≤
      pairCxMax u2 vy x1 x2 detM * K00 + pairCxMax u1 vx x2 x1 detM * K11 +
        pairCAB x1 x2 P detM * (C_ex * √(K00 * K11)) := by
    dsimp only [g]
    rw [integral_add hm12 ((integrable_abs_mul_abs_inner w_u w_v).const_mul _),
      integral_add (hm1.const_mul _) (hm2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sq_inner_stdGaussian, integral_sq_inner_stdGaussian]
    have hc_le := hcorr w_u w_v hwu_sq hwv_sq hwuv
    rw [hwu_sq, hwv_sq] at hc_le ⊢
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc_le hcAB_nn)
  rw [hpx, hpy, hpxy] at hcond
  have hpiD : 0 < 2 * π * √D := by have := pi_pos; have := sqrt_pos.mpr hD; positivity
  have hstep := hcond.trans (div_le_div_of_nonneg_right hg_eval hpiD.le)
  have hhalf : 1 / 2 * ((pairCxMax u2 vy x1 x2 detM * K00 + pairCxMax u1 vx x2 x1 detM * K11 +
        pairCAB x1 x2 P detM * (C_ex * √(K00 * K11))) / (2 * π * √D)) =
      (pairCxMax u2 vy x1 x2 detM * K00 + pairCxMax u1 vx x2 x1 detM * K11 +
        pairCAB x1 x2 P detM * (C_ex * √(K00 * K11))) / (4 * π * √D) := by ring
  linarith

private theorem pairCost_zero_le_planar_in_aux {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    {vx vy rb D u1 u2 x1 x2 P detM detM2 k2 k1 cxe cxm cem cAB tail_cx tail_ce
      K00 K11 K01 detK C_ex : ℝ}
    (ho1 : 0 ≤ pairO1 u) (ho2 : 0 ≤ pairO2 u) (hrb : 0 < rb)
    (hD : 0 < D) (hx1 : x1 < 1) (hx2 : x2 < 1) (hvxy : vx * vy ≤ 2 * rb ^ 2)
    (hdetM2 : 0 < detM2) (hdetK : 0 < detK)
    (hcorr : ∀ w_u w_v : E, ‖w_u‖ ^ 2 = K00 → ‖w_v‖ ^ 2 = K11 → ⟪w_u, w_v⟫ = K01 →
      ∫ x, |⟪w_u, x⟫| * |⟪w_v, x⟫| ∂stdGaussian E ≤ C_ex * √(‖w_u‖ ^ 2 * ‖w_v‖ ^ 2))
    (hvx_def : vx = (1 + pairSab u) / 2) (hvy_def : vy = (1 + pairScd u) / 2)
    (hrb_def : rb = pairRb u) (hD_def : D = vx * vy - rb ^ 2)
    (hu1_def : u1 = pairO1 u / D) (hu2_def : u2 = pairO2 u / D)
    (hx1_def : x1 = u1 * rb) (hx2_def : x2 = u2 * rb)
    (hP_def : P = u1 * u2 * vx * vy) (hdetM_def : detM = (1 - x1) * (1 - x2) - P)
    (hdetM2_def : detM2 = (1 - x1) * (1 - x2) - 2 * P)
    (hk2_def : k2 = u2 * vy * (1 - x2) / detM2) (hk1_def : k1 = u1 * vx * (1 - x1) / detM2)
    (hcxe_def : cxe = pairCxe u1 u2 rb D)
    (hcxm_def : cxm = pairCxMax u2 vy x1 x2 detM)
    (hcem_def : cem = pairCxMax u1 vx x2 x1 detM)
    (hcAB_def : cAB = pairCAB x1 x2 P detM)
    (htcx_def : tail_cx = cxm + max 0 (cAB - cxe) * k2 + cem * k2 ^ 2)
    (htce_def : tail_ce = cem + max 0 (cAB - cxe) * k1 + cxm * k1 ^ 2)
    (hK00_def : K00 = (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D)
    (hK11_def : K11 = (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D)
    (hK01_def : K01 = pairTau u + pairO1 u * pairO2 u * rb / D)
    (hdetK_def : detK = K00 * K11 - K01 ^ 2) :
    pairCost u 0 ≤
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
      (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) / (4 * π) +
      ((pairAbsCx2 u1 u2 rb vy D + tail_cx * (4 * k2 * K00 / (π * √detK))) * K00 +
        (pairAbsCe2 u1 u2 rb vx D + tail_ce * (4 * k1 * K11 / (π * √detK))) * K11 +
        cxe * (C_ex * √(K00 * K11))) / (4 * π * √D) := by
  have hD' : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2 := by
    rwa [← hvx_def, ← hvy_def, ← hrb_def, ← hD_def]
  obtain ⟨hpx, hpy, hpxy, ho_1, ho_2, ho_3, ho_4, hwu_sq, hwv_sq, hwuv, hiff⟩ :=
    pair_orth_residuals hu hD'
  simp only [← hvx_def, ← hvy_def, ← hrb_def] at hpx hpy hpxy ho_1 ho_2 ho_3 ho_4
  simp only [← hvx_def, ← hvy_def, ← hrb_def] at hwu_sq hwv_sq hwuv hiff
  simp only [← hD_def] at ho_1 ho_2 ho_3 ho_4 hwu_sq hwv_sq hwuv hiff
  simp only [← hu1_def, ← hu2_def] at ho_1 ho_2 ho_3 ho_4 hwu_sq hwv_sq hwuv hiff
  rw [← hK00_def] at hwu_sq
  rw [← hK11_def] at hwv_sq
  rw [← hK01_def] at hwuv
  set p_x := (1 / 2 : ℝ) • (u 0 + u 1)
  set p_y := (1 / 2 : ℝ) • (u 2 + u 3)
  set d_x := (1 / 2 : ℝ) • (u 0 - u 1)
  set d_y := (1 / 2 : ℝ) • (u 2 - u 3)
  set w_u := d_x + (u1 * rb) • p_x - (u1 * vx) • p_y
  set w_v := d_y - (u2 * vy) • p_x + (u2 * rb) • p_y
  have hvx_nn : 0 ≤ vx := (sq_nonneg ‖p_x‖).trans_eq hpx
  have hvy_nn : 0 ≤ vy := (sq_nonneg ‖p_y‖).trans_eq hpy
  have hu1_nn : 0 ≤ u1 := hu1_def ▸ div_nonneg ho1 hD.le
  have hu2_nn : 0 ≤ u2 := hu2_def ▸ div_nonneg ho2 hD.le
  have habs_u1 : |u1| = u1 := abs_of_nonneg hu1_nn
  have habs_u2 : |u2| = u2 := abs_of_nonneg hu2_nn
  have hx1_nn : 0 ≤ x1 := hx1_def ▸ mul_nonneg hu1_nn hrb.le
  have hx2_nn : 0 ≤ x2 := hx2_def ▸ mul_nonneg hu2_nn hrb.le
  have h1mx1 : 0 < 1 - x1 := by linarith
  have h1mx2 : 0 < 1 - x2 := by linarith
  have h1px1 : 0 < 1 + x1 := by linarith
  have h1px2 : 0 < 1 + x2 := by linarith
  have hP_nn : 0 ≤ P := by rw [hP_def]; positivity
  have hdetM : 0 < detM := by linarith [hdetM_def, hdetM2_def]
  have hk2_nn : 0 ≤ k2 := by rw [hk2_def]; positivity
  have hk1_nn : 0 ≤ k1 := by rw [hk1_def]; positivity
  have hcxm_nn : 0 ≤ cxm := by
    rw [hcxm_def]; unfold pairCxMax pairCxp
    exact le_trans (by positivity) (le_max_left _ _)
  have hcem_nn : 0 ≤ cem := by
    rw [hcem_def]; unfold pairCxMax pairCxp
    exact le_trans (by positivity) (le_max_left _ _)
  have htcx_nn : 0 ≤ tail_cx := by rw [htcx_def]; positivity
  have htce_nn : 0 ≤ tail_ce := by rw [htce_def]; positivity
  have hQp_pos : 0 < pairQp u1 u2 rb D := by
    unfold pairQp
    have hlt : u2 * |rb - u1 * D| < 1 + x1 := by
      rcases abs_cases (rb - u1 * D) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        have h1 : u2 * (rb - u1 * D) = x2 - u1 * u2 * D := by rw [hx2_def]; ring
        have h2 : 0 ≤ u1 * u2 * D := by positivity
        linarith
      · rw [h]
        have h1 : u2 * -(rb - u1 * D) = P - x2 * (1 + x1) := by
          rw [hP_def, hx1_def, hx2_def, hD_def]; ring
        have h2 : (1 + x1) - (P - x2 * (1 + x1)) = detM + 2 * x1 + 2 * x2 := by
          rw [hdetM_def]; ring
        linarith
    have hsq : (u2 * |rb - u1 * D|) ^ 2 < (1 + x1) ^ 2 :=
      pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    rw [mul_pow, sq_abs, hx1_def] at hsq; linarith
  have hQm_pos : 0 < pairQm u1 u2 rb D := by
    unfold pairQm
    have h1 : u2 * (rb + u1 * D) = x2 + P - x1 * x2 := by
      rw [hx1_def, hx2_def, hP_def, hD_def]; ring
    have h2 : (1 - x1) - (x2 + P - x1 * x2) = detM := by rw [hdetM_def]; ring
    have hnn : 0 ≤ u2 * (rb + u1 * D) := by positivity
    have hsq : (u2 * (rb + u1 * D)) ^ 2 < (1 - x1) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) hnn two_ne_zero
    rw [mul_pow, hx1_def] at hsq; linarith
  have h1pu1 : 0 < 1 + u1 * rb := by rwa [← hx1_def]
  have h1mu1 : 0 < 1 - u1 * rb := by rwa [← hx1_def]
  have hcxe_nn : 0 ≤ cxe := by rw [hcxe_def]; unfold pairCxe; positivity
  have hacx_nn : 0 ≤ pairAbsCx2 u1 u2 rb vy D := by unfold pairAbsCx2; positivity
  have hace_nn : 0 ≤ pairAbsCe2 u1 u2 rb vx D := by unfold pairAbsCe2; positivity
  let acx := pairAbsCx2 u1 u2 rb vy D
  let ace := pairAbsCe2 u1 u2 rb vx D
  let g : ℝ × ℝ → ℝ := fun q =>
    acx * q.1 ^ 2 + ace * q.2 ^ 2 + cxe * (|q.1| * |q.2|) +
      (if |q.2| < k2 * |q.1| then tail_cx * q.1 ^ 2 else 0) +
      (if |q.1| < k1 * |q.2| then tail_ce * q.2 ^ 2 else 0)
  have hm1 : Integrable (fun x : E => ⟪w_u, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w_u) ▸
      integrable_sq_gaussianReal (‖w_u‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hm2 : Integrable (fun x : E => ⟪w_v, x⟫ ^ 2) (stdGaussian E) :=
    ((stdGaussian_map_inner (E := E) w_v) ▸
      integrable_sq_gaussianReal (‖w_v‖₊ ^ 2)).comp_measurable (by fun_prop)
  have hind1_eq : (fun x : E => if |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫| then tail_cx * ⟪w_u, x⟫ ^ 2
      else 0) = fun x => tail_cx * ({x : E | |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫|}).indicator
        (fun x => ⟪w_u, x⟫ ^ 2) x := by
    funext x
    by_cases hx : |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫| <;>
      simp only [mem_ofPred_eq, hx, ↓reduceIte, not_false_eq_true, indicator_of_mem,
        indicator_of_notMem, mul_zero]
  have hind2_eq : (fun x : E => if |⟪w_u, x⟫| < k1 * |⟪w_v, x⟫| then tail_ce * ⟪w_v, x⟫ ^ 2
      else 0) = fun x => tail_ce * ({x : E | |⟪w_u, x⟫| < k1 * |⟪w_v, x⟫|}).indicator
        (fun x => ⟪w_v, x⟫ ^ 2) x := by
    funext x
    by_cases hx : |⟪w_u, x⟫| < k1 * |⟪w_v, x⟫| <;>
      simp only [mem_ofPred_eq, hx, ↓reduceIte, not_false_eq_true, indicator_of_mem,
        indicator_of_notMem, mul_zero]
  have hi_ind1 : Integrable (fun x : E => ({x : E | |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫|}).indicator
      (fun x => ⟪w_u, x⟫ ^ 2) x) (stdGaussian E) :=
    hm1.indicator (measurableSet_lt (by fun_prop) (by fun_prop))
  have hi_ind2 : Integrable (fun x : E => ({x : E | |⟪w_u, x⟫| < k1 * |⟪w_v, x⟫|}).indicator
      (fun x => ⟪w_v, x⟫ ^ 2) x) (stdGaussian E) :=
    hm2.indicator (measurableSet_lt (by fun_prop) (by fun_prop))
  have h12 : Integrable (fun x : E => acx * ⟪w_u, x⟫ ^ 2 + ace * ⟪w_v, x⟫ ^ 2) (stdGaussian E) :=
    (hm1.const_mul acx).add (hm2.const_mul ace)
  have hbase : Integrable (fun x : E => acx * ⟪w_u, x⟫ ^ 2 + ace * ⟪w_v, x⟫ ^ 2 +
      cxe * (|⟪w_u, x⟫| * |⟪w_v, x⟫|)) (stdGaussian E) :=
    h12.add ((integrable_abs_mul_abs_inner w_u w_v).const_mul cxe)
  have hb_i1 : Integrable (fun x : E => acx * ⟪w_u, x⟫ ^ 2 + ace * ⟪w_v, x⟫ ^ 2 +
      cxe * (|⟪w_u, x⟫| * |⟪w_v, x⟫|) +
      tail_cx * ({x : E | |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫|}).indicator (fun x => ⟪w_u, x⟫ ^ 2) x)
      (stdGaussian E) :=
    hbase.add (hi_ind1.const_mul tail_cx)
  have hg_int : Integrable (fun x => g (⟪w_u, x⟫, ⟪w_v, x⟫)) (stdGaussian E) := by
    refine (hb_i1.add (hi_ind2.const_mul tail_ce)).congr (ae_of_all _ fun x => ?_)
    dsimp only [g, Pi.add_apply]
    rw [← congr_fun hind1_eq x, ← congr_fun hind2_eq x]
  have hD_p : 0 < ‖p_x‖ ^ 2 * ‖p_y‖ ^ 2 - ⟪p_x, p_y⟫ ^ 2 := by rwa [hpx, hpy, hpxy, ← hD_def]
  have hcond := measureReal_planarRect_cond_le (b1 := u1) (b2 := u2) (rb := rb) (vx := vx)
    (vy := vy) ho_1 ho_2 ho_3 ho_4 hD_p hg_int
    (fun q => by
      dsimp only [g, acx, ace]
      have t1 : 0 ≤ (if |q.2| < k2 * |q.1| then tail_cx * q.1 ^ 2 else 0) := by
        split_ifs <;> positivity
      have t2 : 0 ≤ (if |q.1| < k1 * |q.2| then tail_ce * q.2 ^ 2 else 0) := by
        split_ifs <;> positivity
      positivity) fun ξ η => by
      have hv := volume_planarRectSet_le_in hrb hvx_nn hvy_nn
        (by rwa [habs_u1, ← hx1_def]) (by rwa [habs_u2, ← hx2_def]) hvxy
        (by rwa [habs_u1, habs_u2, ← hx1_def, ← hx2_def, ← hP_def, ← hdetM2_def]) ξ η
      simpa only [habs_u1, habs_u2, ← hD_def, ← hx1_def, ← hx2_def, ← hP_def, ← hdetM_def,
        ← hdetM2_def, ← hk2_def, ← hk1_def, ← hcxe_def, ← hcxm_def, ← hcem_def, ← hcAB_def,
        ← htcx_def, ← htce_def, g, acx, ace] using hv
  have hset_eq : {x : E | |⟪p_x, x⟫| < |⟪d_x, x⟫| ∧ |⟪p_y, x⟫| < |⟪d_y, x⟫|} =
      {x : E | (⟪p_x, x⟫, ⟪p_y, x⟫) ∈ planarRectSet u1 u2 rb vx vy ⟪w_u, x⟫ ⟪w_v, x⟫} := by
    ext x; exact hiff x
  rw [pairCost_zero_eq_ch_add_half_rect hu, hset_eq]
  have hdetK_uv : 0 < ‖w_u‖ ^ 2 * ‖w_v‖ ^ 2 - ⟪w_u, w_v⟫ ^ 2 := by
    rwa [hwu_sq, hwv_sq, hwuv, ← hdetK_def]
  have hdetK_vu : 0 < ‖w_v‖ ^ 2 * ‖w_u‖ ^ 2 - ⟪w_v, w_u⟫ ^ 2 := by
    have c : ⟪w_v, w_u⟫ = ⟪w_u, w_v⟫ := real_inner_comm _ _
    rw [mul_comm (‖w_v‖ ^ 2), c]; exact hdetK_uv
  have htail1 := integral_sq_indicator_abs_lt_le hk2_nn hdetK_uv
  have htail2 := integral_sq_indicator_abs_lt_le hk1_nn hdetK_vu
  have c_vu : ⟪w_v, w_u⟫ = ⟪w_u, w_v⟫ := real_inner_comm _ _
  rw [mul_comm (‖w_v‖ ^ 2), c_vu] at htail2
  have hg_eval : ∫ x, g (⟪w_u, x⟫, ⟪w_v, x⟫) ∂stdGaussian E ≤
      (acx + tail_cx * (4 * k2 * K00 / (π * √detK))) * K00 +
        (ace + tail_ce * (4 * k1 * K11 / (π * √detK))) * K11 +
        cxe * (C_ex * √(K00 * K11)) := by
    have hfun : (fun x => g (⟪w_u, x⟫, ⟪w_v, x⟫)) = fun x =>
        acx * ⟪w_u, x⟫ ^ 2 + ace * ⟪w_v, x⟫ ^ 2 + cxe * (|⟪w_u, x⟫| * |⟪w_v, x⟫|) +
          tail_cx * ({x : E | |⟪w_v, x⟫| < k2 * |⟪w_u, x⟫|}).indicator (fun x => ⟪w_u, x⟫ ^ 2) x +
          tail_ce * ({x : E | |⟪w_u, x⟫| < k1 * |⟪w_v, x⟫|}).indicator
            (fun x => ⟪w_v, x⟫ ^ 2) x := by
      funext x; dsimp only [g]; rw [congr_fun hind1_eq x, congr_fun hind2_eq x]
    rw [hfun, integral_add hb_i1 (hi_ind2.const_mul tail_ce),
      integral_add hbase (hi_ind1.const_mul tail_cx),
      integral_add h12 ((integrable_abs_mul_abs_inner w_u w_v).const_mul cxe),
      integral_add (hm1.const_mul acx) (hm2.const_mul ace),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_sq_inner_stdGaussian, integral_sq_inner_stdGaussian]
    have hc_le := hcorr w_u w_v hwu_sq hwv_sq hwuv
    rw [hwu_sq, hwv_sq, hwuv, ← hdetK_def] at htail1 htail2
    rw [hwu_sq, hwv_sq] at hc_le ⊢
    have hm_t1 := mul_le_mul_of_nonneg_left htail1 htcx_nn
    have hm_t2 := mul_le_mul_of_nonneg_left htail2 htce_nn
    have hm_cx := mul_le_mul_of_nonneg_left hc_le hcxe_nn
    have hr1 : tail_cx * (4 * k2 * K00 ^ 2 / (π * √detK)) =
        tail_cx * (4 * k2 * K00 / (π * √detK)) * K00 := by ring
    have hr2 : tail_ce * (4 * k1 * K11 ^ 2 / (π * √detK)) =
        tail_ce * (4 * k1 * K11 / (π * √detK)) * K11 := by ring
    linarith
  rw [hpx, hpy, hpxy, ← hD_def] at hcond
  have hpiD : 0 < 2 * π * √D := by have := pi_pos; have := sqrt_pos.mpr hD; positivity
  have hstep := hcond.trans (div_le_div_of_nonneg_right hg_eval hpiD.le)
  dsimp only [acx, ace] at hstep
  have hhalf : 1 / 2 * (((pairAbsCx2 u1 u2 rb vy D + tail_cx * (4 * k2 * K00 / (π * √detK))) * K00 +
        (pairAbsCe2 u1 u2 rb vx D + tail_ce * (4 * k1 * K11 / (π * √detK))) * K11 +
        cxe * (C_ex * √(K00 * K11))) / (2 * π * √D)) =
      ((pairAbsCx2 u1 u2 rb vy D + tail_cx * (4 * k2 * K00 / (π * √detK))) * K00 +
        (pairAbsCe2 u1 u2 rb vx D + tail_ce * (4 * k1 * K11 / (π * √detK))) * K11 +
        cxe * (C_ex * √(K00 * K11))) / (4 * π * √D) := by ring
  linarith

theorem pairCost_zero_le_planar_in {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1)
    (ho1 : 0 ≤ pairO1 u) (ho2 : 0 ≤ pairO2 u) (hrb : 0 < pairRb u)
    {C_ex : ℝ} (_hC_ex : 0 ≤ C_ex)
    (hD : 0 < (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)
    (hx1 : pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u < 1)
    (hx2 : pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
      pairRb u < 1)
    (hvxy : (1 + pairSab u) / 2 * ((1 + pairScd u) / 2) ≤ 2 * pairRb u ^ 2)
    (hdetM2 : 0 <
      (1 - pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) *
      (1 - pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) * pairRb u) -
      2 * (pairO1 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) *
        (pairO2 u / ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 + pairSab u) / 2) * ((1 + pairScd u) / 2)))
    (hdetK : 0 <
      ((1 - pairSab u) / 2 - pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) *
        ((1 - pairScd u) / 2 - pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) -
      (pairTau u + pairO1 u * pairO2 u * pairRb u /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2)) ^ 2)
    (hcorr : ∀ w_u w_v : E,
      ‖w_u‖ ^ 2 = (1 - pairSab u) / 2 - pairO1 u ^ 2 * ((1 + pairSab u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ‖w_v‖ ^ 2 = (1 - pairScd u) / 2 - pairO2 u ^ 2 * ((1 + pairScd u) / 2) /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ⟪w_u, w_v⟫ = pairTau u + pairO1 u * pairO2 u * pairRb u /
          ((1 + pairSab u) / 2 * ((1 + pairScd u) / 2) - pairRb u ^ 2) →
      ∫ x, |⟪w_u, x⟫| * |⟪w_v, x⟫| ∂stdGaussian E ≤ C_ex * √(‖w_u‖ ^ 2 * ‖w_v‖ ^ 2)) :
    let vx := (1 + pairSab u) / 2
    let vy := (1 + pairScd u) / 2
    let rb := pairRb u
    let D := vx * vy - rb ^ 2
    let u1 := pairO1 u / D
    let u2 := pairO2 u / D
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM := (1 - x1) * (1 - x2) - P
    let detM2 := (1 - x1) * (1 - x2) - 2 * P
    let k2 := u2 * vy * (1 - x2) / detM2
    let k1 := u1 * vx * (1 - x1) / detM2
    let cxe := pairCxe u1 u2 rb D
    let cxm := pairCxMax u2 vy x1 x2 detM
    let cem := pairCxMax u1 vx x2 x1 detM
    let cAB := pairCAB x1 x2 P detM
    let tail_cx := cxm + max 0 (cAB - cxe) * k2 + cem * k2 ^ 2
    let tail_ce := cem + max 0 (cAB - cxe) * k1 + cxm * k1 ^ 2
    let K00 := (1 - pairSab u) / 2 - pairO1 u ^ 2 * vx / D
    let K11 := (1 - pairScd u) / 2 - pairO2 u ^ 2 * vy / D
    let K01 := pairTau u + pairO1 u * pairO2 u * rb / D
    let detK := K00 * K11 - K01 ^ 2
    pairCost u 0 ≤
      (arccos ⟪u 0, u 1⟫ + arccos ⟪u 2, u 3⟫) / (2 * π) +
      (arccos ⟪u 0, u 2⟫ + arccos ⟪u 1, u 3⟫ + arccos ⟪u 0, u 3⟫ + arccos ⟪u 1, u 2⟫) / (4 * π) +
      ((pairAbsCx2 u1 u2 rb vy D + tail_cx * (4 * k2 * K00 / (π * √detK))) * K00 +
        (pairAbsCe2 u1 u2 rb vx D + tail_ce * (4 * k1 * K11 / (π * √detK))) * K11 +
        cxe * (C_ex * √(K00 * K11))) / (4 * π * √D) :=
  pairCost_zero_le_planar_in_aux hu ho1 ho2 hrb hD hx1 hx2 hvxy hdetM2 hdetK hcorr
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end PlanarAndMoments

/-! ### Part 5: Elementary real algebraic helpers for `chkPlanar` and `clampBox` -/

theorem inv_sqrt_le_secant {D D_lo slo shi c_inv : ℝ}
    (hslo : 0 < slo) (hD_lo : slo ^ 2 ≤ D_lo) (hle : D_lo ≤ D) (hshi : √D ≤ shi)
    (hc_nn : 0 ≤ c_inv) (hc_le : c_inv ≤ 1 / (slo * shi * (slo + shi))) :
    1 / √D ≤ 1 / slo - c_inv * (D - D_lo) := by
  have hD_pos : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hslo) (hD_lo.trans hle)
  have hsD : 0 < √D := sqrt_pos.mpr hD_pos
  have hslo_le_sD : slo ≤ √D := by
    have := sqrt_le_sqrt (hD_lo.trans hle)
    rwa [sqrt_sq hslo.le] at this
  have hshi_pos : 0 < shi := lt_of_lt_of_le hsD hshi
  have hden_le : √D * slo * (√D + slo) ≤ slo * shi * (slo + shi) := by
    have h1 : √D * slo ≤ slo * shi := by nlinarith
    have h2 : √D + slo ≤ slo + shi := by linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hcinv2 : c_inv ≤ 1 / (√D * slo * (√D + slo)) :=
    hc_le.trans (one_div_le_one_div_of_le (by positivity) hden_le)
  have hmul : c_inv * (D - D_lo) ≤ (D - slo ^ 2) / (√D * slo * (√D + slo)) := by
    calc c_inv * (D - D_lo)
        ≤ c_inv * (D - slo ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hc_nn
      _ ≤ 1 / (√D * slo * (√D + slo)) * (D - slo ^ 2) :=
          mul_le_mul_of_nonneg_right hcinv2 (by linarith)
      _ = (D - slo ^ 2) / (√D * slo * (√D + slo)) := one_div_mul_eq_div _ _
  have hid : 1 / slo - 1 / √D = (D - slo ^ 2) / (√D * slo * (√D + slo)) := by
    have hsq : √D ^ 2 = D := sq_sqrt hD_pos.le
    field_simp [hslo.ne', hsD.ne', (by positivity : √D + slo ≠ 0)]
    nlinarith
  linarith

theorem inv_D_sqrt_ge_tangent {D sm inv2sm5 : ℝ}
    (hD : 0 < D) (hsm : 0 < sm) (h35 : 3 * D ≤ 5 * sm ^ 2)
    (_hinv_nn : 0 ≤ inv2sm5) (hinv_le : inv2sm5 ≤ 1 / (2 * sm ^ 5)) :
    inv2sm5 * (5 * sm ^ 2 - 3 * D) ≤ 1 / (D * √D) := by
  set t := √D
  have ht : 0 < t := sqrt_pos.mpr hD
  have htsq : t ^ 2 = D := sq_sqrt hD.le
  have hpoly : 0 ≤ 3 * t ^ 5 - 5 * t ^ 3 * sm ^ 2 + 2 * sm ^ 5 := by
    have hid : 3 * t ^ 5 - 5 * t ^ 3 * sm ^ 2 + 2 * sm ^ 5 =
        (t - sm) ^ 2 * (3 * t ^ 3 + 6 * t ^ 2 * sm + 4 * t * sm ^ 2 + 2 * sm ^ 3) := by ring
    rw [hid]
    exact mul_nonneg (sq_nonneg _) (by positivity)
  have hdiv : (5 * sm ^ 2 - 3 * D) / (2 * sm ^ 5) ≤ 1 / (D * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hrew : (5 * sm ^ 2 - 3 * D) * (D * t) = 5 * t ^ 3 * sm ^ 2 - 3 * t ^ 5 := by
      rw [← htsq]; ring
    linarith
  calc inv2sm5 * (5 * sm ^ 2 - 3 * D)
      ≤ 1 / (2 * sm ^ 5) * (5 * sm ^ 2 - 3 * D) :=
        mul_le_mul_of_nonneg_right hinv_le (by linarith)
    _ = (5 * sm ^ 2 - 3 * D) / (2 * sm ^ 5) := one_div_mul_eq_div _ _
    _ ≤ 1 / (D * √D) := hdiv

private theorem schurPairIneq_linear_rhs_aux
    {c2 sab scd rbar tau0 A1 A2 D1 M11 M12 M21 M22 X2 σ rhs : ℝ}
    (h : (A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * X2 ≤ (A2 * M11 * M12 + A1 * M21 * M22) ^ 2)
    (ha1 : 0 ≤ A1) (ha2 : 0 < A2) (hx2 : 0 < X2)
    (hden : 0 < c2 - (sab + scd) / 2 + M11)
    (hrhs : (((sab - scd) / 2) ^ 2 + A1 * M21 ^ 2 / A2 +
        (A2 * |M11| * |M12| + A1 * |M21| * |M22|) ^ 2 / (A2 * X2)) /
      (c2 - (sab + scd) / 2 + M11) ≤ rhs)
    (hA1 : A1 = c2 - sab) (hD1 : D1 = c2 - scd)
    (hM11 : M11 = 2 * (3 / 14 * rbar + σ * (8 / 35) * tau0)) :
    0 ≤ (sab + scd) / 2 + 3 / 7 * rbar + σ * (16 / 35) * tau0 - c2 + rhs := by
  have hy_sq : (A2 * M11 * M12 + A1 * M21 * M22) ^ 2 ≤
      (A2 * |M11| * |M12| + A1 * |M21| * |M22|) ^ 2 := by
    have habs : |A2 * M11 * M12 + A1 * M21 * M22| ≤
        A2 * |M11| * |M12| + A1 * |M21| * |M22| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (A2 * M11) M12, abs_mul A2 M11, abs_mul (A1 * M21) M22, abs_mul A1 M21,
        abs_of_pos ha2, abs_of_nonneg ha1]
    have hnn : 0 ≤ A2 * |M11| * |M12| + A1 * |M21| * |M22| := by positivity
    exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) habs 2)
  have h1 := h.trans hy_sq
  have ha2x2 : 0 < A2 * X2 := mul_pos ha2 hx2
  have h2 : A1 * D1 - M11 ^ 2 ≤
      A1 * M21 ^ 2 / A2 + (A2 * |M11| * |M12| + A1 * |M21| * |M22|) ^ 2 / (A2 * X2) := by
    rw [div_add_div _ _ ha2.ne' ha2x2.ne', le_div_iff₀ (mul_pos ha2 ha2x2)]
    have hid : (A1 * D1 - M11 ^ 2) * (A2 * (A2 * X2)) =
        A1 * M21 ^ 2 * (A2 * X2) + A2 * ((A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * X2) := by ring
    rw [hid]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 ha2.le)
  have had_id : (c2 - (sab + scd) / 2 - M11) * (c2 - (sab + scd) / 2 + M11) =
      A1 * D1 - M11 ^ 2 + ((sab - scd) / 2) ^ 2 := by
    rw [hA1, hD1]; ring
  have h3 : (c2 - (sab + scd) / 2 - M11) * (c2 - (sab + scd) / 2 + M11) ≤
      ((sab - scd) / 2) ^ 2 + A1 * M21 ^ 2 / A2 +
        (A2 * |M11| * |M12| + A1 * |M21| * |M22|) ^ 2 / (A2 * X2) := by
    rw [had_id]; linarith [h2]
  have h4 := ((le_div_iff₀ hden).mpr h3).trans hrhs
  have hm11_eq : M11 = 3 / 7 * rbar + σ * (16 / 35) * tau0 := by rw [hM11]; ring
  linarith [h4, hm11_eq]

theorem schurPairIneq_linear_rhs {sab scd sac sbd sad sbc σ rhs : ℝ}
    (h : schurPairIneq sab scd sac sbd sad sbc σ)
    (ha1 : 0 ≤ 1322905 / 1000000 - sab)
    (ha2 : 0 < 1322905 / 1000000 + sab)
    (_hm11 : 0 < 2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
      σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4)))
    (hx2 : 0 < (1322905 / 1000000 + sab) *
        ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
            σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) ^ 2) -
      (1322905 / 1000000 - sab) *
        (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
          σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4))) ^ 2)
    (hden : 0 < 1322905 / 1000000 - (sab + scd) / 2 +
      2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
        σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4)))
    (hrhs : (((sab - scd) / 2) ^ 2 +
        (1322905 / 1000000 - sab) *
          (2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
            σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))) ^ 2 / (1322905 / 1000000 + sab) +
        ((1322905 / 1000000 + sab) *
            |2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
              σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))| *
            |2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
              σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))| +
          (1322905 / 1000000 - sab) *
            |2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
              σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4))| *
            |2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
              σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4))|) ^ 2 /
          ((1322905 / 1000000 + sab) *
            ((1322905 / 1000000 + sab) *
              ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
                (2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
                  σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4))) ^ 2) -
            (1322905 / 1000000 - sab) *
              (2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
                σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4))) ^ 2))) /
      (1322905 / 1000000 - (sab + scd) / 2 +
        2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
          σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4))) ≤ rhs) :
    0 ≤ (sab + scd) / 2 + 3 / 7 * ((sac + sbd + sad + sbc) / 4) +
      σ * (16 / 35) * ((sac + sbd - sad - sbc) / 4) - 1322905 / 1000000 + rhs :=
  schurPairIneq_linear_rhs_aux h ha1 ha2 hx2 hden hrhs rfl rfl rfl

end Cslib.Circuits.Frontier.Gaussian.PairBound
