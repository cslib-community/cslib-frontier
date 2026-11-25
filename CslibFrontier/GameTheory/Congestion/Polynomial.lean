/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Basic
public import CslibFrontier.GameTheory.Strategic.SmoothHierarchy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smoothness and price of anarchy of polynomial atomic congestion games

An atomic congestion game has **degree-`d` polynomial latencies** (`HasPolynomialLatencies d`) if
every resource latency has the form `latency e k = ∑ j ∈ range (d + 1), c e j * k ^ j` with
nonnegative coefficients `c e j ≥ 0` ([Roughgarden2015], Example 2.5;
[AlandDumraufGairingMonienSchoppmann2006]), generalizing the `d = 1` affine case of
[ChristodoulouKoutsoupias2005].

We prove two complementary smoothness theorems:

1. **General degree `d ≥ 1` (`isSmooth_of_hasPolynomialLatencies`)**: let `φ_d = polynomialRoot d`
   be the unique root `φ > 1` of `φ ^ (d + 1) = (1 + φ) ^ d` ([AwerbuchAzarEpstein2005];
   [AlandDumraufGairingMonienSchoppmann2006]). Every atomic congestion game with degree-`d`
   polynomial latencies is `(polynomialSmoothLam d, polynomialSmoothMu d)`-smooth with ratio
   `polynomialSmoothLam d / (1 - polynomialSmoothMu d) = φ_d ^ (d + 1) < (d + 1) ^ (d + 1)`,
   yielding a `d^{O(d)}` robust price-of-anarchy bound across pure Nash, mixed Nash, correlated,
   coarse correlated, and incomplete-information Bayes–Nash equilibria.
2. **Exact quadratic (`d = 2`) unweighted bound (`isSmooth_quadratic`,
   `exists_socialCost_eq_quadratic_poa`)**: on natural numbers,
   `y * (z + 1) ^ 2 ≤ 115 / 19 * y ^ 3 + 7 / 19 * z ^ 3`, so every unweighted congestion game with
   nonnegative quadratic latencies (`HasPolynomialLatencies 2`) is `(115 / 19, 7 / 19)`-smooth with
   exact robust price of anarchy `115 / 12` ([AlandDumraufGairingMonienSchoppmann2006]), attained
   by an explicit symmetric four-player, eight-resource pure Nash witness.

## Main definitions

* `Cslib.GameTheory.CongestionGame.HasPolynomialLatencies`: nonnegative polynomial latencies of
  degree at most `d`.
* `Cslib.GameTheory.CongestionGame.polynomialRoot`,
  `Cslib.GameTheory.CongestionGame.polynomialSmoothLam`,
  `Cslib.GameTheory.CongestionGame.polynomialSmoothMu`: the root `φ_d` of
  `φ ^ (d + 1) = (1 + φ) ^ d` and its `(λ_d, μ_d)` smoothness parameters.

## Main results

* `Cslib.GameTheory.CongestionGame.existsUnique_polynomialRoot`,
  `Cslib.GameTheory.CongestionGame.polynomialRoot_lt_succ`: existence, uniqueness, and
  `1 < φ_d < d + 1` bound for the characteristic root `φ_d`.
* `Cslib.GameTheory.CongestionGame.mul_add_pow_le_polynomialSmooth`: for `d ≥ 1` and `x, z ≥ 0`,
  `x * (z + x) ^ d ≤ polynomialSmoothLam d * x ^ (d + 1) + polynomialSmoothMu d * z ^ (d + 1)`.
* `Cslib.GameTheory.CongestionGame.isSmooth_of_hasPolynomialLatencies`,
  `Cslib.GameTheory.CongestionGame.expected_socialCost_le_of_hasPolynomialLatencies`,
  `Cslib.GameTheory.CongestionGame.expected_socialCost_le_succ_pow_of_hasPolynomialLatencies`:
  general degree-`d` `(λ_d, μ_d)`-smoothness and `φ_d ^ (d + 1) ≤ (d + 1) ^ (d + 1)` robust price
  of anarchy.
* `Cslib.GameTheory.CongestionGame.mul_add_one_sq_le_quadraticSmooth`,
  `Cslib.GameTheory.CongestionGame.isSmooth_quadratic`,
  `Cslib.GameTheory.CongestionGame.expected_socialCost_le_quadratic`,
  `Cslib.GameTheory.CongestionGame.exists_socialCost_eq_quadratic_poa`: exact `(115 / 19, 7 / 19)`
  quadratic smoothness, `115 / 12` price of anarchy, and four-player tightness witness.

## References

* [AlandDumraufGairingMonienSchoppmann2006]
* [AwerbuchAzarEpstein2005]
* [ChristodoulouKoutsoupias2005]
* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory.CongestionGame

open Finset

section CharacteristicRoot

private theorem exp_one_le_four : Real.exp 1 ≤ 4 := by
  have h1 : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by linarith [Real.add_one_le_exp (-1 / 2 : ℝ)]
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (1 / 2)).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    linarith
  have h3 := mul_le_mul h2 h2 (Real.exp_pos _).le (by norm_num)
  rw [← Real.exp_add] at h3
  norm_num at h3
  exact h3

private theorem add_two_pow_lt_add_one_pow_succ {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) + 2) ^ d < ((d : ℝ) + 1) ^ (d + 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd2
  · norm_num
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd2) with rfl | hd3
  · norm_num
  set u : ℝ := (d : ℝ) + 1
  have hu4 : 4 ≤ u := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_of_lt hd3
    linarith
  have hu_pos : 0 < u := by linarith
  have hpow : (1 + 1 / u) ^ d ≤ Real.exp (d * (1 / u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / u)]) d
  have hexp_lt : (1 + 1 / u) ^ d < u :=
    (hpow.trans_lt (Real.exp_lt_exp.2 (by rw [mul_one_div, div_lt_one hu_pos]; linarith))).trans_le
      (exp_one_le_four.trans hu4)
  have hdiv : (d : ℝ) + 2 = u * (1 + 1 / u) := by
    dsimp [u]
    field_simp [hu_pos.ne']
    ring
  rw [hdiv, mul_pow, pow_succ]
  exact mul_lt_mul_of_pos_left hexp_lt (pow_pos hu_pos d)

private theorem pow_succ_mul_one_add_pow_lt {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a ^ (d + 1) * (1 + b) ^ d < b ^ (d + 1) * (1 + a) ^ d := by
  have hb : 0 < b := ha.trans hab
  have h1b : 0 < 1 + b := by linarith
  have hpow : a ^ d * (1 + b) ^ d ≤ b ^ d * (1 + a) ^ d := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg ha.le h1b.le) (by linarith) d
  calc a ^ (d + 1) * (1 + b) ^ d
      = a * (a ^ d * (1 + b) ^ d) := by ring
    _ < b * (a ^ d * (1 + b) ^ d) := mul_lt_mul_of_pos_right hab (by positivity)
    _ ≤ b * (b ^ d * (1 + a) ^ d) := mul_le_mul_of_nonneg_left hpow hb.le
    _ = b ^ (d + 1) * (1 + a) ^ d := by ring

/-- For every degree `d ≥ 1`, there is a unique real `φ > 0` satisfying `φ ^ (d + 1) = (1 + φ) ^ d`,
and it lies strictly between `1` and `d + 1`. -/
theorem existsUnique_polynomialRoot {d : ℕ} (hd : 1 ≤ d) :
    ∃! φ : ℝ, 0 < φ ∧ φ ^ (d + 1) = (1 + φ) ^ d := by
  let f : ℝ → ℝ := fun x => (1 + x) ^ d - x ^ (d + 1)
  have hf_cont : ContinuousOn f (Set.Icc 1 ((d : ℝ) + 1)) :=
    (((continuous_const.add continuous_id).pow d).sub (continuous_id.pow (d + 1))).continuousOn
  have hf1 : 0 < f 1 := by
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    dsimp [f]
    norm_num at h2 ⊢
    linarith
  have hfd : f ((d : ℝ) + 1) < 0 := by
    dsimp [f]; rw [show 1 + ((d : ℝ) + 1) = (d : ℝ) + 2 by ring]
    linarith [add_two_pow_lt_add_one_pow_succ hd]
  obtain ⟨φ, hφ_mem, hφ_zero⟩ := intermediate_value_Icc'
    (by linarith [Nat.cast_nonneg (α := ℝ) d]) hf_cont ⟨hfd.le, hf1.le⟩
  have hφ_pos : 0 < φ := zero_lt_one.trans_le hφ_mem.1
  have hφ_eq : φ ^ (d + 1) = (1 + φ) ^ d := by dsimp [f] at hφ_zero; linarith
  refine ⟨φ, ⟨hφ_pos, hφ_eq⟩, fun y ⟨hy_pos, hy_eq⟩ => ?_⟩
  rcases lt_trichotomy y φ with hlt | rfl | hgt
  · have h := pow_succ_mul_one_add_pow_lt (d := d) hy_pos hlt
    rw [hy_eq, hφ_eq, mul_comm] at h; exact absurd h (lt_irrefl _)
  · rfl
  · have h := pow_succ_mul_one_add_pow_lt (d := d) hφ_pos hgt
    rw [hφ_eq, hy_eq, mul_comm] at h; exact absurd h (lt_irrefl _)

/-- Characteristic root `φ_d` of `φ ^ (d + 1) = (1 + φ) ^ d` for `d ≥ 1` (and `1` for `d = 0`). -/
noncomputable def polynomialRoot (d : ℕ) : ℝ :=
  if hd : 1 ≤ d then Classical.choose (existsUnique_polynomialRoot hd).exists else 1

theorem polynomialRoot_pos (d : ℕ) : 0 < polynomialRoot d := by
  unfold polynomialRoot; split_ifs with hd
  · exact (Classical.choose_spec (existsUnique_polynomialRoot hd).exists).1
  · exact zero_lt_one

theorem polynomialRoot_pow_eq {d : ℕ} (hd : 1 ≤ d) :
    polynomialRoot d ^ (d + 1) = (1 + polynomialRoot d) ^ d := by
  rw [polynomialRoot, dite_eq_left hd]
  exact (Classical.choose_spec (existsUnique_polynomialRoot hd).exists).2

theorem polynomialRoot_gt_one {d : ℕ} (hd : 1 ≤ d) : 1 < polynomialRoot d := by
  by_contra! hle
  linarith [polynomialRoot_pow_eq hd, pow_le_one₀ (n := d + 1) (polynomialRoot_pos d).le hle,
    (one_lt_pow₀ (by linarith [polynomialRoot_pos d]) (by omega : d ≠ 0) :
      (1 : ℝ) < (1 + polynomialRoot d) ^ d)]

/-- For every `d ≥ 1`, the characteristic root satisfies `polynomialRoot d < d + 1`. -/
theorem polynomialRoot_lt_succ {d : ℕ} (hd : 1 ≤ d) : polynomialRoot d < (d : ℝ) + 1 := by
  by_contra! hge
  have hφ := polynomialRoot_pos d
  have hlt := add_two_pow_lt_add_one_pow_succ hd
  rcases eq_or_lt_of_le hge with heq | hgt
  · have h := polynomialRoot_pow_eq hd
    rw [← heq, show 1 + ((d : ℝ) + 1) = (d : ℝ) + 2 by ring] at h
    linarith
  · have h := pow_succ_mul_one_add_pow_lt (d := d) (by positivity) hgt
    rw [polynomialRoot_pow_eq hd, show 1 + ((d : ℝ) + 1) = (d : ℝ) + 2 by ring] at h
    have : 0 < (1 + polynomialRoot d) ^ d := by positivity
    nlinarith

theorem polynomialRoot_strictMono {j d : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    polynomialRoot j < polynomialRoot d := by
  by_contra! hge
  have hd : 1 ≤ d := by omega
  set φj := polynomialRoot j
  set φd := polynomialRoot d
  have hφd_pos : 0 < φd := polynomialRoot_pos d
  have hφj_pos : 0 < φj := polynomialRoot_pos j
  have hstep1 : φd ^ (j + 1) ≤ (1 + φd) ^ j := by
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [heq, polynomialRoot_pow_eq hj]
    · have h := pow_succ_mul_one_add_pow_lt (d := j) hφd_pos hlt
      rw [polynomialRoot_pow_eq hj] at h
      exact le_of_mul_le_mul_right (by linarith) (by positivity : 0 < (1 + φj) ^ j)
  obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ d = j + m := ⟨d - j, by omega, by omega⟩
  have hφd1 := polynomialRoot_gt_one hd
  have hlt_m : φd ^ m < (1 + φd) ^ m := pow_lt_pow_left₀ (by linarith) hφd_pos.le (by omega)
  have hstep2 : φd ^ (j + m + 1) < (1 + φd) ^ (j + m) :=
    calc φd ^ (j + m + 1) = φd ^ (j + 1) * φd ^ m := by ring
      _ ≤ (1 + φd) ^ j * φd ^ m := mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ < (1 + φd) ^ j * (1 + φd) ^ m := mul_lt_mul_of_pos_left hlt_m (by positivity)
      _ = (1 + φd) ^ (j + m) := (pow_add _ _ _).symm
  exact hstep2.ne (polynomialRoot_pow_eq hd)

/-- Smoothness parameter `λ_d` for degree-`d` polynomial congestion games (`1` for `d = 0`). -/
noncomputable def polynomialSmoothLam (d : ℕ) : ℝ :=
  if d = 0 then 1
  else ((d : ℝ) + 1 + polynomialRoot d) / (((d : ℝ) + 1) * (1 + polynomialRoot d)) *
    polynomialRoot d ^ (d + 1)

/-- Smoothness parameter `μ_d` for degree-`d` polynomial congestion games (`0` for `d = 0`). -/
noncomputable def polynomialSmoothMu (d : ℕ) : ℝ :=
  if d = 0 then 0
  else (d : ℝ) * polynomialRoot d / (((d : ℝ) + 1) * (1 + polynomialRoot d))

theorem polynomialSmoothMu_nonneg (d : ℕ) : 0 ≤ polynomialSmoothMu d := by
  unfold polynomialSmoothMu
  split_ifs
  · exact le_rfl
  · have := polynomialRoot_pos d
    positivity

theorem polynomialSmoothMu_lt_one (d : ℕ) : polynomialSmoothMu d < 1 := by
  unfold polynomialSmoothMu
  split_ifs
  · exact zero_lt_one
  · have := polynomialRoot_pos d
    rw [div_lt_one (by positivity)]
    nlinarith

theorem one_le_polynomialSmoothLam (d : ℕ) : 1 ≤ polynomialSmoothLam d := by
  unfold polynomialSmoothLam
  split_ifs with hd0
  · exact le_rfl
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd0
  have hφ1 : 1 < polynomialRoot d := polynomialRoot_gt_one hd
  have hpow : 1 + polynomialRoot d ≤ polynomialRoot d ^ (d + 1) := by
    rw [polynomialRoot_pow_eq hd]
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith) hd
  rw [div_mul_eq_mul_div, one_le_div (by positivity)]
  nlinarith [show (0 : ℝ) ≤ d by positivity]

/-- Exact smoothness ratio: for `d ≥ 1`,
`polynomialSmoothLam d / (1 - polynomialSmoothMu d) = polynomialRoot d ^ (d + 1)`. -/
theorem polynomialSmoothRatio_eq {d : ℕ} (hd : 1 ≤ d) :
    polynomialSmoothLam d / (1 - polynomialSmoothMu d) = polynomialRoot d ^ (d + 1) := by
  have hd0 : d ≠ 0 := by omega
  have hφ : 0 < polynomialRoot d := polynomialRoot_pos d
  unfold polynomialSmoothLam polynomialSmoothMu
  simp only [hd0, ↓reduceIte]
  have hden1 : ((d : ℝ) + 1) * (1 + polynomialRoot d) ≠ 0 := by positivity
  have h1mu : 1 - (d : ℝ) * polynomialRoot d / (((d : ℝ) + 1) * (1 + polynomialRoot d)) =
      ((d : ℝ) + 1 + polynomialRoot d) / (((d : ℝ) + 1) * (1 + polynomialRoot d)) := by
    field_simp; ring
  rw [h1mu]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem polynomialSmoothMu_mono {j d : ℕ} (hjd : j ≤ d) :
    polynomialSmoothMu j ≤ polynomialSmoothMu d := by
  rcases eq_or_lt_of_le hjd with rfl | hlt
  · exact le_rfl
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [polynomialSmoothMu, ↓reduceIte]
    exact polynomialSmoothMu_nonneg d
  have hφ_lt := polynomialRoot_strictMono hj hlt
  have hφj := polynomialRoot_pos j
  have hφd := polynomialRoot_pos d
  have hj0 : j ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  unfold polynomialSmoothMu
  simp only [hj0, hd0, ↓reduceIte]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hjd' : (j : ℝ) ≤ d := Nat.cast_le.2 hjd
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) * d) (sub_nonneg.2 hφ_lt.le),
    mul_nonneg (sub_nonneg.2 hjd') (by positivity : 0 ≤ polynomialRoot j * polynomialRoot d),
    mul_le_mul hjd' hφ_lt.le hφj.le (by positivity)]

theorem polynomialSmoothLam_mono {j d : ℕ} (hjd : j ≤ d) :
    polynomialSmoothLam j ≤ polynomialSmoothLam d := by
  induction hjd with
  | refl => exact le_rfl
  | @step m hjm ih =>
    refine ih.trans ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp only [polynomialSmoothLam, ↓reduceIte]; exact one_le_polynomialSmoothLam 1
    have hm_succ : 1 ≤ m + 1 := by omega
    have hφm_lt := polynomialRoot_lt_succ hm1
    have hφ_inc := polynomialRoot_strictMono hm1 (Nat.lt_succ_self m)
    have hφm_gt1 := polynomialRoot_gt_one hm1
    have hφs_gt1 := polynomialRoot_gt_one hm_succ
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm1
    have hk0 : k + 1 ≠ 0 := by omega
    have hks0 : k + 1 + 1 ≠ 0 := by omega
    unfold polynomialSmoothLam
    simp only [hk0, hks0, ↓reduceIte,
      polynomialRoot_pow_eq hm1, polynomialRoot_pow_eq hm_succ]
    have h1m : 1 + polynomialRoot (k + 1) ≠ 0 := by linarith
    have h1s : 1 + polynomialRoot (k + 1 + 1) ≠ 0 := by linarith
    have hrew1 : (((k + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1)) /
        ((((k + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1))) *
        (1 + polynomialRoot (k + 1)) ^ (k + 1) =
        (1 + polynomialRoot (k + 1) / (((k + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1)) ^ k := by
      rw [pow_succ]; field_simp [show (((k + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
    have hrew2 : (((k + 1 + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1 + 1)) /
        ((((k + 1 + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1 + 1))) *
        (1 + polynomialRoot (k + 1 + 1)) ^ (k + 1 + 1) =
        (1 + polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1 + 1)) * (1 + polynomialRoot (k + 1 + 1)) ^ k := by
      rw [pow_succ, pow_succ]; field_simp [show (((k + 1 + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
    rw [hrew1, hrew2]
    have hcoef : 1 + polynomialRoot (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) ≤
        (1 + polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1 + 1)) := by
      have := (div_lt_one (by positivity)).2 hφm_lt
      have : 0 ≤ polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1) := by positivity
      nlinarith
    exact mul_le_mul hcoef (pow_le_pow_left₀ (by positivity) (by linarith) k)
      (by positivity) (by positivity)

/-! ### Division-free polynomial smoothness inequalities -/

private theorem pow_sub_mul_sub_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (k : ℕ) :
    0 ≤ (u ^ k - v ^ k) * (u - v) := by
  rcases le_total u v with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hu h k)) (sub_nonpos.2 h)
  · exact mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hv h k)) (sub_nonneg.2 h)

private theorem young_nat_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    ((d : ℝ) + 1) * a * b ^ d ≤ a ^ (d + 1) + (d : ℝ) * b ^ (d + 1) := by
  induction d with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_zero, pow_one, mul_one, zero_mul, add_zero, one_mul,
      le_refl]
  | succ k ih =>
    have hmon := pow_sub_mul_sub_nonneg ha hb (k + 1)
    have hdiff : 0 ≤ b * (a ^ (k + 1) + (k : ℝ) * b ^ (k + 1) - ((k : ℝ) + 1) * a * b ^ k) :=
      mul_nonneg hb (by linarith)
    push_cast
    linarith [show a ^ (k + 2) + ((k : ℝ) + 1) * b ^ (k + 2) - ((k : ℝ) + 2) * a * b ^ (k + 1) =
      b * (a ^ (k + 1) + (k : ℝ) * b ^ (k + 1) - ((k : ℝ) + 1) * a * b ^ k) +
      (a ^ (k + 1) - b ^ (k + 1)) * (a - b) by ring]

private theorem add_pow_weighted_bound {x z φ : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hφ : 0 ≤ φ) :
    ∀ m : ℕ, φ ^ m * (x + z) ^ (m + 1) ≤
      φ ^ m * (1 + φ) ^ m * x ^ (m + 1) + (1 + φ) ^ m * z ^ (m + 1)
  | 0 => by simp only [zero_add, pow_zero, pow_one, one_mul, le_refl]
  | m + 1 => by
    have ih := add_pow_weighted_bound hx hz hφ m
    have hmul : φ * (x + z) * (φ ^ m * (x + z) ^ (m + 1)) ≤
        φ * (x + z) * (φ ^ m * (1 + φ) ^ m * x ^ (m + 1) + (1 + φ) ^ m * z ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have hmon := pow_sub_mul_sub_nonneg (mul_nonneg hφ hx) hz (m + 1)
    have hgap : 0 ≤ (1 + φ) ^ m * (((φ * x) ^ (m + 1) - z ^ (m + 1)) * (φ * x - z)) :=
      mul_nonneg (by positivity) hmon
    linarith [show φ ^ (m + 1) * (1 + φ) ^ (m + 1) * x ^ (m + 2) +
        (1 + φ) ^ (m + 1) * z ^ (m + 2) -
        φ * (x + z) * (φ ^ m * (1 + φ) ^ m * x ^ (m + 1) + (1 + φ) ^ m * z ^ (m + 1)) =
        (1 + φ) ^ m * (((φ * x) ^ (m + 1) - z ^ (m + 1)) * (φ * x - z)) by ring,
      show φ * (x + z) * (φ ^ m * (x + z) ^ (m + 1)) = φ ^ (m + 1) * (x + z) ^ (m + 2) by ring]

/-- **Real polynomial smoothness inequality**: for every degree `d ≥ 1` and nonnegative reals
`x, z ≥ 0`,
`x * (z + x) ^ d ≤ polynomialSmoothLam d * x ^ (d + 1) + polynomialSmoothMu d * z ^ (d + 1)`. -/
theorem mul_add_pow_le_polynomialSmooth {d : ℕ} (hd : 1 ≤ d) {x z : ℝ} (hx : 0 ≤ x)
    (hz : 0 ≤ z) :
    x * (z + x) ^ d ≤
      polynomialSmoothLam d * x ^ (d + 1) + polynomialSmoothMu d * z ^ (d + 1) := by
  have hd0 : d ≠ 0 := by omega
  set φ := polynomialRoot d
  have hφ : 0 < φ := polynomialRoot_pos d
  have heq : φ ^ (d + 1) = (1 + φ) ^ d := polynomialRoot_pow_eq hd
  have hyoung := young_nat_pow (a := (1 + φ) * x) (b := z + x) (by positivity) (by positivity) d
  have hw := add_pow_weighted_bound hx hz hφ.le d
  rw [← heq] at hw
  have hw_cancel : (x + z) ^ (d + 1) ≤ φ ^ (d + 1) * x ^ (d + 1) + φ * z ^ (d + 1) := by
    refine le_of_mul_le_mul_left ?_ (pow_pos hφ d)
    linarith [show φ ^ d * (φ ^ (d + 1) * x ^ (d + 1) + φ * z ^ (d + 1)) =
      φ ^ d * φ ^ (d + 1) * x ^ (d + 1) + φ ^ (d + 1) * z ^ (d + 1) by ring]
  have hcomb : (x * (z + x) ^ d) * (((d : ℝ) + 1) * (1 + φ)) ≤
      ((d : ℝ) + 1 + φ) * φ ^ (d + 1) * x ^ (d + 1) + (d : ℝ) * φ * z ^ (d + 1) := by
    have h1 : ((1 + φ) * x) ^ (d + 1) = (1 + φ) * φ ^ (d + 1) * x ^ (d + 1) := by
      rw [mul_pow, pow_succ', ← heq]
    have h2 : (z + x) ^ (d + 1) = (x + z) ^ (d + 1) := by ring
    nlinarith
  unfold polynomialSmoothLam polynomialSmoothMu
  simp only [hd0, ↓reduceIte]
  have hden : 0 < ((d : ℝ) + 1) * (1 + φ) := by positivity
  have hdiv : x * (z + x) ^ d ≤
      (((d : ℝ) + 1 + φ) * φ ^ (d + 1) * x ^ (d + 1) + (d : ℝ) * φ * z ^ (d + 1)) /
        (((d : ℝ) + 1) * (1 + φ)) :=
    (le_div_iff₀ hden).2 hcomb
  refine hdiv.trans_eq ?_
  dsimp [φ] at hden ⊢
  have hden_ne : ((d : ℝ) + 1) * (1 + polynomialRoot d) ≠ 0 := hden.ne'
  field_simp

theorem nat_mul_add_one_pow_le_polynomialSmooth {j d : ℕ} (hjd : j ≤ d) (y z : ℕ) :
    (y : ℝ) * ((z : ℝ) + 1) ^ j ≤
      polynomialSmoothLam d * (y : ℝ) ^ (j + 1) + polynomialSmoothMu d * (z : ℝ) ^ (j + 1) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [Nat.cast_zero, zero_mul]
    have := polynomialSmoothMu_nonneg d
    have := one_le_polynomialSmoothLam d
    positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, zero_add, pow_one, mul_one]
    have hlam := one_le_polynomialSmoothLam d
    have hmu := polynomialSmoothMu_nonneg d
    nlinarith [show (0 : ℝ) ≤ y by positivity, show (0 : ℝ) ≤ z by positivity]
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hstep1 : (y : ℝ) * ((z : ℝ) + 1) ^ j ≤ (y : ℝ) * ((z : ℝ) + y) ^ j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) j) (by positivity)
  have hstep2 := mul_add_pow_le_polynomialSmooth (d := j) hj (x := (y : ℝ)) (z := (z : ℝ))
    (by positivity) (by positivity)
  have hlam := polynomialSmoothLam_mono hjd
  have hmu := polynomialSmoothMu_mono hjd
  exact (hstep1.trans hstep2).trans (add_le_add
    (mul_le_mul_of_nonneg_right hlam (by positivity))
    (mul_le_mul_of_nonneg_right hmu (by positivity)))

end CharacteristicRoot

section GeneralPolynomial

variable {ι : Type*} {S : ι → Type*} {E : Type*}

/-- `C` has **nonnegative polynomial latencies of degree at most `d`**: every latency has the form
`latency e k = ∑ j ∈ range (d + 1), c e j * k ^ j` with `c e j ≥ 0`
([Roughgarden2015], Example 2.5; [AlandDumraufGairingMonienSchoppmann2006]). -/
@[expose] def HasPolynomialLatencies (C : CongestionGame ι S E) (d : ℕ) : Prop :=
  ∃ c : E → ℕ → ℝ, (∀ e j, 0 ≤ c e j) ∧
    ∀ e k, C.latency e k = ∑ j ∈ range (d + 1), c e j * (k : ℝ) ^ j

theorem HasPolynomialLatencies.monotone_latency {C : CongestionGame ι S E} {d : ℕ}
    (h : C.HasPolynomialLatencies d) (e : E) : Monotone (C.latency e) := by
  obtain ⟨c, hc, hl⟩ := h
  intro k₁ k₂ hk
  rw [hl, hl]
  have hk' : (k₁ : ℝ) ≤ k₂ := Nat.cast_le.2 hk
  exact sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k₁) hk' j) (hc e j)

variable [Fintype ι] [DecidableEq ι] [DecidableEq E] [Finite E] {C : CongestionGame ι S E}

private theorem isSmooth_of_latency_bound {lam μ : ℝ}
    (hmono : ∀ e, Monotone (C.latency e))
    (he : ∀ e (y z : ℕ), (y : ℝ) * C.latency e (z + 1) ≤
      lam * ((y : ℝ) * C.latency e y) + μ * ((z : ℝ) * C.latency e z)) :
    C.toCostGame.IsSmooth lam μ := by
  have := Fintype.ofFinite E
  intro s s'
  calc ∑ i, C.toCostGame.cost i (Function.update s i (s' i))
      ≤ ∑ i, ∑ e ∈ C.resources i (s' i), C.latency e (C.load s e + 1) := by
        refine sum_le_sum fun i _ => ?_
        rw [toCostGame_cost, Function.update_self]
        exact sum_le_sum fun e _ => hmono e (C.load_update_le s i (s' i) e)
    _ = ∑ e, (C.load s' e : ℝ) * C.latency e (C.load s e + 1) :=
        C.sum_sum_resources_eq_sum_load_mul s' fun e => C.latency e (C.load s e + 1)
    _ ≤ ∑ e, (lam * ((C.load s' e : ℝ) * C.latency e (C.load s' e)) +
          μ * ((C.load s e : ℝ) * C.latency e (C.load s e))) :=
        sum_le_sum fun e _ => he e (C.load s' e) (C.load s e)
    _ = lam * C.toCostGame.socialCost s' + μ * C.toCostGame.socialCost s := by
        rw [socialCost_toCostGame, socialCost_toCostGame, sum_add_distrib, mul_sum, mul_sum]

/-- **Degree-`d` polynomial atomic congestion games are `(λ_d, μ_d)`-smooth**
([Roughgarden2015], Example 2.5; [AwerbuchAzarEpstein2005];
[AlandDumraufGairingMonienSchoppmann2006]). -/
theorem isSmooth_of_hasPolynomialLatencies {d : ℕ} (h : C.HasPolynomialLatencies d) :
    C.toCostGame.IsSmooth (polynomialSmoothLam d) (polynomialSmoothMu d) := by
  have hmono := h.monotone_latency
  obtain ⟨c, hc, hl⟩ := h
  refine isSmooth_of_latency_bound hmono fun e y z => ?_
  rw [hl, hl, hl, mul_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun j hj => ?_
  have hjd : j ≤ d := Nat.lt_succ_iff.1 (mem_range.1 hj)
  have hbase := nat_mul_add_one_pow_le_polynomialSmooth hjd y z
  push_cast at hbase ⊢
  have hscaled := mul_le_mul_of_nonneg_left hbase (hc e j)
  linarith [show (y : ℝ) * (c e j * ((z : ℝ) + 1) ^ j) = c e j * ((y : ℝ) * ((z : ℝ) + 1) ^ j) by
      ring,
    show polynomialSmoothLam d * ((y : ℝ) * (c e j * (y : ℝ) ^ j)) +
        polynomialSmoothMu d * ((z : ℝ) * (c e j * (z : ℝ) ^ j)) =
      c e j * (polynomialSmoothLam d * (y : ℝ) ^ (j + 1) +
        polynomialSmoothMu d * (z : ℝ) ^ (j + 1)) by ring]

/-- **Robust price of anarchy `φ_d ^ (d + 1)` for degree-`d` polynomial congestion games**: for
`d ≥ 1`, every coarse correlated equilibrium `σ` satisfies
`E_{s ∼ σ}[socialCost s] ≤ polynomialRoot d ^ (d + 1) * socialCost s'`. -/
theorem expected_socialCost_le_of_hasPolynomialLatencies {d : ℕ} (hd : 1 ≤ d)
    (h : C.HasPolynomialLatencies d) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hσ : C.toCostGame.IsCoarseCorrelatedEquilibrium σ) (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * C.toCostGame.socialCost s) ≤
      polynomialRoot d ^ (d + 1) * C.toCostGame.socialCost s' := by
  have hsm := (isSmooth_of_hasPolynomialLatencies h).expected_socialCost_le
    (polynomialSmoothMu_lt_one d) hσ s'
  rwa [polynomialSmoothRatio_eq hd] at hsm

/-- **Explicit closed-form `d^{O(d)}` robust price of anarchy** ([AwerbuchAzarEpstein2005];
[Roughgarden2015], Example 2.5 and Theorem 3.2): for `d ≥ 1`, every coarse correlated equilibrium
of a degree-`d` polynomial congestion game has expected social cost at most
`(d + 1) ^ (d + 1) * socialCost s'`. -/
theorem expected_socialCost_le_succ_pow_of_hasPolynomialLatencies {d : ℕ} (hd : 1 ≤ d)
    (h : C.HasPolynomialLatencies d) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hσ : C.toCostGame.IsCoarseCorrelatedEquilibrium σ) (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * C.toCostGame.socialCost s) ≤
      ((d : ℝ) + 1) ^ (d + 1) * C.toCostGame.socialCost s' := by
  have := Fintype.ofFinite E
  have hnonneg : 0 ≤ C.toCostGame.socialCost s' := by
    obtain ⟨c, hc, hl⟩ := h
    rw [socialCost_toCostGame]
    refine sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) ?_
    rw [hl]
    exact sum_nonneg fun j _ => mul_nonneg (hc e j) (by positivity)
  have hpow : polynomialRoot d ^ (d + 1) ≤ ((d : ℝ) + 1) ^ (d + 1) :=
    pow_le_pow_left₀ (polynomialRoot_pos d).le (polynomialRoot_lt_succ hd).le (d + 1)
  exact (expected_socialCost_le_of_hasPolynomialLatencies hd h hσ s').trans
    (mul_le_mul_of_nonneg_right hpow hnonneg)

end GeneralPolynomial

/-! ### Exact quadratic (`d = 2`) smoothness and `115 / 12` tightness -/

section Quadratic

/-- **Exact natural-number quadratic smoothness inequality**
([AlandDumraufGairingMonienSchoppmann2006]):
`y * (z + 1) ^ 2 ≤ 115 / 19 * y ^ 3 + 7 / 19 * z ^ 3` for all `y, z : ℕ`, with equality at
`(y, z) = (1, 2)` and `(y, z) = (1, 3)`. -/
theorem mul_add_one_sq_le_quadraticSmooth (y z : ℕ) :
    (y : ℝ) * ((z : ℝ) + 1) ^ 2 ≤ 115 / 19 * (y : ℝ) ^ 3 + 7 / 19 * (z : ℝ) ^ 3 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp only [Nat.cast_zero, zero_mul]; positivity
  rcases eq_or_ne y 1 with rfl | hy1
  · push_cast
    have hfac : 0 ≤ ((z : ℝ) - 2) * ((z : ℝ) - 3) := by
      rcases (by omega : z ≤ 2 ∨ 3 ≤ z) with hz2 | hz3
      · have : (z : ℝ) ≤ 2 := Nat.cast_le.2 hz2
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have : (3 : ℝ) ≤ z := Nat.cast_le.2 hz3
        exact mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hfac (by positivity : (0 : ℝ) ≤ 7 * (z : ℝ) + 16),
      show 19 * (115 / 19 * (1 : ℝ) ^ 3 + 7 / 19 * (z : ℝ) ^ 3 - 1 * ((z : ℝ) + 1) ^ 2) =
        ((z : ℝ) - 2) * ((z : ℝ) - 3) * (7 * (z : ℝ) + 16) by ring]
  have hy2 : (2 : ℝ) ≤ y := Nat.ofNat_le_cast.2 (by omega)
  have hstep : 4 * ((y : ℝ) * ((z : ℝ) + 1) ^ 2) ≤ (y : ℝ) * (2 * (z : ℝ) + y) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) (by linarith : 2 * ((z : ℝ) + 1) ≤ 2 * (z : ℝ) + y) 2
    nlinarith [Nat.cast_nonneg (α := ℝ) y]
  have hsos : 0 ≤ 36 * (115 * (y : ℝ) ^ 3 + 7 * (z : ℝ) ^ 3) -
      171 * (y : ℝ) * (2 * (z : ℝ) + y) ^ 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) z) (sq_nonneg ((z : ℝ) - 2 * y)),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) y) (sq_nonneg (18 * (z : ℝ) - 47 * y)),
      sq_nonneg (y : ℝ), mul_nonneg (Nat.cast_nonneg (α := ℝ) y) (sq_nonneg (y : ℝ)),
      show 36 * (115 * (y : ℝ) ^ 3 + 7 * (z : ℝ) ^ 3) -
        171 * (y : ℝ) * (2 * (z : ℝ) + y) ^ 2 =
        252 * (z : ℝ) * ((z : ℝ) - 2 * y) ^ 2 +
        (y : ℝ) * ((18 * (z : ℝ) - 47 * y) ^ 2 + 1760 * (y : ℝ) ^ 2) by ring]
  linarith

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
  [Finite E] {C : CongestionGame ι S E}

/-- **Unweighted quadratic atomic congestion games are `(115 / 19, 7 / 19)`-smooth**
([AlandDumraufGairingMonienSchoppmann2006]). -/
theorem isSmooth_quadratic (h : C.HasPolynomialLatencies 2) :
    C.toCostGame.IsSmooth (115 / 19) (7 / 19) := by
  have hmono := h.monotone_latency
  obtain ⟨c, hc, hl⟩ := h
  refine isSmooth_of_latency_bound hmono fun e y z => ?_
  rw [hl, hl, hl]; simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
  push_cast
  have hlin : (y : ℝ) * ((z : ℝ) + 1) ≤ 115 / 19 * (y : ℝ) ^ 2 + 7 / 19 * (z : ℝ) ^ 2 := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp only [Nat.cast_zero, zero_mul]; positivity
    · have : (1 : ℝ) ≤ y := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hy0)
      nlinarith [sq_nonneg (7 * (z : ℝ) - (19 / 2) * y), Nat.cast_nonneg (α := ℝ) z]
  nlinarith [mul_le_mul_of_nonneg_left hlin (hc e 1),
    mul_le_mul_of_nonneg_left (mul_add_one_sq_le_quadraticSmooth y z) (hc e 2),
    mul_nonneg (hc e 0) (Nat.cast_nonneg (α := ℝ) y),
    mul_nonneg (hc e 0) (Nat.cast_nonneg (α := ℝ) z)]

/-- **Exact robust price of anarchy `115 / 12` for quadratic congestion games**
([AlandDumraufGairingMonienSchoppmann2006], extended to coarse correlated equilibria via
[Roughgarden2015], Theorem 3.2): every coarse correlated equilibrium of an unweighted congestion
game with nonnegative quadratic latencies has expected social cost at most `115 / 12` times the
social cost of every profile `s'`. -/
theorem expected_socialCost_le_quadratic (h : C.HasPolynomialLatencies 2)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (hσ : C.toCostGame.IsCoarseCorrelatedEquilibrium σ)
    (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * C.toCostGame.socialCost s) ≤
      115 / 12 * C.toCostGame.socialCost s' := by
  have h' := (isSmooth_quadratic h).expected_socialCost_le (by norm_num) hσ s'
  norm_num at h' ⊢
  linarith

/-- Resource sets of a symmetric four-player, eight-resource quadratic congestion game attaining
exact pure Nash price of anarchy `115 / 12`: resources `0..3` form ring 1 (weight `11`) and
resources `4..7` form ring 2 (weight `1`). Under `true` (social optimum), player `i` uses `{i, i+4}`
(load `1` everywhere, player cost `11 + 1 = 12`); under `false` (pure Nash), player `i` uses two
ring-1 resources `{i+1, i+2}` (load `2`) and three ring-2 resources `{i+1+4, i+2+4, i+3+4}`
(load `3`), giving equilibrium cost `2 * 44 + 3 * 9 = 115 = 11 * 9 + 1 * 16`. -/
private def quadraticTightResources : Fin 4 → Bool → Finset (Fin 8)
  | 0, true => {0, 4}
  | 0, false => {1, 2, 5, 6, 7}
  | 1, true => {1, 5}
  | 1, false => {2, 3, 6, 7, 4}
  | 2, true => {2, 6}
  | 2, false => {3, 0, 7, 4, 5}
  | 3, true => {3, 7}
  | 3, false => {0, 1, 4, 5, 6}

private def quadraticTightWeight (e : Fin 8) : ℕ :=
  if e.val < 4 then 11 else 1

private def quadraticTightGame : CongestionGame (Fin 4) (fun _ => Bool) (Fin 8) where
  resources := quadraticTightResources
  latency e k := (quadraticTightWeight e : ℝ) * (k : ℝ) ^ 2

private theorem quadraticTightGame_socialCost_eq (s : Fin 4 → Bool) :
    quadraticTightGame.toCostGame.socialCost s =
      ((∑ e : Fin 8, quadraticTightGame.load s e *
        (quadraticTightWeight e * quadraticTightGame.load s e ^ 2) : ℕ) : ℝ) := by
  rw [socialCost_toCostGame]
  change ∑ e : Fin 8, (quadraticTightGame.load s e : ℝ) *
    ((quadraticTightWeight e : ℝ) * (quadraticTightGame.load s e : ℝ) ^ 2) = _
  push_cast
  rfl

private theorem quadraticTightGame_socialCost_false :
    quadraticTightGame.toCostGame.socialCost (fun _ => false) = 460 := by
  rw [quadraticTightGame_socialCost_eq]
  exact_mod_cast (by decide :
    ∑ e : Fin 8, quadraticTightGame.load (fun _ => false) e *
      (quadraticTightWeight e * quadraticTightGame.load (fun _ => false) e ^ 2) = 460)

private theorem quadraticTightGame_socialCost_true :
    quadraticTightGame.toCostGame.socialCost (fun _ => true) = 48 := by
  rw [quadraticTightGame_socialCost_eq]
  exact_mod_cast (by decide :
    ∑ e : Fin 8, quadraticTightGame.load (fun _ => true) e *
      (quadraticTightWeight e * quadraticTightGame.load (fun _ => true) e ^ 2) = 48)

private theorem quadraticTightGame_isPureNash :
    quadraticTightGame.toCostGame.IsPureNash (fun _ => false) := by
  intro i t
  have hcast (s : Fin 4 → Bool) : quadraticTightGame.toCostGame.cost i s =
      ((∑ e ∈ quadraticTightResources i (s i),
        quadraticTightWeight e * quadraticTightGame.load s e ^ 2 : ℕ) : ℝ) := by
    rw [toCostGame_cost]
    dsimp only [quadraticTightGame]
    push_cast
    rfl
  rw [hcast, hcast, Nat.cast_le]
  clear hcast
  revert i t
  decide

/-- **The quadratic price-of-anarchy bound `115 / 12` is tight**: there is a four-player,
eight-resource atomic congestion game with nonnegative quadratic latencies
(`HasPolynomialLatencies 2`) possessing a pure Nash equilibrium `s` and a profile `s'` with
`socialCost s = 115 / 12 * socialCost s' > 0`. -/
theorem exists_socialCost_eq_quadratic_poa :
    ∃ (C : CongestionGame (Fin 4) (fun _ => Bool) (Fin 8)) (s s' : Fin 4 → Bool),
      C.HasPolynomialLatencies 2 ∧ C.toCostGame.IsPureNash s ∧
        0 < C.toCostGame.socialCost s' ∧
        C.toCostGame.socialCost s = 115 / 12 * C.toCostGame.socialCost s' := by
  refine ⟨quadraticTightGame, fun _ => false, fun _ => true,
    ⟨fun e j => if j = 2 then (quadraticTightWeight e : ℝ) else 0,
      fun e j => by dsimp; split_ifs <;> positivity, fun e k => ?_⟩,
    quadraticTightGame_isPureNash, ?_, ?_⟩
  · simp only [quadraticTightGame, sum_range_succ, sum_range_zero, Nat.reduceEqDiff, ↓reduceIte,
      zero_mul, zero_add]
  · rw [quadraticTightGame_socialCost_true]
    norm_num
  · rw [quadraticTightGame_socialCost_false, quadraticTightGame_socialCost_true]
    norm_num

end Quadratic

end Cslib.GameTheory.CongestionGame
