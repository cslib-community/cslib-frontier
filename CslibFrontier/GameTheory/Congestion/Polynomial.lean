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
  have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) ≤ 2 * 2 :=
    mul_le_mul h2 h2 (Real.exp_pos _).le (by norm_num)
  rw [← Real.exp_add] at h3
  norm_num at h3
  exact h3

private theorem add_two_pow_lt_add_one_pow_succ {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) + 2) ^ d < ((d : ℝ) + 1) ^ (d + 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd2
  · norm_num
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd2) with rfl | hd3
  · norm_num
  have hd3' : 3 ≤ d := Nat.succ_le_of_lt hd3
  set u : ℝ := (d : ℝ) + 1
  have hu4 : 4 ≤ u := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3'
    linarith
  have hu_pos : 0 < u := by linarith
  have hstep : 1 + 1 / u ≤ Real.exp (1 / u) := by linarith [Real.add_one_le_exp (1 / u)]
  have hpow : (1 + 1 / u) ^ d ≤ Real.exp (d * (1 / u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hstep d
  have hlt1 : (d : ℝ) * (1 / u) < 1 := by
    rw [mul_one_div, div_lt_one hu_pos]
    linarith
  have hexp_lt : (1 + 1 / u) ^ d < u :=
    (hpow.trans_lt (Real.exp_lt_exp.2 hlt1)).trans_le (exp_one_le_four.trans hu4)
  have hdiv : (d : ℝ) + 2 = u * (1 + 1 / u) := by
    have hu_ne : u ≠ 0 := hu_pos.ne'
    dsimp [u]
    field_simp
    ring
  rw [hdiv, mul_pow, pow_succ]
  exact mul_lt_mul_of_pos_left hexp_lt (pow_pos hu_pos d)

/-- For every degree `d ≥ 1`, there is a unique real `φ > 0` satisfying `φ ^ (d + 1) = (1 + φ) ^ d`,
and it lies strictly between `1` and `d + 1`. -/
theorem existsUnique_polynomialRoot {d : ℕ} (hd : 1 ≤ d) :
    ∃! φ : ℝ, 0 < φ ∧ φ ^ (d + 1) = (1 + φ) ^ d := by
  let f : ℝ → ℝ := fun x => (1 + x) ^ d - x ^ (d + 1)
  have hf_cont : ContinuousOn f (Set.Icc 1 ((d : ℝ) + 1)) := by
    dsimp [f]
    exact ((continuous_const.add continuous_id).pow d).sub (continuous_id.pow (d + 1))
      |>.continuousOn
  have hf1 : 0 < f 1 := by
    dsimp [f]
    have h2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    norm_num at h2 ⊢
    linarith
  have hfd : f ((d : ℝ) + 1) < 0 := by
    dsimp [f]
    have h := add_two_pow_lt_add_one_pow_succ hd
    have heq : 1 + ((d : ℝ) + 1) = (d : ℝ) + 2 := by ring
    rw [heq]
    linarith
  have hle : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨φ, hφ_mem, hφ_zero⟩ := intermediate_value_Icc' hle hf_cont ⟨hfd.le, hf1.le⟩
  have hφ_pos : 0 < φ := lt_of_lt_of_le zero_lt_one hφ_mem.1
  have hφ_eq : φ ^ (d + 1) = (1 + φ) ^ d := by
    dsimp [f] at hφ_zero
    linarith
  refine ⟨φ, ⟨hφ_pos, hφ_eq⟩, fun y ⟨hy_pos, hy_eq⟩ => ?_⟩
  have strict : ∀ {a b : ℝ}, 0 < a → a < b →
      a ^ (d + 1) * (1 + b) ^ d < b ^ (d + 1) * (1 + a) ^ d := by
    intro a b ha hab
    have hb : 0 < b := ha.trans hab
    have h1b : 0 < 1 + b := by linarith
    have hcross : a * (1 + b) < b * (1 + a) := by linarith
    have hpow : (a * (1 + b)) ^ d ≤ (b * (1 + a)) ^ d :=
      pow_le_pow_left₀ (mul_nonneg ha.le h1b.le) hcross.le d
    rw [mul_pow, mul_pow] at hpow
    have hpos : 0 < a ^ d * (1 + b) ^ d := mul_pos (pow_pos ha d) (pow_pos h1b d)
    calc a ^ (d + 1) * (1 + b) ^ d
        = a * (a ^ d * (1 + b) ^ d) := by ring
      _ < b * (a ^ d * (1 + b) ^ d) := mul_lt_mul_of_pos_right hab hpos
      _ ≤ b * (b ^ d * (1 + a) ^ d) := mul_le_mul_of_nonneg_left hpow hb.le
      _ = b ^ (d + 1) * (1 + a) ^ d := by ring
  rcases lt_trichotomy y φ with hlt | rfl | hgt
  · exfalso
    have h := strict hy_pos hlt
    rw [hy_eq, hφ_eq, mul_comm] at h
    exact lt_irrefl _ h
  · rfl
  · exfalso
    have h := strict hφ_pos hgt
    rw [hφ_eq, hy_eq, mul_comm] at h
    exact lt_irrefl _ h

/-- Characteristic root `φ_d` of `φ ^ (d + 1) = (1 + φ) ^ d` for `d ≥ 1` (and `1` for `d = 0`). -/
noncomputable def polynomialRoot (d : ℕ) : ℝ :=
  if hd : 1 ≤ d then Classical.choose (existsUnique_polynomialRoot hd).exists else 1

theorem polynomialRoot_pos (d : ℕ) : 0 < polynomialRoot d := by
  unfold polynomialRoot
  split_ifs with hd
  · exact (Classical.choose_spec (existsUnique_polynomialRoot hd).exists).1
  · exact zero_lt_one

theorem polynomialRoot_pow_eq {d : ℕ} (hd : 1 ≤ d) :
    polynomialRoot d ^ (d + 1) = (1 + polynomialRoot d) ^ d := by
  unfold polynomialRoot
  rw [dite_eq_left hd]
  exact (Classical.choose_spec (existsUnique_polynomialRoot hd).exists).2

theorem polynomialRoot_gt_one {d : ℕ} (hd : 1 ≤ d) : 1 < polynomialRoot d := by
  by_contra hle
  push Not at hle
  have hpos := polynomialRoot_pos d
  have heq := polynomialRoot_pow_eq hd
  have h1 : polynomialRoot d ^ (d + 1) ≤ 1 := pow_le_one₀ hpos.le hle
  have h2 : (1 : ℝ) < (1 + polynomialRoot d) ^ d := one_lt_pow₀ (by linarith) (by omega)
  linarith

/-- For every `d ≥ 1`, the characteristic root satisfies `polynomialRoot d < d + 1`. -/
theorem polynomialRoot_lt_succ {d : ℕ} (hd : 1 ≤ d) : polynomialRoot d < (d : ℝ) + 1 := by
  by_contra hge
  push Not at hge
  have hφ_pos := polynomialRoot_pos d
  have heq := polynomialRoot_pow_eq hd
  have hbase : ((d : ℝ) + 2) ^ d < ((d : ℝ) + 1) ^ (d + 1) := add_two_pow_lt_add_one_pow_succ hd
  set a : ℝ := (d : ℝ) + 1
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have h1φ : 0 < 1 + polynomialRoot d := by linarith
  have hcross : a * (1 + polynomialRoot d) ≤ polynomialRoot d * (1 + a) := by
    dsimp [a] at hge ⊢
    linarith
  have hpow : (a * (1 + polynomialRoot d)) ^ d ≤ (polynomialRoot d * (1 + a)) ^ d :=
    pow_le_pow_left₀ (mul_nonneg ha_pos.le h1φ.le) hcross d
  rw [mul_pow, mul_pow, ← heq] at hpow
  have hmul : a * (a ^ d * polynomialRoot d ^ (d + 1)) ≤
      polynomialRoot d * (polynomialRoot d ^ d * (1 + a) ^ d) :=
    mul_le_mul hge hpow (mul_nonneg (pow_nonneg ha_pos.le d) (pow_nonneg hφ_pos.le (d + 1)))
      hφ_pos.le
  have hsimp : a ^ (d + 1) * polynomialRoot d ^ (d + 1) ≤
      polynomialRoot d ^ (d + 1) * (1 + a) ^ d := by
    calc a ^ (d + 1) * polynomialRoot d ^ (d + 1)
        = a * (a ^ d * polynomialRoot d ^ (d + 1)) := by ring
      _ ≤ polynomialRoot d * (polynomialRoot d ^ d * (1 + a) ^ d) := hmul
      _ = polynomialRoot d ^ (d + 1) * (1 + a) ^ d := by ring
  have hcancel : a ^ (d + 1) ≤ (1 + a) ^ d :=
    le_of_mul_le_mul_left (by rwa [mul_comm] at hsimp) (pow_pos hφ_pos (d + 1))
  have ha2 : 1 + a = (d : ℝ) + 2 := by
    dsimp [a]
    ring
  rw [ha2] at hcancel
  exact hbase.not_ge hcancel

theorem polynomialRoot_strictMono {j d : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    polynomialRoot j < polynomialRoot d := by
  by_contra hge
  push Not at hge
  have hd : 1 ≤ d := by omega
  set φj := polynomialRoot j
  set φd := polynomialRoot d
  have hφd_gt1 : 1 < φd := polynomialRoot_gt_one hd
  have hφj_pos : 0 < φj := polynomialRoot_pos j
  have hφd_pos : 0 < φd := polynomialRoot_pos d
  have h1φj : 0 < 1 + φj := by linarith
  have hcross : φd * (1 + φj) ≤ φj * (1 + φd) := by linarith
  have hpow : (φd * (1 + φj)) ^ j ≤ (φj * (1 + φd)) ^ j :=
    pow_le_pow_left₀ (mul_nonneg hφd_pos.le h1φj.le) hcross j
  rw [mul_pow, mul_pow, ← polynomialRoot_pow_eq hj] at hpow
  have hcancel : φd ^ j * φj ≤ (1 + φd) ^ j := by
    have hrew : φj ^ j * (φd ^ j * φj) ≤ φj ^ j * (1 + φd) ^ j := by
      calc φj ^ j * (φd ^ j * φj) = φd ^ j * φj ^ (j + 1) := by ring
        _ ≤ φj ^ j * (1 + φd) ^ j := hpow
    exact le_of_mul_le_mul_left hrew (pow_pos hφj_pos j)
  have hstep1 : φd ^ (j + 1) ≤ (1 + φd) ^ j := by
    calc φd ^ (j + 1) = φd ^ j * φd := by ring
      _ ≤ φd ^ j * φj := mul_le_mul_of_nonneg_left hge (pow_nonneg hφd_pos.le j)
      _ ≤ (1 + φd) ^ j := hcancel
  have hstep2 : φd ^ (d + 1) < (1 + φd) ^ d := by
    obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ d = j + m := ⟨d - j, by omega, by omega⟩
    have hlt_ratio : φd ^ m < (1 + φd) ^ m :=
      pow_lt_pow_left₀ (by linarith) hφd_pos.le (by omega)
    calc φd ^ (j + m + 1)
        = φd ^ (j + 1) * φd ^ m := by ring
      _ ≤ (1 + φd) ^ j * φd ^ m := mul_le_mul_of_nonneg_right hstep1 (pow_nonneg hφd_pos.le m)
      _ < (1 + φd) ^ j * (1 + φd) ^ m :=
          mul_lt_mul_of_pos_left hlt_ratio (pow_pos (by linarith) j)
      _ = (1 + φd) ^ (j + m) := by rw [← pow_add]
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
  split_ifs with hd0
  · exact zero_lt_one
  · have hφ := polynomialRoot_pos d
    rw [div_lt_one (by positivity)]
    nlinarith

theorem one_le_polynomialSmoothLam (d : ℕ) : 1 ≤ polynomialSmoothLam d := by
  unfold polynomialSmoothLam
  split_ifs with hd0
  · exact le_rfl
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd0
    have hφ1 : 1 < polynomialRoot d := polynomialRoot_gt_one hd
    have heq : polynomialRoot d ^ (d + 1) = (1 + polynomialRoot d) ^ d := polynomialRoot_pow_eq hd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
    rw [heq, pow_succ]
    have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have h1pos : 0 < 1 + polynomialRoot (k + 1) := by linarith
    have hpow1 : (1 : ℝ) ≤ (1 + polynomialRoot (k + 1)) ^ k :=
      one_le_pow₀ (by linarith)
    have hfrac : 1 ≤ (((k + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1)) /
        ((((k + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1))) *
        (1 + polynomialRoot (k + 1)) := by
      have hne1 : (((k + 1 : ℕ) : ℝ) + 1) ≠ 0 := hden_pos.ne'
      have hne2 : 1 + polynomialRoot (k + 1) ≠ 0 := h1pos.ne'
      field_simp
      linarith
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ ((((k + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1)) /
            ((((k + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1))) *
            (1 + polynomialRoot (k + 1))) * (1 + polynomialRoot (k + 1)) ^ k :=
          mul_le_mul hfrac hpow1 zero_le_one (by positivity)
      _ = (((k + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1)) /
            ((((k + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1))) *
            ((1 + polynomialRoot (k + 1)) ^ k * (1 + polynomialRoot (k + 1))) := by ring

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
    field_simp
    ring
  rw [h1mu]
  have hnum_ne : ((d : ℝ) + 1 + polynomialRoot d) / (((d : ℝ) + 1) * (1 + polynomialRoot d)) ≠ 0 :=
    by positivity
  exact mul_div_cancel_left₀ _ hnum_ne

theorem polynomialSmoothMu_mono {j d : ℕ} (hjd : j ≤ d) :
    polynomialSmoothMu j ≤ polynomialSmoothMu d := by
  rcases eq_or_lt_of_le hjd with rfl | hlt
  · exact le_rfl
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [polynomialSmoothMu, ↓reduceIte]
    exact polynomialSmoothMu_nonneg d
  have hj1 : 1 ≤ j := hj
  have hφ_lt : polynomialRoot j < polynomialRoot d := polynomialRoot_strictMono hj1 hlt
  have hφj : 0 < polynomialRoot j := polynomialRoot_pos j
  have hφd : 0 < polynomialRoot d := polynomialRoot_pos d
  have hj0 : j ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  unfold polynomialSmoothMu
  simp only [hj0, hd0, ↓reduceIte]
  have hj_le_d : (j : ℝ) ≤ d := by exact_mod_cast hjd
  have hf1 : (j : ℝ) / ((j : ℝ) + 1) ≤ (d : ℝ) / ((d : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hf2 : polynomialRoot j / (1 + polynomialRoot j) ≤
      polynomialRoot d / (1 + polynomialRoot d) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc (j : ℝ) * polynomialRoot j / (((j : ℝ) + 1) * (1 + polynomialRoot j))
      = ((j : ℝ) / ((j : ℝ) + 1)) * (polynomialRoot j / (1 + polynomialRoot j)) := by
        field_simp
    _ ≤ ((d : ℝ) / ((d : ℝ) + 1)) * (polynomialRoot d / (1 + polynomialRoot d)) :=
        mul_le_mul hf1 hf2 (by positivity) (by positivity)
    _ = (d : ℝ) * polynomialRoot d / (((d : ℝ) + 1) * (1 + polynomialRoot d)) := by
        field_simp

theorem polynomialSmoothLam_mono {j d : ℕ} (hjd : j ≤ d) :
    polynomialSmoothLam j ≤ polynomialSmoothLam d := by
  induction hjd with
  | refl => exact le_rfl
  | @step m hjm ih =>
    refine ih.trans ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [polynomialSmoothLam, ↓reduceIte]
      exact one_le_polynomialSmoothLam 1
    have hm1 : 1 ≤ m := hm
    have hm_succ : 1 ≤ m + 1 := by omega
    have hφm_lt_succ : polynomialRoot m < (m : ℝ) + 1 := polynomialRoot_lt_succ hm1
    have hφ_inc : polynomialRoot m < polynomialRoot (m + 1) :=
      polynomialRoot_strictMono hm1 (Nat.lt_succ_self m)
    have hφm_gt1 : 1 < polynomialRoot m := polynomialRoot_gt_one hm1
    have hφs_gt1 : 1 < polynomialRoot (m + 1) := polynomialRoot_gt_one hm_succ
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm1
    have heq_m := polynomialRoot_pow_eq hm1
    have heq_s := polynomialRoot_pow_eq hm_succ
    have hk0 : k + 1 ≠ 0 := by omega
    have hks0 : k + 1 + 1 ≠ 0 := by omega
    unfold polynomialSmoothLam
    simp only [hk0, hks0, ↓reduceIte, heq_m, heq_s]
    have h1m : 0 < 1 + polynomialRoot (k + 1) := by linarith
    have h1s : 0 < 1 + polynomialRoot (k + 1 + 1) := by linarith
    have hrew1 : (((k + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1)) /
        ((((k + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1))) *
        (1 + polynomialRoot (k + 1)) ^ (k + 1) =
        (1 + polynomialRoot (k + 1) / (((k + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1)) ^ k := by
      rw [pow_succ]
      have hd1 : (((k + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      have hd2 : 1 + polynomialRoot (k + 1) ≠ 0 := h1m.ne'
      field_simp
    have hrew2 : (((k + 1 + 1 : ℕ) : ℝ) + 1 + polynomialRoot (k + 1 + 1)) /
        ((((k + 1 + 1 : ℕ) : ℝ) + 1) * (1 + polynomialRoot (k + 1 + 1))) *
        (1 + polynomialRoot (k + 1 + 1)) ^ (k + 1 + 1) =
        (1 + polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1 + 1)) * (1 + polynomialRoot (k + 1 + 1)) ^ k := by
      rw [pow_succ, pow_succ]
      have hd1 : (((k + 1 + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      have hd2 : 1 + polynomialRoot (k + 1 + 1) ≠ 0 := h1s.ne'
      field_simp
    rw [hrew1, hrew2]
    have hcoef : 1 + polynomialRoot (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) ≤
        (1 + polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1)) *
        (1 + polynomialRoot (k + 1 + 1)) := by
      have hdiv_lt : polynomialRoot (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) < 1 :=
        (div_lt_one (by positivity)).2 hφm_lt_succ
      have hpos_div : 0 ≤ polynomialRoot (k + 1 + 1) / (((k + 1 + 1 : ℕ) : ℝ) + 1) := by
        positivity
      nlinarith
    have hpow_le : (1 + polynomialRoot (k + 1)) ^ k ≤ (1 + polynomialRoot (k + 1 + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    exact mul_le_mul hcoef hpow_le (by positivity) (by positivity)

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
  · simp only [Nat.cast_zero, zero_mul]
    positivity
  rcases eq_or_ne y 1 with rfl | hy1
  · push_cast
    have hsplit : z ≤ 2 ∨ 3 ≤ z := by omega
    have hfac : ((z : ℝ) - 2) * ((z : ℝ) - 3) ≥ 0 := by
      rcases hsplit with hz2 | hz3
      · have hz2' : (z : ℝ) ≤ 2 := by exact_mod_cast hz2
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hz3' : (3 : ℝ) ≤ z := by exact_mod_cast hz3
        exact mul_nonneg (by linarith) (by linarith)
    have hpos : (0 : ℝ) ≤ 7 * (z : ℝ) + 16 := by positivity
    nlinarith [mul_nonneg hfac hpos,
      show 19 * (115 / 19 * (1 : ℝ) ^ 3 + 7 / 19 * (z : ℝ) ^ 3 - 1 * ((z : ℝ) + 1) ^ 2) =
        ((z : ℝ) - 2) * ((z : ℝ) - 3) * (7 * (z : ℝ) + 16) by ring]
  have hy2 : 2 ≤ y := by omega
  have hy2' : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hz_pos : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hy_pos : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hstep : 4 * ((y : ℝ) * ((z : ℝ) + 1) ^ 2) ≤ (y : ℝ) * (2 * (z : ℝ) + y) ^ 2 := by
    have hle : 2 * ((z : ℝ) + 1) ≤ 2 * (z : ℝ) + y := by linarith
    have hsq : (2 * ((z : ℝ) + 1)) ^ 2 ≤ (2 * (z : ℝ) + y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    nlinarith
  have hsos : 0 ≤ 36 * (115 * (y : ℝ) ^ 3 + 7 * (z : ℝ) ^ 3) -
      171 * (y : ℝ) * (2 * (z : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z : ℝ) - 2 * y), sq_nonneg (18 * (z : ℝ) - 47 * y),
      mul_nonneg hz_pos (sq_nonneg ((z : ℝ) - 2 * y)),
      mul_nonneg hy_pos (sq_nonneg (18 * (z : ℝ) - 47 * y)),
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
  rw [hl, hl, hl]
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
  push_cast
  have hlin : (y : ℝ) * ((z : ℝ) + 1) ≤ 115 / 19 * (y : ℝ) ^ 2 + 7 / 19 * (z : ℝ) ^ 2 := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · simp only [hy0, Nat.cast_zero, zero_mul]
      positivity
    · have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hy0
      have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
      nlinarith [sq_nonneg (7 * (z : ℝ) - (19 / 2) * y)]
  have hquad := mul_add_one_sq_le_quadraticSmooth y z
  have hc0 := hc e 0
  have hc1 := hc e 1
  have hc2 := hc e 2
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlin hc1, mul_le_mul_of_nonneg_left hquad hc2,
    mul_nonneg hc0 hy0, mul_nonneg hc0 hz0]

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
  rw [toCostGame_cost, toCostGame_cost]
  change ∑ e ∈ quadraticTightResources i false,
      (quadraticTightWeight e : ℝ) * (quadraticTightGame.load (fun _ => false) e : ℝ) ^ 2 ≤
    ∑ e ∈ quadraticTightResources i (Function.update (fun _ => false) i t i),
      (quadraticTightWeight e : ℝ) *
        (quadraticTightGame.load (Function.update (fun _ => false) i t) e : ℝ) ^ 2
  have hcast : ∀ s : Fin 4 → Bool,
      (∑ e ∈ quadraticTightResources i (s i),
        (quadraticTightWeight e : ℝ) * (quadraticTightGame.load s e : ℝ) ^ 2) =
      ((∑ e ∈ quadraticTightResources i (s i),
        quadraticTightWeight e * quadraticTightGame.load s e ^ 2 : ℕ) : ℝ) := by
    intro s
    push_cast
    rfl
  rw [hcast (fun _ => false), hcast (Function.update (fun _ => false) i t), Nat.cast_le]
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
