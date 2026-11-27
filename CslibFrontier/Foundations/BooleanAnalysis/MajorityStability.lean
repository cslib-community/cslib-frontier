/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.MajorityFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ArcsinSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The limits of the spectrum and the noise stability of majority

For majority of `n = 2 m + 1` bits, read as signs, the Fourier weight at each odd level
`k = 2 j + 1` converges as `m → ∞`:
`W^k[Maj_n] → [ρ^k] (2/π) arcsin ρ = (2/π) C(2j, j) / (4^j (2j + 1))`
(`BitString.tendsto_levelWeight_signVal_majority`) [O'Donnell, Theorem 5.22][ODonnell2014]. At
level one, `W^1[Maj_n] = (2m + 1) (C(2m, m) / 4^m)²` is the reciprocal of the `m`-th Wallis
product, which tends to `π/2`. From one odd level to the next the weights change by the factor
`(2m - 2j) (2j + 1)² / ((2j + 2)(2j + 3)(2m - 2j - 1))`, which tends to the ratio
`(2j + 1)² / ((2j + 2)(2j + 3))` of consecutive coefficients of `(2/π) arcsin`. The weights
decrease in `n` (`BitString.levelWeight_signVal_majority_succ_lt`, Corollary 5.21), so each is at
least its limit (`BitString.le_levelWeight_signVal_majority`), the lower half of the book's error
bound (5.15). For the upper half, the weight at level `k = 2j + 1` is `(π/2) n c_{m-j} c_m` times
its limit, with `c_a = C(2a, a)/4^a`; Wallis's product gives `c_a² ≤ 1/(πa)`, so for `k < n/2` the
weight is at most `(1 + 2k/n)` times its limit (`BitString.levelWeight_signVal_majority_le`).

Summing over the levels, with the weights bounded by `1` and the geometric bound `|ρ|^k` for
`|ρ| < 1` (Tannery's theorem), and using the Maclaurin series of `arcsin`
(`Real.hasSum_arcsin`), the noise stability of majority converges:
`Stab_ρ[Maj_n] → (2/π) arcsin ρ` for every `ρ ∈ [-1, 1]`
(`BitString.tendsto_noiseStability_signVal_majority`) [O'Donnell, Theorem 2.45][ODonnell2014].
At `ρ = 1` every function read as signs has `Stab_1 = 1`, and at `ρ = -1` majority, being odd,
has `Stab_{-1} = -1`. For `0 ≤ ρ ≤ 1` the noise stability decreases in `n` (Theorem 5.18), so it
is at least its limit (`BitString.le_noiseStability_signVal_majority`); summing the error bound
(5.15) over the levels below `n/2` and bounding the levels above by `ρ^((n+1)/2)` gives
`Stab_ρ[Maj_n] ≤ (2/π) arcsin ρ + 3 / √((1 - ρ²) n)` for `0 ≤ ρ < 1`
(`BitString.noiseStability_signVal_majority_le`), the rest of Theorem 5.18. Equivalently, for
`δ ∈ [0, 1]`, `NS_δ[Maj_n] → arccos(1 - 2δ) / π` (`BitString.tendsto_noiseSensitivity_majority`).

This is the Fourier route of the book's Section 5.3 (the book first proves Theorem 2.45 through
the multidimensional central limit theorem in Section 5.2 and deduces Theorem 5.22 from it, then
proves Theorem 5.22 directly); no central limit theorem is used.

## Main results

* `Cslib.BitString.tendsto_levelWeight_signVal_majority`: the limit in Theorem 5.22.
* `Cslib.BitString.le_levelWeight_signVal_majority`,
  `Cslib.BitString.levelWeight_signVal_majority_le`: the error bound (5.15) of Theorem 5.22.
* `Cslib.BitString.tendsto_noiseStability_signVal_majority`: Theorem 2.45.
* `Cslib.BitString.le_noiseStability_signVal_majority`,
  `Cslib.BitString.noiseStability_signVal_majority_le`: the bounds of Theorem 5.18.
* `Cslib.BitString.tendsto_noiseSensitivity_majority`: Theorem 2.45 in noise-sensitivity form.

## Usage

Majority of `2 m + 1` bits read as signs is `fun x => signVal (majority (2 * m + 1) x)`; the
limits are along `m → ∞`, the book's `n → ∞` through the odd numbers. The book's sign convention
differs (`true` reads as `-1`), which changes neither level weights nor noise stability. The book's
form `(4 / (π k 2^k)) C(k - 1, (k - 1)/2)` of the limiting weight is
`2 / π * (Nat.centralBinom j / 4 ^ j / (2 * j + 1))` at `k = 2 j + 1`. The asymptotics of
Corollary 5.23 are not formalized ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Sections 2.4 and 5.3.
-/

public section

namespace Cslib.BitString

open Finset Filter Topology Real

/-! ### The level weights of majority -/

/-- The degree-one weight of majority of `2 m + 1` bits is the reciprocal of the `m`-th Wallis
product. -/
private theorem levelWeight_one_signVal_majority (m : ℕ) :
    levelWeight 1 (fun x => signVal (majority (2 * m + 1) x)) = (Real.Wallis.W m)⁻¹ := by
  have h := levelWeight_signVal_majority_of_odd m 0
  simp only [mul_zero, zero_add, Nat.choose_zero_right, Nat.cast_one, Nat.choose_one_right,
    div_one, one_mul] at h
  rw [h, Real.Wallis.W_eq_factorial_ratio, Nat.cast_choose ℝ (by omega : m ≤ 2 * m),
    show 2 * m - m = m by omega]
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  have : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  rw [h4]
  push_cast
  field_simp
  ring

/-- From one odd level of majority to the next, the weight changes by the factor
`(2m - 2j) (2j + 1)² / ((2j + 2)(2j + 3)(2m - 2j - 1))`. -/
private theorem levelWeight_signVal_majority_succ_level {m j : ℕ} (hj : j + 1 ≤ m) :
    levelWeight (2 * (j + 1) + 1) (fun x => signVal (majority (2 * m + 1) x)) *
        ((2 * j + 2) * (2 * j + 3) * (2 * m - 2 * j - 1)) =
      levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) *
        ((2 * m - 2 * j) * (2 * j + 1) ^ 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = j + 1 + r := ⟨m - j - 1, by omega⟩
  rw [levelWeight_signVal_majority_of_odd, levelWeight_signVal_majority_of_odd,
    Nat.cast_choose ℝ (by omega : 2 * (j + 1) + 1 ≤ 2 * (j + 1 + r) + 1),
    Nat.cast_choose ℝ (by omega : 2 * j + 1 ≤ 2 * (j + 1 + r) + 1),
    Nat.cast_choose ℝ (by omega : j + 1 ≤ j + 1 + r),
    Nat.cast_choose ℝ (by omega : j ≤ j + 1 + r),
    Nat.cast_choose ℝ (by omega : 2 * (j + 1) ≤ 2 * (j + 1 + r)),
    Nat.cast_choose ℝ (by omega : 2 * j ≤ 2 * (j + 1 + r)),
    show 2 * (j + 1 + r) + 1 - (2 * (j + 1) + 1) = 2 * r by omega,
    show 2 * (j + 1 + r) + 1 - (2 * j + 1) = 2 * r + 1 + 1 by omega,
    show j + 1 + r - (j + 1) = r by omega, show j + 1 + r - j = r + 1 by omega,
    show 2 * (j + 1 + r) - 2 * (j + 1) = 2 * r by omega,
    show 2 * (j + 1 + r) - 2 * j = 2 * r + 1 + 1 by omega,
    show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((2 * r).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h5 : ((2 * (j + 1 + r)).choose (j + 1 + r) : ℝ) ≠ 0 := by
    have := Nat.choose_pos (by omega : j + 1 + r ≤ 2 * (j + 1 + r)); positivity
  have h6 : ((2 * (j + 1 + r) + 1).factorial : ℝ) ≠ 0 := by positivity
  have h7 : ((2 * (j + 1 + r)).factorial : ℝ) ≠ 0 := by positivity
  have h8 : ((j + 1 + r).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **The limit of the spectrum of majority** [O'Donnell, Theorem 5.22][ODonnell2014]: for each
`j`, the Fourier weight of majority of `2 m + 1` bits, read as signs, at level `k = 2 j + 1`
tends to `[ρ^k] (2/π) arcsin ρ = (2/π) C(2j, j) / (4^j (2j + 1))` as `m → ∞`. The two halves of
the book's error bound (5.15) are `BitString.le_levelWeight_signVal_majority` and
`BitString.levelWeight_signVal_majority_le`. -/
theorem tendsto_levelWeight_signVal_majority (j : ℕ) :
    Tendsto (fun m : ℕ => levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)))
      atTop (𝓝 (2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1)))) := by
  induction j with
  | zero =>
    have h := Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ (by positivity)
    simp only [mul_zero, zero_add, Nat.centralBinom_zero, Nat.cast_one, pow_zero, div_one,
      CharP.cast_eq_zero, mul_one]
    convert h using 1
    · exact funext levelWeight_one_signVal_majority
    · rw [inv_div]
  | succ j ih =>
    set c : ℝ := (2 * j + 1) ^ 2 / ((2 * j + 2) * (2 * j + 3)) with hc
    have hlin : Tendsto (fun m : ℕ => (2 : ℝ) * m - 2 * j - 1) atTop atTop := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (zero_lt_two' ℝ)
      simpa [sub_eq_add_neg, add_assoc] using
        tendsto_atTop_add_const_right _ (-(2 * (j : ℝ)) - 1) this
    have hq : Tendsto (fun m : ℕ => c * (1 + ((2 : ℝ) * m - 2 * j - 1)⁻¹)) atTop (𝓝 c) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_inv_atTop_zero.comp hlin)).const_mul c
      simpa using this
    have hlim : 2 / π * ((Nat.centralBinom (j + 1) : ℝ) / 4 ^ (j + 1) / (2 * (j + 1 : ℕ) + 1)) =
        2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1)) * c := by
      have h' : ((j : ℝ) + 1) * Nat.centralBinom (j + 1) =
          2 * (2 * j + 1) * Nat.centralBinom j := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ j
      have hc' : (Nat.centralBinom (j + 1) : ℝ) =
          2 * (2 * j + 1) * Nat.centralBinom j / (j + 1) := by
        rw [← h']; field_simp
      rw [hc', hc, pow_succ]
      push_cast
      field_simp
      ring
    rw [hlim]
    refine (ih.mul hq).congr' ?_
    filter_upwards [eventually_ge_atTop (j + 1)] with m hm
    have hpos : (0 : ℝ) < 2 * m - 2 * j - 1 := by
      have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hm
      linarith
    have hden : (0 : ℝ) < (2 * j + 2) * (2 * j + 3) * (2 * m - 2 * j - 1) := by positivity
    have h' : levelWeight (2 * (j + 1) + 1) (fun x => signVal (majority (2 * m + 1) x)) =
        levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) *
          ((2 * m - 2 * j) * (2 * j + 1) ^ 2) /
            ((2 * j + 2) * (2 * j + 3) * (2 * m - 2 * j - 1)) := by
      rw [eq_div_iff hden.ne']; exact levelWeight_signVal_majority_succ_level hm
    rw [h', hc]
    set d : ℝ := 2 * m - 2 * j - 1 with hd
    have hne : d ≠ 0 := hpos.ne'
    have hd1 : (2 : ℝ) * m - 2 * j = d + 1 := by rw [hd]; ring
    rw [hd1]
    field_simp

/-- **The level weights of majority are at least their limits**: for `j ≤ m`, the Fourier weight
of majority of `2 m + 1` bits at level `2 j + 1` is at least
`(2/π) C(2j, j) / (4^j (2j + 1))`, the lower half of [O'Donnell, (5.15)][ODonnell2014]. The
weights decrease in `m` (Corollary 5.21) towards this limit (Theorem 5.22). -/
theorem le_levelWeight_signVal_majority {m j : ℕ} (hj : j ≤ m) :
    2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1)) ≤
      levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = j + r := ⟨m - j, by omega⟩
  have hanti : Antitone fun n : ℕ =>
      levelWeight (2 * j + 1) (fun x => signVal (majority (2 * (j + n) + 1) x)) :=
    antitone_nat_of_succ_le fun n => (levelWeight_signVal_majority_succ_lt (j + n) j (by omega)).le
  exact hanti.le_of_tendsto ((tendsto_levelWeight_signVal_majority j).comp
    ((tendsto_add_atTop_nat j).congr fun n => add_comm n j)) r

/-- The level weights of majority in terms of `c_a = C(2a, a) / 4^a`:
`W^{2j+1}[Maj_{2(j+r)+1}] = (2(j+r) + 1)/(2j + 1) · c_j c_r c_{j+r}`. -/
private theorem levelWeight_signVal_majority_eq_mul (j r : ℕ) :
    levelWeight (2 * j + 1) (fun x => signVal (majority (2 * (j + r) + 1) x)) =
      (2 * (j + r) + 1) / (2 * j + 1) * ((Nat.centralBinom j : ℝ) / 4 ^ j) *
        ((Nat.centralBinom r : ℝ) / 4 ^ r) * ((Nat.centralBinom (j + r) : ℝ) / 4 ^ (j + r)) := by
  rw [levelWeight_signVal_majority_of_odd,
    Nat.cast_choose ℝ (by omega : 2 * j + 1 ≤ 2 * (j + r) + 1),
    Nat.cast_choose ℝ (by omega : j ≤ j + r),
    Nat.cast_choose ℝ (by omega : 2 * j ≤ 2 * (j + r)),
    Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose,
    Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (by omega : j ≤ 2 * j), Nat.cast_choose ℝ (by omega : r ≤ 2 * r),
    Nat.cast_choose ℝ (by omega : j + r ≤ 2 * (j + r)),
    show 2 * (j + r) + 1 - (2 * j + 1) = 2 * r by omega, show j + r - j = r by omega,
    show 2 * (j + r) - 2 * j = 2 * r by omega, show 2 * j - j = j by omega,
    show 2 * r - r = r by omega, show 2 * (j + r) - (j + r) = j + r by omega,
    show 2 * (j + r) + 1 = 2 * (j + r) + 1 from rfl, Nat.factorial_succ (2 * (j + r)),
    Nat.factorial_succ (2 * j), pow_add]
  have h1 : ((2 * r).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h7 : ((2 * (j + r)).factorial : ℝ) ≠ 0 := by positivity
  have h8 : ((j + r).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- By Wallis's product, `(C(2a, a) / 4^a)² ≤ 1 / (π a)` for `a ≥ 1`. -/
private theorem sq_centralBinom_div_four_pow_le {a : ℕ} (ha : 1 ≤ a) :
    ((Nat.centralBinom a : ℝ) / 4 ^ a) ^ 2 ≤ 1 / (π * a) := by
  have hle := Real.Wallis.le_W a
  rw [Real.Wallis.W_eq_factorial_ratio] at hle
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.cast_choose ℝ (by omega : a ≤ 2 * a),
    show 2 * a - a = a by omega]
  have hf : (a.factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((2 * a).factorial : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
  rw [h4]
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  set X : ℝ := ((2 * a).factorial : ℝ)
  set Y : ℝ := (a.factorial : ℝ)
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have hP : (0 : ℝ) < 2 ^ (2 * a) := by positivity
  have h44 : (2 : ℝ) ^ (4 * a) = (2 ^ (2 * a)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [h44] at hle
  set P : ℝ := 2 ^ (2 * a)
  -- cross-multiplied Wallis bound
  have hcross : (2 * a + 1) ^ 2 * π * X ^ 2 ≤ (4 * a + 4) * P ^ 2 * Y ^ 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)] at hle
    nlinarith [pi_pos]
  rw [div_pow, div_pow, mul_pow, le_div_iff₀ (by positivity)]
  rw [div_div, div_mul_eq_mul_div, div_le_one (by positivity)]
  have hkey : a * (4 * a + 4) ≤ (2 * (a : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [pi_pos, mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ P ^ 2 * Y ^ 4),
    mul_le_mul_of_nonneg_left hcross (by positivity : (0 : ℝ) ≤ a)]

/-- [O'Donnell, Exercise 5.24][ODonnell2014]: `n⁴ ≤ (n + 2k)² (n - k)(n - 1)` for
`1 ≤ k ≤ n/2`, that is, `n / √((n - k)(n - 1)) ≤ 1 + 2k/n`. -/
private theorem pow_four_le_mul_sub_mul_sub {n k : ℝ} (hk : 1 ≤ k) (hnk : 2 * k ≤ n) :
    n ^ 4 ≤ (n + 2 * k) ^ 2 * ((n - k) * (n - 1)) := by
  have hn : 2 ≤ n := by linarith
  have h1 : n * (2 * k - 1) ≥ 2 * k := by nlinarith
  have h2 : n ^ 2 ≥ 4 * k ^ 2 := by nlinarith
  have h3 : n * (3 * k - 1) - 3 * k ≥ k * (n - 1) := by nlinarith
  have h4 : n ^ 2 * (n * (3 * k - 1) - 3 * k) ≥ 4 * k ^ 2 * (k * (n - 1)) := by
    have : 0 ≤ k * (n - 1) := by nlinarith
    nlinarith
  nlinarith

/-- **The upper error bound for the spectrum of majority** [O'Donnell, Theorem 5.22, (5.15)]
[ODonnell2014]: for `k = 2j + 1 < n/2`, with `n = 2m + 1`, the Fourier weight of majority at level
`k` is at most `(1 + 2k/n)` times its limit `(2/π) C(2j, j) / (4^j (2j + 1))`. The weight is
`(π/2) n c_{m-j} c_m` times its limit for `c_a = C(2a, a)/4^a`; Wallis's product bounds
`c_a² ≤ 1/(πa)`, so the factor is at most `n / √((n - k)(n - 1)) ≤ 1 + 2k/n` (Exercise 5.24). -/
theorem levelWeight_signVal_majority_le {m j : ℕ} (h : 2 * (2 * j + 1) < 2 * m + 1) :
    levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) ≤
      (1 + 2 * (2 * j + 1) / (2 * m + 1)) *
        (2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = j + r := ⟨m - j, by omega⟩
  have hr : 1 ≤ r := by omega
  have hm : 1 ≤ j + r := by omega
  rw [levelWeight_signVal_majority_eq_mul]
  set cj : ℝ := (Nat.centralBinom j : ℝ) / 4 ^ j
  set cr : ℝ := (Nat.centralBinom r : ℝ) / 4 ^ r
  set cm : ℝ := (Nat.centralBinom (j + r) : ℝ) / 4 ^ (j + r)
  have hcj : 0 ≤ cj := by positivity
  have hcr : 0 ≤ cr := by positivity
  have hcm : 0 ≤ cm := by positivity
  have hcr2 := sq_centralBinom_div_four_pow_le hr
  have hcm2 := sq_centralBinom_div_four_pow_le hm
  set n : ℝ := 2 * ((j : ℝ) + r) + 1 with hn
  set k : ℝ := 2 * (j : ℝ) + 1 with hk
  have hk1 : 1 ≤ k := by rw [hk]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  have hnk : 2 * k ≤ n := by
    have : (2 * j + 1 : ℝ) < 2 * r := by exact_mod_cast (by omega : 2 * j + 1 < 2 * r)
    rw [hn, hk]
    linarith
  -- the factor `A = (π/2) n c_r c_m` is at most `1 + 2k/n`
  have hA : π / 2 * n * cr * cm ≤ 1 + 2 * k / n := by
    have hnpos : 0 < n := by linarith
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hm' : (1 : ℝ) ≤ ((j + r : ℕ) : ℝ) := by exact_mod_cast hm
    have h4rm : (n - k) * (n - 1) = 4 * r * ((j + r : ℕ) : ℝ) := by
      rw [hn, hk]; push_cast; ring
    have hsq : (π / 2 * n * cr * cm) ^ 2 ≤ (1 + 2 * k / n) ^ 2 := by
      have hprod : cr ^ 2 * cm ^ 2 ≤ 1 / (π * r) * (1 / (π * ((j + r : ℕ) : ℝ))) :=
        mul_le_mul hcr2 hcm2 (by positivity) (by positivity)
      have hpi := pi_pos
      calc (π / 2 * n * cr * cm) ^ 2 = π ^ 2 / 4 * n ^ 2 * (cr ^ 2 * cm ^ 2) := by ring
        _ ≤ π ^ 2 / 4 * n ^ 2 * (1 / (π * r) * (1 / (π * ((j + r : ℕ) : ℝ)))) := by gcongr
        _ = n ^ 2 / ((n - k) * (n - 1)) := by rw [h4rm]; field_simp
        _ ≤ (1 + 2 * k / n) ^ 2 := by
          have hden : 0 < (n - k) * (n - 1) := by nlinarith
          rw [div_le_iff₀ hden, show (1 + 2 * k / n) = (n + 2 * k) / n by field_simp, div_pow,
            div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith [pow_four_le_mul_sub_mul_sub hk1 hnk]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc n / k * cj * cr * cm = (π / 2 * n * cr * cm) * (2 / π * (cj / k)) := by
        field_simp
    _ ≤ (1 + 2 * k / n) * (2 / π * (cj / k)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by rw [hn]; push_cast; ring

/-! ### The noise stability of majority -/

/-- A Fourier weight of a Boolean function read as signs is at most `1`. -/
private theorem levelWeight_signVal_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (f : (ι → Bool) → Bool) : levelWeight k (fun x => signVal (f x)) ≤ 1 := by
  by_cases hk : k < Fintype.card ι + 1
  · rw [← sum_levelWeight_signVal f]
    exact single_le_sum (fun i _ => levelWeight_nonneg i _) (mem_range.2 hk)
  · rw [levelWeight_eq_zero_of_card_lt (by omega)]
    exact zero_le_one

/-- The noise stability of majority is the sum over the odd levels of `ρ^k W^k`. -/
private theorem hasSum_noiseStability_signVal_majority (ρ : ℝ) (m : ℕ) :
    HasSum (fun j : ℕ => ρ ^ (2 * j + 1) *
        levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)))
      (noiseStability ρ (fun x => signVal (majority (2 * m + 1) x))) := by
  have hk : HasSum (fun k => ρ ^ k * levelWeight k (fun x => signVal (majority (2 * m + 1) x)))
      (noiseStability ρ (fun x => signVal (majority (2 * m + 1) x))) := by
    rw [noiseStability_eq_sum_levelWeight]
    exact hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [levelWeight_eq_zero_of_card_lt (by
        simp only [mem_range, not_lt, Fintype.card_fin] at hk ⊢; omega), mul_zero]
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b h => by
    simp only at h; omega
  refine (hinj.hasSum_iff (f := fun k =>
    ρ ^ k * levelWeight k (fun x => signVal (majority (2 * m + 1) x))) fun k hk => ?_).2 hk
  have he : Even k := by
    rcases Nat.even_or_odd k with h | ⟨j, rfl⟩
    · exact h
    · exact absurd ⟨j, rfl⟩ hk
  rw [levelWeight_signVal_majority_of_even m he, mul_zero]

/-- **The noise stability of majority** [O'Donnell, Theorem 2.45][ODonnell2014]: for every
`ρ ∈ [-1, 1]`, the noise stability of majority of `2 m + 1` bits, read as signs, tends to
`(2/π) arcsin ρ = 1 - (2/π) arccos ρ` as `m → ∞`. -/
theorem tendsto_noiseStability_signVal_majority {ρ : ℝ} (h₁ : -1 ≤ ρ) (h₂ : ρ ≤ 1) :
    Tendsto (fun m : ℕ => noiseStability ρ (fun x => signVal (majority (2 * m + 1) x))) atTop
      (𝓝 (2 / π * arcsin ρ)) := by
  -- `Stab_1 = 1` for every function read as signs
  have hone (m : ℕ) : noiseStability 1 (fun x => signVal (majority (2 * m + 1) x)) = 1 := by
    simp [noiseStability_one, sq, signVal_mul_self]
  rcases h₂.lt_or_eq with h₂ | rfl
  · rcases h₁.lt_or_eq with h₁ | rfl
    · have hρ : |ρ| < 1 := abs_lt.2 ⟨h₁, h₂⟩
      have hlim : HasSum (fun j : ℕ => ρ ^ (2 * j + 1) *
          (2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1)))) (2 / π * arcsin ρ) := by
        convert (hasSum_arcsin hρ.le).mul_left (2 / π) using 1
        funext j
        ring
      rw [← hlim.tsum_eq]
      have hstab : (fun m : ℕ => noiseStability ρ (fun x => signVal (majority (2 * m + 1) x))) =
          fun m => ∑' j : ℕ, ρ ^ (2 * j + 1) *
            levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) :=
        funext fun m => (hasSum_noiseStability_signVal_majority ρ m).tsum_eq.symm
      rw [hstab]
      refine tendsto_tsum_of_dominated_convergence (bound := fun j => |ρ| * (ρ ^ 2) ^ j) ?_
        (fun j => (tendsto_levelWeight_signVal_majority j).const_mul _) ?_
      · exact (summable_geometric_of_lt_one (sq_nonneg ρ)
          (by nlinarith [abs_nonneg ρ, sq_abs ρ])).mul_left _
      · refine Eventually.of_forall fun m j => ?_
        rw [norm_mul, norm_pow, Real.norm_eq_abs,
          Real.norm_of_nonneg (levelWeight_nonneg _ _), pow_succ, pow_mul, sq_abs, mul_comm |ρ|]
        exact mul_le_of_le_one_right (by positivity) (levelWeight_signVal_le_one _ _)
    · -- at `ρ = -1`, majority has only odd-degree weight, so `Stab_{-1} = -Stab_1 = -1`
      have hneg (m : ℕ) :
          noiseStability (-1) (fun x => signVal (majority (2 * m + 1) x)) = -1 := by
        have h := (hasSum_noiseStability_signVal_majority 1 m).neg
        simp only [one_pow, one_mul, hone] at h
        refine (hasSum_noiseStability_signVal_majority (-1) m).unique ?_
        simpa [pow_succ, pow_mul] using h
      simp only [hneg, arcsin_neg_one]
      convert tendsto_const_nhds using 2
      field_simp
  · simp only [hone, arcsin_one]
    convert tendsto_const_nhds using 2
    field_simp

/-- **The noise stability of majority is at least its limit** [O'Donnell, Theorem 5.18, lower
bound][ODonnell2014]: for `0 ≤ ρ ≤ 1`, `(2/π) arcsin ρ ≤ Stab_ρ[Maj_n]` for majority of every odd
number `n = 2 m + 1` of bits. For `0 < ρ < 1` the noise stability decreases in `n`
(`BitString.noiseStability_signVal_majority_succ_lt`) towards its limit (Theorem 2.45); it is `0`
at `ρ = 0` and `1` at `ρ = 1`. The upper bound is
`BitString.noiseStability_signVal_majority_le`. -/
theorem le_noiseStability_signVal_majority {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (m : ℕ) :
    2 / π * arcsin ρ ≤ noiseStability ρ (fun x => signVal (majority (2 * m + 1) x)) := by
  have hzero (n : ℕ) : noiseStability 0 (fun x => signVal (majority (2 * n + 1) x)) = 0 :=
    (hasSum_noiseStability_signVal_majority 0 n).unique (by simp)
  have hone (n : ℕ) : noiseStability 1 (fun x => signVal (majority (2 * n + 1) x)) = 1 := by
    simp [noiseStability_one, sq, signVal_mul_self]
  have hanti : Antitone fun n : ℕ =>
      noiseStability ρ (fun x => signVal (majority (2 * n + 1) x)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    rcases h₀.lt_or_eq with h₀ | rfl
    · rcases h₁.lt_or_eq with h₁ | rfl
      · exact (noiseStability_signVal_majority_succ_lt n h₀ h₁).le
      · rw [hone, hone]
    · rw [hzero, hzero]
  exact hanti.le_of_tendsto (tendsto_noiseStability_signVal_majority (by linarith) h₁) m

/-- The noise stability of majority of `2 m + 1` bits is the finite sum of `ρ^k W^k` over the odd
levels `k = 2 j + 1 ≤ 2 m + 1`. -/
private theorem noiseStability_signVal_majority_eq_sum (ρ : ℝ) (m : ℕ) :
    noiseStability ρ (fun x => signVal (majority (2 * m + 1) x)) =
      ∑ j ∈ range (m + 1), ρ ^ (2 * j + 1) *
        levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x)) :=
  ((hasSum_noiseStability_signVal_majority ρ m).unique
    (hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [levelWeight_eq_zero_of_card_lt (by
        simp only [mem_range, not_lt] at hj; simp only [Fintype.card_fin]; omega), mul_zero]))

/-- **The upper bound on the noise stability of majority** [O'Donnell, Theorem 5.18, upper bound;
Exercise 5.23][ODonnell2014]: for `0 ≤ ρ < 1`, majority of `n = 2 m + 1` bits has
`Stab_ρ[Maj_n] ≤ (2/π) arcsin ρ + 3 / √((1 - ρ²) n)`, the book's `O(1 / (√(1 - ρ²) √n))` with the
constant `3`. The levels `k < n/2` contribute at most `(1 + 2k/n)` times their limits
(`BitString.levelWeight_signVal_majority_le`), which sum to
`(2/π) arcsin ρ + (2/n) (2/π) ρ / √(1 - ρ²)`; the levels `k ≥ n/2` contribute at most
`ρ^((n+1)/2) ≤ √(2 / ((1 - ρ²) n))`. -/
theorem noiseStability_signVal_majority_le {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ < 1) (m : ℕ) :
    noiseStability ρ (fun x => signVal (majority (2 * m + 1) x)) ≤
      2 / π * arcsin ρ + 3 / √((1 - ρ ^ 2) * (2 * m + 1)) := by
  set W : ℕ → ℝ := fun j => levelWeight (2 * j + 1) (fun x => signVal (majority (2 * m + 1) x))
    with hW
  set L : ℕ → ℝ := fun j => 2 / π * ((Nat.centralBinom j : ℝ) / 4 ^ j / (2 * j + 1)) with hL
  set n : ℝ := 2 * m + 1 with hn
  set t : ℝ := 1 - ρ ^ 2 with ht
  have hρ : |ρ| < 1 := by rw [abs_of_nonneg h₀]; exact h₁
  have hnpos : 0 < n := by positivity
  have htpos : 0 < t := by rw [ht]; nlinarith
  have hpi := pi_pos
  have hL0 (j : ℕ) : 0 ≤ L j := by positivity
  have hW0 (j : ℕ) : 0 ≤ W j := levelWeight_nonneg _ _
  -- the two series of the limits
  have harc : HasSum (fun j : ℕ => ρ ^ (2 * j + 1) * L j) (2 / π * arcsin ρ) := by
    convert (hasSum_arcsin hρ.le).mul_left (2 / π) using 1
    funext j; rw [hL]; ring
  have hder : HasSum (fun j : ℕ => (2 * j + 1) * (ρ ^ (2 * j + 1) * L j))
      (2 / π * ρ / √t) := by
    convert ((hasSum_centralBinom_div_four_pow_mul_pow_two_mul hρ).mul_left (2 / π * ρ)) using 1
    · funext j
      rw [hL]
      field_simp
      ring
    · rw [ht]; field_simp
  -- termwise bound
  have hterm (j : ℕ) : ρ ^ (2 * j + 1) * W j ≤
      ρ ^ (2 * j + 1) * L j + 2 / n * ((2 * j + 1) * (ρ ^ (2 * j + 1) * L j)) +
        ρ ^ (m + 1) * W j := by
    have hpow0 : 0 ≤ ρ ^ (2 * j + 1) := by positivity
    by_cases hj : 2 * (2 * j + 1) < 2 * m + 1
    · have h := levelWeight_signVal_majority_le hj
      have h' : ρ ^ (2 * j + 1) * W j ≤ ρ ^ (2 * j + 1) * ((1 + 2 * (2 * j + 1) / n) * L j) :=
        mul_le_mul_of_nonneg_left h hpow0
      have : ρ ^ (2 * j + 1) * ((1 + 2 * (2 * j + 1) / n) * L j) =
          ρ ^ (2 * j + 1) * L j + 2 / n * ((2 * j + 1) * (ρ ^ (2 * j + 1) * L j)) := by
        field_simp
      have : 0 ≤ ρ ^ (m + 1) * W j := mul_nonneg (pow_nonneg h₀ _) (hW0 j)
      linarith
    · have hle : ρ ^ (2 * j + 1) ≤ ρ ^ (m + 1) :=
        pow_le_pow_of_le_one h₀ h₁.le (by omega)
      have h1 : ρ ^ (2 * j + 1) * W j ≤ ρ ^ (m + 1) * W j := mul_le_mul_of_nonneg_right hle (hW0 j)
      have : 0 ≤ ρ ^ (2 * j + 1) * L j := mul_nonneg hpow0 (hL0 j)
      have : 0 ≤ 2 / n * ((2 * j + 1) * (ρ ^ (2 * j + 1) * L j)) := by positivity
      linarith
  have hsumW : ∑ j ∈ range (m + 1), W j = 1 := by
    have h := noiseStability_signVal_majority_eq_sum 1 m
    simp only [one_pow, one_mul] at h
    rw [← h]
    simp [noiseStability_one, sq, signVal_mul_self]
  have hA : ∑ j ∈ range (m + 1), ρ ^ (2 * j + 1) * L j ≤ 2 / π * arcsin ρ :=
    sum_le_hasSum _ (fun j _ => mul_nonneg (pow_nonneg h₀ _) (hL0 j)) harc
  have hB : ∑ j ∈ range (m + 1), (2 * j + 1) * (ρ ^ (2 * j + 1) * L j) ≤ 2 / π * ρ / √t :=
    sum_le_hasSum _ (fun j _ => by positivity) hder
  have hstab : noiseStability ρ (fun x => signVal (majority (2 * m + 1) x)) ≤
      2 / π * arcsin ρ + 2 / n * (2 / π * ρ / √t) + ρ ^ (m + 1) := by
    rw [noiseStability_signVal_majority_eq_sum]
    calc ∑ j ∈ range (m + 1), ρ ^ (2 * j + 1) * W j
        ≤ ∑ j ∈ range (m + 1), (ρ ^ (2 * j + 1) * L j +
            2 / n * ((2 * j + 1) * (ρ ^ (2 * j + 1) * L j)) + ρ ^ (m + 1) * W j) :=
          sum_le_sum fun j _ => hterm j
      _ = ∑ j ∈ range (m + 1), ρ ^ (2 * j + 1) * L j +
            2 / n * ∑ j ∈ range (m + 1), (2 * j + 1) * (ρ ^ (2 * j + 1) * L j) +
            ρ ^ (m + 1) * ∑ j ∈ range (m + 1), W j := by
          rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum]
      _ ≤ 2 / π * arcsin ρ + 2 / n * (2 / π * ρ / √t) + ρ ^ (m + 1) := by
          rw [hsumW, mul_one]
          gcongr
  -- the error terms
  have hsqrt : √(t * n) = √t * √n := Real.sqrt_mul htpos.le n
  have hsn : 0 < √n := Real.sqrt_pos.2 hnpos
  have hst : 0 < √t := Real.sqrt_pos.2 htpos
  have hn1 : √n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have herr1 : 2 / n * (2 / π * ρ / √t) ≤ (4 / π) / √(t * n) := by
    rw [hsqrt]
    have : 2 / n * (2 / π * ρ / √t) = (4 / π) * ρ / (n * √t) := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 0 ≤ 4 / π := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn1 (mul_nonneg h4 hst.le),
      mul_le_mul_of_nonneg_left h₁.le (mul_nonneg h4 (mul_nonneg hst.le hsn.le))]
  have herr2 : ρ ^ (m + 1) ≤ √2 / √(t * n) := by
    -- `(ρ²)^(m+1) (1 + (m+1) t) ≤ (1 - t)^(m+1) (1 + t)^(m+1) ≤ 1`
    have hb := one_add_mul_le_pow (a := t) (by linarith) (m + 1)
    have hprod : (1 - t) ^ (m + 1) * (1 + t) ^ (m + 1) ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (by nlinarith) (by nlinarith)
    have h1t : 0 ≤ 1 - t := by rw [ht]; nlinarith
    have hsq : (ρ ^ (m + 1)) ^ 2 ≤ 2 / (t * n) := by
      rw [← pow_mul, mul_comm, pow_mul, show ρ ^ 2 = 1 - t by rw [ht]; ring]
      rw [le_div_iff₀ (by positivity)]
      have hmt : (1 : ℝ) + (m + 1 : ℕ) * t ≤ (1 + t) ^ (m + 1) := hb
      have h2 : (1 - t) ^ (m + 1) * (1 + (m + 1 : ℕ) * t) ≤ 1 :=
        (mul_le_mul_of_nonneg_left hmt (pow_nonneg h1t _)).trans hprod
      push_cast at h2
      have h3 : 0 ≤ (1 - t) ^ (m + 1) := pow_nonneg h1t _
      rw [hn]
      nlinarith
    have : ρ ^ (m + 1) ≤ √(2 / (t * n)) := Real.le_sqrt_of_sq_le hsq
    rwa [Real.sqrt_div' 2 (by positivity : (0 : ℝ) ≤ t * n)] at this
  have hconst : 4 / π + √2 ≤ 3 := by
    have h3 := pi_gt_three
    have : 4 / π < 4 / 3 := by rw [div_lt_div_iff₀ hpi (by norm_num)]; linarith
    have : √2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have htn : 0 < √(t * n) := Real.sqrt_pos.2 (by positivity)
  calc noiseStability ρ (fun x => signVal (majority (2 * m + 1) x))
      ≤ 2 / π * arcsin ρ + 2 / n * (2 / π * ρ / √t) + ρ ^ (m + 1) := hstab
    _ ≤ 2 / π * arcsin ρ + (4 / π) / √(t * n) + √2 / √(t * n) := by linarith
    _ = 2 / π * arcsin ρ + (4 / π + √2) / √(t * n) := by ring
    _ ≤ 2 / π * arcsin ρ + 3 / √(t * n) := by gcongr

/-- **The noise sensitivity of majority** [O'Donnell, Theorem 2.45][ODonnell2014], in its
equivalent form: for every `δ ∈ [0, 1]`, the noise sensitivity of majority of `2 m + 1` bits
tends to `arccos(1 - 2δ) / π` as `m → ∞`. -/
theorem tendsto_noiseSensitivity_majority {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) :
    Tendsto (fun m : ℕ => noiseSensitivity δ (majority (2 * m + 1))) atTop
      (𝓝 (arccos (1 - 2 * δ) / π)) := by
  have h := ((tendsto_noiseStability_signVal_majority (ρ := 1 - 2 * δ) (by linarith)
    (by linarith)).const_mul (1 / 2)).const_sub (1 / 2)
  simp only [← noiseSensitivity_eq_noiseStability] at h
  convert h using 2
  rw [arccos_eq_pi_div_two_sub_arcsin]
  field_simp

end Cslib.BitString
