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
bound (5.15).

Summing over the levels, with the weights bounded by `1` and the geometric bound `|ρ|^k` for
`|ρ| < 1` (Tannery's theorem), and using the Maclaurin series of `arcsin`
(`Real.hasSum_arcsin`), the noise stability of majority converges:
`Stab_ρ[Maj_n] → (2/π) arcsin ρ` for every `ρ ∈ [-1, 1]`
(`BitString.tendsto_noiseStability_signVal_majority`) [O'Donnell, Theorem 2.45][ODonnell2014].
At `ρ = 1` every function read as signs has `Stab_1 = 1`, and at `ρ = -1` majority, being odd,
has `Stab_{-1} = -1`. For `0 ≤ ρ ≤ 1` the noise stability decreases in `n` (Theorem 5.18), so it
is at least its limit (`BitString.le_noiseStability_signVal_majority`). Equivalently, for
`δ ∈ [0, 1]`, `NS_δ[Maj_n] → arccos(1 - 2δ) / π` (`BitString.tendsto_noiseSensitivity_majority`).

This is the Fourier route of the book's Section 5.3 (the book first proves Theorem 2.45 through
the multidimensional central limit theorem in Section 5.2 and deduces Theorem 5.22 from it, then
proves Theorem 5.22 directly); no central limit theorem is used.

## Main results

* `Cslib.BitString.tendsto_levelWeight_signVal_majority`: the limit in Theorem 5.22.
* `Cslib.BitString.le_levelWeight_signVal_majority`: each weight is at least its limit.
* `Cslib.BitString.tendsto_noiseStability_signVal_majority`: Theorem 2.45.
* `Cslib.BitString.le_noiseStability_signVal_majority`: the lower bound of Theorem 5.18.
* `Cslib.BitString.tendsto_noiseSensitivity_majority`: Theorem 2.45 in noise-sensitivity form.

## Usage

Majority of `2 m + 1` bits read as signs is `fun x => signVal (majority (2 * m + 1) x)`; the
limits are along `m → ∞`, the book's `n → ∞` through the odd numbers. The book's sign convention
differs (`true` reads as `-1`), which changes neither level weights nor noise stability. The book's
form `(4 / (π k 2^k)) C(k - 1, (k - 1)/2)` of the limiting weight is
`2 / π * (Nat.centralBinom j / 4 ^ j / (2 * j + 1))` at `k = 2 j + 1`. The upper half of (5.15),
`W^k[Maj_n] ≤ (1 + 2k/n) [ρ^k] (2/π) arcsin ρ`, the upper bound of Theorem 5.18 and the asymptotics
of Corollary 5.23 are not formalized ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)).

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
tends to `[ρ^k] (2/π) arcsin ρ = (2/π) C(2j, j) / (4^j (2j + 1))` as `m → ∞`. The book's error
bound (5.15) is not part of this statement; its lower half is
`BitString.le_levelWeight_signVal_majority`. -/
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
        convert (hasSum_arcsin hρ).mul_left (2 / π) using 1
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
at `ρ = 0` and `1` at `ρ = 1`. The upper bound of Theorem 5.18 is not formalized. -/
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
