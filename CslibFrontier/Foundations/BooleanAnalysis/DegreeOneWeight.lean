/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
import CslibFrontier.Foundations.BooleanAnalysis.FriedgutKalaiNaor

/-!
# Degree-one weight one and the extremes of noise stability

A Boolean function `f`, read as signs `F = signVal ∘ f`, has squared Fourier coefficients summing
to one, so its weight at degree `k` is `W^k[F] = 1` exactly when its coefficients off the sets of
size `k` vanish (`BitString.levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero`). The functions
with `W^1[F] = 1` are exactly the literals `x ↦ b ⊕ x_i`, the book's `±χ_i`
(`BitString.levelWeight_one_signVal_eq_one_iff`) [O'Donnell, Exercise 1.19(a)][ODonnell2014]: the
forward direction is the Friedgut–Kalai–Naor module's
`BitString.exists_eq_xor_of_levelWeight_one_eq_one`, and every literal has `W^1 = 1` since its only
nonzero coefficient is `±1` on `{i}` (`BitString.fourierCoeff_signVal_xor`).

Since `Stab_ρ[F] = ∑_S ρ ^ |S| F̂(S) ^ 2` and the squares sum to one,
`ρ - Stab_ρ[F] = ∑_S (ρ - ρ ^ |S|) F̂(S) ^ 2`, so a function with `W^1[F] = 1` has `Stab_ρ[F] = ρ`
at every rate
(`BitString.noiseStability_signVal_eq_of_levelWeight_one_eq_one`). This pins down the extremes of
noise stability. For `0 ≤ ρ ≤ 1` an unbiased `F` has `Stab_ρ[F] ≤ ρ`
(`BitString.noiseStability_signVal_le_of_expect_eq_zero`), and for `0 < ρ < 1` equality holds
exactly for the literals (`BitString.noiseStability_signVal_eq_iff_of_expect_eq_zero`)
[O'Donnell, Proposition 2.50][ODonnell2014]. For `-1 ≤ ρ ≤ 0` every `F` has `Stab_ρ[F] ≥ ρ`,
since `ρ ^ k ≥ ρ` for every `k` (`BitString.le_noiseStability_signVal_of_nonpos`), and for
`-1 < ρ < 0` equality holds exactly for the literals
(`BitString.noiseStability_signVal_eq_iff_of_neg`). At `ρ = -1/3` these are the two steps of the
book's proof of Arrow's Theorem from Theorem 2.56 [O'Donnell, Section 2.5][ODonnell2014].

## Main results

* `Cslib.BitString.levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero`: `W^k[F] = 1` exactly
  when the coefficients off the sets of size `k` vanish.
* `Cslib.BitString.levelWeight_one_signVal_eq_one_iff`: Exercise 1.19(a) with its converse.
* `Cslib.BitString.noiseStability_signVal_eq_of_levelWeight_one_eq_one`: `Stab_ρ[F] = ρ` when
  `W^1[F] = 1`.
* `Cslib.BitString.noiseStability_signVal_le_of_expect_eq_zero`,
  `Cslib.BitString.noiseStability_signVal_eq_iff_of_expect_eq_zero`: Proposition 2.50.
* `Cslib.BitString.le_noiseStability_signVal_of_nonpos`,
  `Cslib.BitString.noiseStability_signVal_eq_iff_of_neg`: the negative rates of Arrow's Theorem.

## Usage

Open `Cslib.BitString`. A Boolean function `f : (ι → Bool) → Bool` is read as signs through
`fun x => signVal (f x)`, the book's `±χ_i` are the literals `fun x => b ^^ x i`, `levelWeight 1`
is `W^1` and `noiseStability ρ` is `Stab_ρ`. Unbiasedness is `𝔼 x, signVal (f x) = 0`. The
forward direction of `Cslib.BitString.levelWeight_one_signVal_eq_one_iff` is the `δ = 0` case
`Cslib.BitString.exists_eq_xor_of_levelWeight_one_eq_one` of the Friedgut–Kalai–Naor theorem;
for the coefficients of a single literal use `Cslib.BitString.fourierCoeff_signVal_xor`. The
Proposition 2.50 bound is stated on `0 ≤ ρ ≤ 1`, the book's on `0 < ρ < 1`; its equality case
keeps the open interval, since every unbiased `f` has `Stab_0 = 0` and every `f` has
`Stab_1 = 1`. At negative rates no unbiasedness is needed; at `ρ = 0` equality holds for every
unbiased `f`, and at `ρ = -1` for every function with only odd-degree weight, such as the
majority of three bits. Theorem 2.56, the Condorcet formula `3/4 - 3/4 Stab_{-1/3}[f]`, is not
part of this module.

The checked clients in
[CslibFrontierTests/BooleanAnalysisDegreeOneWeight.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisDegreeOneWeight.lean)
apply these statements to the negated dictator on three bits and the parity of two bits, at
`ρ = 1/2`, `-1/3` and the endpoints, and check that the majority of three bits has
`Stab_{-1} = -1`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Sections 1.7, 2.4 and 2.5.
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Weight one at a single degree -/

/-- **All the weight at one degree, by coefficients**: a Boolean function read as signs has
`W^k[F] = 1` exactly when its Fourier coefficients on the sets of size other than `k` vanish. -/
theorem levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero (k : ℕ) (f : (ι → Bool) → Bool) :
    levelWeight k (fun x => signVal (f x)) = 1 ↔
      ∀ S : Finset ι, #S ≠ k → fourierCoeff (fun x => signVal (f x)) S = 0 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hsplit : levelWeight k F + ∑ S with #S ≠ k, fourierCoeff F S ^ 2 = 1 :=
    (sum_filter_add_sum_filter_not _ _ _).trans (sum_fourierCoeff_sq_signVal f)
  have hrest : levelWeight k F = 1 ↔ ∑ S with #S ≠ k, fourierCoeff F S ^ 2 = 0 := by
    constructor <;> intro h <;> linarith
  rw [hrest, sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  simp only [mem_filter, mem_univ, true_and, sq_eq_zero_iff]

/-- **Boolean functions of degree-one weight one are the literals**: a Boolean function read as
signs has `W^1[F] = 1` if and only if `f x = b ⊕ x_i` for some coordinate `i` and bit `b`
[O'Donnell, Exercise 1.19(a)][ODonnell2014]. The book states the forward direction, with `f = ±χ_i`
in the `±1` encoding; the converse holds since the only nonzero coefficient of `x ↦ b ⊕ x_i` is
`±1`, on `{i}`. -/
theorem levelWeight_one_signVal_eq_one_iff (f : (ι → Bool) → Bool) :
    levelWeight 1 (fun x => signVal (f x)) = 1 ↔ ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  refine ⟨exists_eq_xor_of_levelWeight_one_eq_one, ?_⟩
  rintro ⟨i, b, rfl⟩
  simpa only [levelWeight_one, fourierCoeff_signVal_xor, singleton_inj, ite_pow,
    zero_pow two_ne_zero, sum_ite_eq, mem_univ, ↓reduceIte, sq] using signVal_mul_self b

/-! ### Noise stability at degree one -/

/-- The noise stability below the rate: for a Boolean function read as signs,
`ρ - Stab_ρ[F] = ∑_S (ρ - ρ ^ |S|) F̂(S) ^ 2`, by Parseval and the Fourier formula for the noise
stability [O'Donnell, Theorem 2.49][ODonnell2014]. -/
private theorem sub_noiseStability_signVal_eq_sum (ρ : ℝ) (f : (ι → Bool) → Bool) :
    ρ - noiseStability ρ (fun x => signVal (f x)) =
      ∑ S, (ρ - ρ ^ #S) * fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  nth_rw 1 [← mul_one ρ]
  rw [← sum_fourierCoeff_sq_signVal f, noiseStability_eq_sum, mul_sum, ← sum_sub_distrib]
  simp only [sub_mul]

/-- **Degree-one weight one gives noise stability `ρ`**: a Boolean function read as signs with
`W^1[F] = 1` has `Stab_ρ[F] = ρ` at every rate `ρ`. With
`Cslib.BitString.levelWeight_one_signVal_eq_one_iff` this gives `Stab_ρ[±χ_i] = ρ`
[O'Donnell, Example 2.44][ODonnell2014]. -/
theorem noiseStability_signVal_eq_of_levelWeight_one_eq_one {f : (ι → Bool) → Bool}
    (h : levelWeight 1 (fun x => signVal (f x)) = 1) (ρ : ℝ) :
    noiseStability ρ (fun x => signVal (f x)) = ρ := by
  have hoff := (levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero 1 f).1 h
  refine (sub_eq_zero.1 ?_).symm
  rw [sub_noiseStability_signVal_eq_sum]
  refine sum_eq_zero fun S _ => ?_
  by_cases hS : #S = 1
  · rw [hS, pow_one, sub_self, zero_mul]
  · rw [hoff S hS, sq, mul_zero, mul_zero]

/-- If `Stab_ρ[F] = ρ` and, scaled by `σ`, the factor `ρ - ρ ^ |S|` is positive on every set of size
other than one where `F̂(S) ≠ 0`, then `W^1[F] = 1`. -/
private theorem levelWeight_one_eq_one_of_noiseStability_eq {ρ σ : ℝ} {f : (ι → Bool) → Bool}
    (hpos : ∀ S : Finset ι, #S ≠ 1 →
      fourierCoeff (fun x => signVal (f x)) S = 0 ∨ 0 < σ * (ρ - ρ ^ #S))
    (h : noiseStability ρ (fun x => signVal (f x)) = ρ) :
    levelWeight 1 (fun x => signVal (f x)) = 1 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hterm (S : Finset ι) : 0 ≤ σ * ((ρ - ρ ^ #S) * fourierCoeff F S ^ 2) := by
    by_cases hS : #S = 1
    · simp [hS]
    exact (hpos S hS).elim (fun h0 => by simp [h0]) fun h0 =>
      mul_assoc σ _ _ ▸ mul_nonneg h0.le (sq_nonneg _)
  have hzero := (sum_eq_zero_iff_of_nonneg fun S _ => hterm S).1 <| by
    rw [← mul_sum, ← sub_noiseStability_signVal_eq_sum, h, sub_self, mul_zero]
  exact (levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero 1 f).2 fun S hS =>
    (hpos S hS).elim id fun h0 => sq_eq_zero_iff.1
      ((mul_eq_zero.1 (mul_assoc σ _ _ ▸ hzero S (mem_univ S))).resolve_left h0.ne')

/-- **Unbiased functions are at most as noise-stable as the dictators**: for `0 ≤ ρ ≤ 1`, an
unbiased Boolean function read as signs has `Stab_ρ[F] ≤ ρ`
[O'Donnell, Proposition 2.50][ODonnell2014]. The book states it for `0 < ρ < 1`; the bound holds
on the closed interval. -/
theorem noiseStability_signVal_le_of_expect_eq_zero {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1)
    {f : (ι → Bool) → Bool} (hf : 𝔼 x, signVal (f x) = 0) :
    noiseStability ρ (fun x => signVal (f x)) ≤ ρ := by
  refine sub_nonneg.1 ((sub_noiseStability_signVal_eq_sum ρ f).symm ▸ sum_nonneg fun S _ => ?_)
  by_cases hS : S = ∅
  · simp [hS, hf]
  exact mul_nonneg (sub_nonneg.2 (pow_le_of_le_one h₀ h₁
    (card_ne_zero.2 (ne_empty_iff_nonempty.1 hS)))) (sq_nonneg _)

/-- **The unbiased functions of largest noise stability are the literals**: for `0 < ρ < 1`, an
unbiased Boolean function read as signs has `Stab_ρ[F] = ρ` exactly when `f x = b ⊕ x_i` for some
coordinate `i` and bit `b` [O'Donnell, Proposition 2.50][ODonnell2014]. The book writes the
literals as `±χ_i`. The equality case needs the open interval: at `ρ = 0` every unbiased `F` has
`Stab_0[F] = (𝔼 F) ^ 2 = 0`, and at `ρ = 1` every `F` has `Stab_1[F] = 𝔼 F ^ 2 = 1`. -/
theorem noiseStability_signVal_eq_iff_of_expect_eq_zero {ρ : ℝ} (h₀ : 0 < ρ) (h₁ : ρ < 1)
    {f : (ι → Bool) → Bool} (hf : 𝔼 x, signVal (f x) = 0) :
    noiseStability ρ (fun x => signVal (f x)) = ρ ↔
      ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [← levelWeight_one_signVal_eq_one_iff]
  refine ⟨levelWeight_one_eq_one_of_noiseStability_eq (σ := 1) fun S hS => ?_,
    fun h => noiseStability_signVal_eq_of_levelWeight_one_eq_one h ρ⟩
  by_cases h0 : S = ∅
  · exact .inl (by simp [h0, hf])
  have := card_pos.2 (ne_empty_iff_nonempty.1 h0)
  exact .inr (by simpa using pow_lt_self_of_lt_one₀ h₀ h₁ (by omega))

/-- For `-1 ≤ ρ ≤ 0`, `ρ ≤ ρ ^ k` for every `k`. -/
private theorem le_pow_of_nonpos {ρ : ℝ} (h₁ : -1 ≤ ρ) (h₀ : ρ ≤ 0) (k : ℕ) : ρ ≤ ρ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · linarith [pow_zero ρ]
  have habs := pow_le_of_le_one (abs_nonneg _) (abs_le.2 ⟨h₁, by linarith⟩) hk.ne'
  have hle : -|ρ| ^ k ≤ ρ ^ k := abs_pow ρ k ▸ neg_abs_le _
  rw [abs_of_nonpos h₀] at habs hle; linarith

/-- For `-1 < ρ < 0`, `ρ < ρ ^ k` for every `k ≠ 1`. -/
private theorem lt_pow_of_neg {ρ : ℝ} (h₁ : -1 < ρ) (h₀ : ρ < 0) {k : ℕ} (hk : k ≠ 1) :
    ρ < ρ ^ k := by
  rcases Nat.lt_or_gt_of_ne hk with hk | hk
  · rw [Nat.lt_one_iff.1 hk]; linarith [pow_zero ρ]
  · have habs := pow_lt_self_of_lt_one₀ (abs_pos.2 h₀.ne) (abs_lt.2 ⟨h₁, by linarith⟩) hk
    have hle : -|ρ| ^ k ≤ ρ ^ k := abs_pow ρ k ▸ neg_abs_le _
    rw [abs_of_neg h₀] at habs hle; linarith

/-- **Noise stability at a nonpositive rate is at least the rate**: for `-1 ≤ ρ ≤ 0`, a Boolean
function read as signs has `Stab_ρ[F] ≥ ρ`. The book uses the case `ρ = -1/3`, through
`(-1/3) ^ k ≥ -1/3`, in its proof of Arrow's Theorem [O'Donnell, Section 2.5][ODonnell2014]; no
unbiasedness is needed. -/
theorem le_noiseStability_signVal_of_nonpos {ρ : ℝ} (h₁ : -1 ≤ ρ) (h₀ : ρ ≤ 0)
    (f : (ι → Bool) → Bool) : ρ ≤ noiseStability ρ (fun x => signVal (f x)) := by
  refine sub_nonpos.1 ?_
  rw [sub_noiseStability_signVal_eq_sum]
  exact sum_nonpos fun S _ =>
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (le_pow_of_nonpos h₁ h₀ _)) (sq_nonneg _)

/-- **The functions of least noise stability at a negative rate are the literals**: for
`-1 < ρ < 0`, a Boolean function read as signs has `Stab_ρ[F] = ρ` exactly when `f x = b ⊕ x_i`
for some coordinate `i` and bit `b`. The book uses the forward direction at `ρ = -1/3`, where
`Stab_{-1/3}[F] = -1/3` forces `W^1[F] = 1` and then `f = ±χ_i` by Exercise 1.19(a), in its proof
of Arrow's Theorem [O'Donnell, Section 2.5][ODonnell2014]. Both endpoints are excluded. At
`ρ = 0`, `Stab_0[F] = (𝔼 F) ^ 2`, which is `0` exactly for the unbiased `f`, not only the literals.
At `ρ = -1`, every function with only odd-degree weight, such as the majority of three bits, has
`Stab_{-1}[F] = -1`. -/
theorem noiseStability_signVal_eq_iff_of_neg {ρ : ℝ} (h₁ : -1 < ρ) (h₀ : ρ < 0)
    (f : (ι → Bool) → Bool) :
    noiseStability ρ (fun x => signVal (f x)) = ρ ↔
      ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  rw [← levelWeight_one_signVal_eq_one_iff]
  exact ⟨levelWeight_one_eq_one_of_noiseStability_eq (σ := -1) fun _ hS =>
    .inr (by simpa using lt_pow_of_neg h₁ h₀ hS),
    fun h => noiseStability_signVal_eq_of_levelWeight_one_eq_one h ρ⟩

end Cslib.BitString
