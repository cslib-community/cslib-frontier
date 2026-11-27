/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.CondorcetElection
public import CslibFrontier.Foundations.BooleanAnalysis.MajorityStability
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.Majority
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Guilbaud's formula and the Condorcet bound for fair voting rules

Combining Kalai's formula (`BitString.condorcetWinnerProb_eq`) with the limit of the noise
stability of majority (`BitString.tendsto_noiseStability_signVal_majority`) at `ρ = -1/3` gives
**Guilbaud's formula** (`BitString.tendsto_condorcetWinnerProb_majority`)
[O'Donnell, Section 2.5][ODonnell2014]: in a 3-candidate Condorcet election using majority of
`n` voters, the probability of a Condorcet winner tends to `(3 / (2π)) arccos(-1/3) ≈ 91.2%`.

A voting rule whose degree-one Fourier coefficients are all equal can do only slightly better.
Majority maximizes `∑ᵢ f̂(i)`, which is at most `E|x₁ + ⋯ + xₙ|` (Theorem 2.33), so equal
coefficients give `n W^1[f] ≤ E[|x₁ + ⋯ + xₙ|]²`
(`BitString.card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq`). For odd `n` the right
side divided by `n` is `W^1[Maj_n]`, which tends to `2/π`; since `E|x₁ + ⋯ + xₙ|` increases in `n`
the even case follows, which proves **Proposition 2.58**, `W^1[f] ≤ 2/π + o_n(1)`
(`BitString.eventually_levelWeight_one_le_of_fourierCoeff_singleton_eq`). With Corollary 2.59
this gives **Theorem 2.57**: the probability of a Condorcet winner is at most
`7/9 + 4/(9π) + o_n(1) ≈ 91.9%` (`BitString.eventually_condorcetWinnerProb_le`).

## Main results

* `Cslib.BitString.tendsto_condorcetWinnerProb_majority`: Guilbaud's formula.
* `Cslib.BitString.card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq`: the exact bound
  behind Proposition 2.58.
* `Cslib.BitString.eventually_levelWeight_one_le_of_fourierCoeff_singleton_eq`: Proposition 2.58.
* `Cslib.BitString.eventually_condorcetWinnerProb_le`: Theorem 2.57.

## Usage

The `o_n(1)` terms are stated as: for every `ε > 0`, eventually in `n`, every Boolean function on
`n` bits with equal degree-one coefficients satisfies the bound with `+ ε`. Majority of `n` voters
is `majority (2 * m + 1)` along odd `n = 2 m + 1`, the book's `Maj_n`. Exercise 2.24's rate
`O(1/n)` in Proposition 2.58 is not formalized, and neither is the improvement of Theorem 2.57
to the tight value `(3 / (2π)) arccos(-1/3)` of Chapter 11.7
([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 2.5 and Exercise 2.24.
-/

public section

namespace Cslib.BitString

open Finset Filter Topology Real
open scoped BigOperators

/-! ### Guilbaud's formula -/

/-- **Guilbaud's formula** [O'Donnell, Section 2.5][ODonnell2014]: in a 3-candidate Condorcet
election using majority of `2 m + 1` voters, under impartial culture, the probability of a
Condorcet winner tends to `(3 / (2π)) arccos(-1/3)` as `m → ∞`. -/
theorem tendsto_condorcetWinnerProb_majority :
    Tendsto (fun m : ℕ => condorcetWinnerProb (majority (2 * m + 1))) atTop
      (𝓝 (3 / (2 * π) * arccos (-1 / 3))) := by
  have h := ((tendsto_noiseStability_signVal_majority (ρ := -1 / 3) (by norm_num)
    (by norm_num)).const_mul (3 / 4)).const_sub (3 / 4)
  simp only [← condorcetWinnerProb_eq] at h
  convert h using 2
  rw [arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

/-! ### Equal degree-one coefficients -/

/-- The mean absolute value of the sum of `n` uniform signs increases with `n`. -/
private theorem expect_abs_sum_signVal_le_succ (n : ℕ) :
    𝔼 x : Fin n → Bool, |∑ i, signVal (x i)| ≤
      𝔼 x : Fin (n + 1) → Bool, |∑ i, signVal (x i)| := by
  have hsplit : 𝔼 x : Fin (n + 1) → Bool, |∑ i, signVal (x i)| =
      𝔼 y : Fin n → Bool, 𝔼 b : Bool, |signVal b + ∑ i, signVal (y i)| := by
    rw [← (Fintype.expect_equiv (Fin.consEquiv fun _ => Bool)
      (fun p : Bool × (Fin n → Bool) => |signVal p.1 + ∑ i, signVal (p.2 i)|) _
      fun p => by simp [Fin.sum_univ_succ, Fin.consEquiv]), Fintype.expect_prod_type,
      expect_comm]
  rw [hsplit]
  refine expect_le_expect fun y _ => ?_
  rw [Fintype.expect_bool, signVal_false, signVal_true]
  have h := abs_add_le (1 + ∑ i, signVal (y i)) (-1 + ∑ i, signVal (y i))
  rw [show 1 + ∑ i, signVal (y i) + (-1 + ∑ i, signVal (y i)) = 2 * ∑ i, signVal (y i) by ring,
    abs_mul, abs_two] at h
  linarith

/-- For odd `n = 2 m + 1`, `E[|x₁ + ⋯ + xₙ|]² = n W^1[Maj_n]`. -/
private theorem sq_expect_abs_sum_signVal_two_mul_add_one (m : ℕ) :
    (𝔼 x : Fin (2 * m + 1) → Bool, |∑ i, signVal (x i)|) ^ 2 =
      (2 * m + 1) * levelWeight 1 (fun x => signVal (majority (2 * m + 1) x)) := by
  rw [← sum_fourierCoeff_singleton_majority, levelWeight_one]
  simp only [fourierCoeff_signVal_majority_singleton, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- **Equal degree-one coefficients are at most majority's** [O'Donnell, Section 2.5 and
Exercise 2.24][ODonnell2014]: a Boolean function `f` on `n` bits, read as signs, whose degree-one
Fourier coefficients are all equal has `n W^1[f] ≤ E[|x₁ + ⋯ + xₙ|]²`. For odd `n` the right side
is `n W^1[Maj_n]`. -/
theorem card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq {n : ℕ}
    (f : BooleanFunction n)
    (hf : ∀ i j, fourierCoeff (fun x => signVal (f x)) {i} =
      fourierCoeff (fun x => signVal (f x)) {j}) :
    n * levelWeight 1 (fun x => signVal (f x)) ≤
      (𝔼 x : Fin n → Bool, |∑ i, signVal (x i)|) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set a := fourierCoeff (fun x => signVal (f x)) {⟨0, hn⟩}
  have hsum : ∑ i, fourierCoeff (fun x => signVal (f x)) {i} = n * a := by
    simp [hf _ ⟨0, hn⟩, a]
  -- the negated rule has the negated coefficients
  have hneg : ∑ i, fourierCoeff (fun x => signVal ((fun x => !f x) x)) {i} = -(n * a) := by
    simp only [signVal_not]
    rw [← hsum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simpa using fourierCoeff_const_mul (-1) (fun x => signVal (f x)) {i}
  have hle := sum_fourierCoeff_singleton_signVal_le f
  have hle' := sum_fourierCoeff_singleton_signVal_le (fun x => !f x)
  rw [hsum] at hle
  rw [hneg] at hle'
  have hW : levelWeight 1 (fun x => signVal (f x)) = n * a ^ 2 := by
    simp [levelWeight_one, hf _ ⟨0, hn⟩, a]
  rw [hW, show (n : ℝ) * (n * a ^ 2) = (n * a) ^ 2 by ring]
  exact sq_le_sq' (by linarith) hle

/-- **Proposition 2.58** [O'Donnell, Section 2.5][ODonnell2014]: Boolean functions with all
degree-one Fourier coefficients equal have `W^1[f] ≤ 2/π + o_n(1)`. For every `ε > 0`, eventually
in `n`, every such function on `n` bits, read as signs, has `W^1[f] ≤ 2/π + ε`. -/
theorem eventually_levelWeight_one_le_of_fourierCoeff_singleton_eq {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ f : BooleanFunction n,
      (∀ i j, fourierCoeff (fun x => signVal (f x)) {i} =
        fourierCoeff (fun x => signVal (f x)) {j}) →
      levelWeight 1 (fun x => signVal (f x)) ≤ 2 / π + ε := by
  -- `W^1[Maj_{2m+1}] (2m + 1) / (2m) → 2/π`
  have hratio : Tendsto (fun m : ℕ => (2 * m + 1 : ℝ) / (2 * m)) atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => 1 + (2 * (m : ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (zero_lt_two' ℝ)))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp
  have hlim := (tendsto_levelWeight_signVal_majority 0).mul hratio
  simp only [mul_zero, zero_add, Nat.centralBinom_zero, Nat.cast_one, pow_zero, div_one,
    CharP.cast_eq_zero, mul_one] at hlim
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (eventually_le_nhds
    (by linarith : 2 / π < 2 / π + ε)))
  have hmono : Monotone fun n : ℕ => 𝔼 x : Fin n → Bool, |∑ i, signVal (x i)| :=
    monotone_nat_of_le_succ expect_abs_sum_signVal_le_succ
  filter_upwards [eventually_ge_atTop (2 * (M + 1))] with n hn f hf
  set m := n / 2
  have hm : M + 1 ≤ m := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2m : (2 * m : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * m ≤ n)
  have hT := hmono (show n ≤ 2 * m + 1 by omega)
  have hT0 : 0 ≤ 𝔼 x : Fin n → Bool, |∑ i, signVal (x i)| :=
    expect_nonneg fun x _ => abs_nonneg _
  have hW := card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq f hf
  have hsq := sq_expect_abs_sum_signVal_two_mul_add_one m
  have hbound := hM m (by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < 2 * m := by linarith
  -- `n W^1[f] ≤ T_n² ≤ T_{2m+1}² = (2m + 1) W^1[Maj_{2m+1}]`, and `2m ≤ n`
  have hchain : (2 * m : ℝ) * levelWeight 1 (fun x => signVal (f x)) ≤
      (2 * m + 1) * levelWeight 1 (fun x => signVal (majority (2 * m + 1) x)) := by
    have hWf := levelWeight_nonneg 1 (fun x => signVal (f x))
    calc (2 * m : ℝ) * levelWeight 1 (fun x => signVal (f x))
        ≤ n * levelWeight 1 (fun x => signVal (f x)) := mul_le_mul_of_nonneg_right h2m hWf
      _ ≤ (𝔼 x : Fin n → Bool, |∑ i, signVal (x i)|) ^ 2 := hW
      _ ≤ (𝔼 x : Fin (2 * m + 1) → Bool, |∑ i, signVal (x i)|) ^ 2 :=
          pow_le_pow_left₀ hT0 hT 2
      _ = _ := by rw [hsq]
  rw [← mul_le_mul_iff_of_pos_left hm0]
  calc (2 * m : ℝ) * levelWeight 1 (fun x => signVal (f x))
      ≤ (2 * m + 1) * levelWeight 1 (fun x => signVal (majority (2 * m + 1) x)) := hchain
    _ = 2 * m * (levelWeight 1 (fun x => signVal (majority (2 * m + 1) x)) *
          ((2 * m + 1) / (2 * m))) := by field_simp
    _ ≤ 2 * m * (2 / π + ε) := mul_le_mul_of_nonneg_left hbound hm0.le

/-- **Theorem 2.57** [O'Donnell, Section 2.5][ODonnell2014]: in a 3-candidate Condorcet election
using a voting rule whose degree-one Fourier coefficients are all equal, the probability of a
Condorcet winner is at most `7/9 + 4/(9π) + o_n(1)`. For every `ε > 0`, eventually in `n`, every
such rule on `n` voters has probability at most `7/9 + 4/(9π) + ε`. -/
theorem eventually_condorcetWinnerProb_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ f : BooleanFunction n,
      (∀ i j, fourierCoeff (fun x => signVal (f x)) {i} =
        fourierCoeff (fun x => signVal (f x)) {j}) →
      condorcetWinnerProb f ≤ 7 / 9 + 4 / (9 * π) + ε := by
  filter_upwards [eventually_levelWeight_one_le_of_fourierCoeff_singleton_eq
    (by positivity : 0 < 9 / 2 * ε)] with n hn f hf
  have h1 := condorcetWinnerProb_le f
  have h2 := hn f hf
  have : 2 / 9 * (2 / π + 9 / 2 * ε) = 4 / (9 * π) + ε := by field_simp; ring
  nlinarith

end Cslib.BitString
