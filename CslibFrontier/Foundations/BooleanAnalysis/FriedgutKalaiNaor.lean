/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Anticoncentration
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments
import CslibFrontier.Probability.BitString.Rademacher
import CslibFrontier.Probability.KWiseIndependent.TugOfWar

/-!
# The Friedgut–Kalai–Naor Theorem

A Boolean function `f` whose Fourier weight at degree one is `W^1[f] ≥ 1 - δ` is `O(δ)`-close to a
dictator or a negated dictator `x ↦ ±x_i`: this is the **Friedgut–Kalai–Naor (FKN) Theorem**
[FriedgutKalaiNaor2002] [O'Donnell, Section 2.5][ODonnell2014]. We prove it with the explicit
constants of O'Donnell's proof via the anticoncentration of low-degree functions
[O'Donnell, Section 9.1][ODonnell2014]: if `δ ≤ 1 / 1600`, some degree-one coefficient has
`|f̂({i})| ≥ 1 - 3202 δ` (`BitString.exists_one_sub_le_abs_fourierCoeff_singleton`), and in general
`f` agrees with `x ↦ b ⊕ x_i` for some `i` and `b` except on a fraction at most `1601 δ` of the
inputs (`BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one`). With `δ = 0`, a
Boolean function with `W^1[f] = 1` is a dictator or a negated dictator
(`BitString.exists_eq_xor_of_levelWeight_one_eq_one`)
[O'Donnell, Exercise 1.19(a)][ODonnell2014].

The proof, following O'Donnell, writes `ℓ = f^{=1} = ∑ᵢ f̂({i}) χ_{i}`, so `𝔼 ℓ ^ 2 = W^1[f]` and
`𝔼 (f - ℓ) ^ 2 = 1 - W^1[f] ≤ δ`. The variance of `ℓ ^ 2` is
`2 ((∑ᵢ f̂({i}) ^ 2) ^ 2 - ∑ᵢ f̂({i}) ^ 4)` (`BitString.expect_sum_mul_signVal_sq_sub_expect_sq`)
[O'Donnell, Exercise 1.20][ODonnell2014]; this is the variance of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`) for the identity hash family.
If it exceeded `6400 δ`, then by the anticoncentration of the degree-two function `ℓ ^ 2`
(`BitString.nine_div_sixteen_div_nine_pow_le_dens`), with probability at least `1 / 144` we would
have `|ℓ ^ 2 - 1| > 39 √δ`, hence `(f - ℓ) ^ 2 ≥ 169 δ` (`BitString.mul_le_sq_sub_of_sq_eq_one`,
[O'Donnell, Exercise 9.5][ODonnell2014]), so `𝔼 (f - ℓ) ^ 2 ≥ 169 δ / 144 > δ`. Thus
`∑ᵢ f̂({i}) ^ 4 ≥ 1 - 3202 δ`, which bounds the largest `|f̂({i})|` from below. The distance bound
`1601 δ = (1 - (1 - 3202 δ)) / 2` follows since `f̂({i}) = 1 - 2 dist(f, x ↦ x_i)`; for
`δ > 1 / 1600` it is trivial.

## Main results

* `Cslib.BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one`: the FKN Theorem,
  `W^1[f] ≥ 1 - δ` gives `dist(f, ±χ_i) ≤ 1601 δ` for some `i`.
* `Cslib.BitString.exists_one_sub_le_abs_fourierCoeff_singleton`: its coefficient form,
  `max_i |f̂({i})| ≥ 1 - 3202 δ` for `δ ≤ 1 / 1600`.
* `Cslib.BitString.exists_eq_xor_of_levelWeight_one_eq_one`: `W^1[f] = 1` forces `f = ±χ_i`.
* `Cslib.BitString.expect_sum_mul_signVal_sq_sub_expect_sq`: the variance of the square of a
  homogeneous degree-one function.
* `Cslib.BitString.mul_le_sq_sub_of_sq_eq_one`: the scalar estimate of Exercise 9.5.

## References

* [E. Friedgut, G. Kalai, A. Naor, *Boolean functions whose Fourier transform is concentrated on
  the first two levels*][FriedgutKalaiNaor2002]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- Exercise 9.5 normalised to `f = 1` and `u = √δ`. -/
private theorem sq_mul_le_sq_one_sub {l u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1 / 40)
    (hl : 39 * u < |l ^ 2 - 1|) : 169 * u ^ 2 ≤ (1 - l) ^ 2 := by
  by_contra! hlt
  obtain ⟨h₁, h₂⟩ := abs_lt.mp (abs_lt_of_sq_lt_sq (by nlinarith only [hlt]) (by positivity) :
    |1 - l| < 13 * u)
  rcases abs_cases (l ^ 2 - 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hl <;>
    nlinarith only [hu₀, hu₁, hl, h₁, h₂]

/-- **A sign far from a near-unit square**: if `f ^ 2 = 1`, `0 ≤ δ ≤ 1 / 1600` and
`|ℓ ^ 2 - 1| > 39 √δ`, then `(f - ℓ) ^ 2 ≥ 169 δ` [O'Donnell, Exercise 9.5][ODonnell2014]. -/
theorem mul_le_sq_sub_of_sq_eq_one {f l δ : ℝ} (hf : f ^ 2 = 1) (hδ₀ : 0 ≤ δ)
    (hδ₁ : δ ≤ 1 / 1600) (hl : 39 * √δ < |l ^ 2 - 1|) : 169 * δ ≤ (f - l) ^ 2 := by
  have hu₀ := Real.sqrt_nonneg δ
  have hu₁ : √δ ≤ 1 / 40 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hδ₁]⟩
  have hsq : √δ ^ 2 = δ := Real.sq_sqrt hδ₀
  rcases sq_eq_one_iff.mp hf with rfl | rfl
  · simpa only [hsq] using sq_mul_le_sq_one_sub hu₀ hu₁ hl
  · simpa only [hsq, show (-1 - l) ^ 2 = (1 - -l) ^ 2 by ring] using
      sq_mul_le_sq_one_sub hu₀ hu₁ (l := -l) (by rwa [neg_sq])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The variance of the square of a homogeneous degree-one function**: for `ℓ = ∑ᵢ aᵢ xᵢ`,
`Var[ℓ ^ 2] = 2 ∑_{i ≠ j} aᵢ ^ 2 aⱼ ^ 2 = 2 ((∑ᵢ aᵢ ^ 2) ^ 2 - ∑ᵢ aᵢ ^ 4)`
[O'Donnell, Exercise 1.20][ODonnell2014]. This is the variance of the tug-of-war estimator
(`Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`) for the identity hash
family. -/
theorem expect_sum_mul_signVal_sq_sub_expect_sq (a : ι → ℝ) :
    𝔼 x : ι → Bool, ((∑ i, a i * signVal (x i)) ^ 2 -
        𝔼 y : ι → Bool, (∑ i, a i * signVal (y i)) ^ 2) ^ 2 =
      2 * ((∑ i, a i ^ 2) ^ 2 - ∑ i, a i ^ 4) := by
  rw [expect_sq_sum_mul_signVal]
  exact Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq
    (Probability.isKWiseIndependentHash_id (X := ι) (Y := Bool) 4) signVal_sq expect_bool_signVal
    univ a

/-- **The FKN Theorem**, coefficient form: if a Boolean function `f`, read as signs, has
`W^1[f] ≥ 1 - δ` with `δ ≤ 1 / 1600`, then some degree-one coefficient has
`|f̂({i})| ≥ 1 - 3202 δ` [FriedgutKalaiNaor2002] [O'Donnell, Section 9.1][ODonnell2014]. The
constants are those of O'Donnell's proof. -/
theorem exists_one_sub_le_abs_fourierCoeff_singleton {f : (ι → Bool) → Bool} {δ : ℝ}
    (hδ : δ ≤ 1 / 1600) (hW : 1 - δ ≤ levelWeight 1 (fun x => signVal (f x))) :
    ∃ i, 1 - 3202 * δ ≤ |fourierCoeff (fun x => signVal (f x)) {i}| := by
  classical
  set F : (ι → Bool) → ℝ := fun x => signVal (f x) with hF
  set a : ι → ℝ := fun i => fourierCoeff F {i} with ha
  set ℓ : (ι → Bool) → ℝ := fun x => ∑ i, a i * signVal (x i) with hℓ
  set A := ∑ i, a i ^ 2 with hA
  have hWA : levelWeight 1 F = A := levelWeight_one F
  -- `𝔼 F ℓ = 𝔼 ℓ ^ 2 = A` and `𝔼 F ^ 2 = 1`
  have hFℓ : 𝔼 x, F x * ℓ x = A := by
    simp only [hℓ, mul_sum, expect_sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [show (fun x => F x * (a i * signVal (x i))) = fun x => a i * (F x * chi ℝ {i} x) from
      funext fun x => by rw [chi_singleton]; ring, ← mul_expect, sq]
    rfl
  have hℓℓ : 𝔼 x, ℓ x ^ 2 = A := expect_sq_sum_mul_signVal a
  have hFsq (x : ι → Bool) : F x ^ 2 = 1 := by simp only [hF, sq, signVal_mul_self]
  have hFF : 𝔼 x, F x ^ 2 = 1 := by simp only [hFsq, Fintype.expect_const]
  -- `δ' = 𝔼 (F - ℓ) ^ 2 = 1 - W^1[f] ≤ δ`
  set δ' := 𝔼 x, (F x - ℓ x) ^ 2 with hδ'
  have hδ'A : δ' = 1 - A := by
    rw [hδ', show (fun x => (F x - ℓ x) ^ 2) = fun x => F x ^ 2 - 2 * (F x * ℓ x) + ℓ x ^ 2 from
      funext fun x => by ring, expect_add_distrib, expect_sub_distrib, ← mul_expect, hFF, hFℓ,
      hℓℓ]
    ring
  have hδ'0 : 0 ≤ δ' := expect_nonneg fun x _ => sq_nonneg _
  have hδ'δ : δ' ≤ δ := by rw [hδ'A, ← hWA]; linarith
  have hδ'1 : δ' ≤ 1 / 1600 := hδ'δ.trans hδ
  -- the variance of `ℓ ^ 2` is at most `6400 δ'`
  set V := 𝔼 x, (ℓ x ^ 2 - 𝔼 y, ℓ y ^ 2) ^ 2 with hV
  have hVeq : V = 2 * (A ^ 2 - ∑ i, a i ^ 4) := expect_sum_mul_signVal_sq_sub_expect_sq a
  have hVle : V ≤ 6400 * δ' := by
    by_contra hVgt
    push Not at hVgt
    have hVpos : 0 < V := lt_of_le_of_lt (by positivity) hVgt
    have hℓdeg : (fun x => ℓ x ^ 2) ∈ lowDegree ℝ ι 2 :=
      pow_mem_lowDegree (sum_mul_signVal_mem_lowDegree_one a) 2
    -- by anticoncentration, `|ℓ ^ 2 - A| > √V / 2` with probability at least `1 / 144`
    have h97 : (1 / 144 : ℝ) ≤ (dens {x | √V / 2 < |ℓ x ^ 2 - A|} : ℝ) := by
      have h := nine_div_sixteen_div_nine_pow_le_dens hℓdeg hVpos
      rw [← hV, hℓℓ] at h
      exact le_of_eq_of_le (by norm_num) h
    have hsqrt : 80 * √δ' < √V :=
      Real.lt_sqrt_of_sq_lt (by rw [mul_pow, Real.sq_sqrt hδ'0]; linarith only [hVgt])
    have hδsq : δ' ≤ √δ' := (Real.le_sqrt hδ'0 hδ'0).2 (by nlinarith only [hδ'0, hδ'1])
    -- on that event, `(F - ℓ) ^ 2 ≥ 169 δ'`
    have hd : (dens ({x | √V / 2 < |ℓ x ^ 2 - A|} : Finset (ι → Bool)) : ℝ) ≤
        (dens ({x | 169 * δ' ≤ (F x - ℓ x) ^ 2} : Finset (ι → Bool)) : ℝ) := by
      refine NNRat.cast_le.mpr (dens_le_dens fun x hx => ?_)
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      refine mul_le_sq_sub_of_sq_eq_one (hFsq x) hδ'0 hδ'1 ?_
      have htri : |ℓ x ^ 2 - A| ≤ |ℓ x ^ 2 - 1| + |1 - A| := abs_sub_le _ _ _
      rw [← hδ'A, abs_of_nonneg hδ'0] at htri
      linarith only [htri, hx, hsqrt, hδsq]
    -- so by Markov, `δ' ≥ 169 δ' / 144`, forcing `δ' = 0`
    have hmk := Fintype.mul_dens_filter_le_expect (f := fun x => (F x - ℓ x) ^ 2)
      (fun x => sq_nonneg _) (169 * δ')
    rw [← hδ'] at hmk
    rcases hδ'0.lt_or_eq with hpos | hzero
    · nlinarith only [hpos, h97, hd, hmk]
    · -- `δ' = 0`: then `F = ℓ` and `A = 1`, so `ℓ ^ 2 = A` and the event is empty
      obtain ⟨x, hx⟩ := dens_pos.1 (NNRat.cast_pos.1 (lt_of_lt_of_le (by norm_num) h97))
      have hx0 := congrFun ((Fintype.expect_eq_zero_iff_of_nonneg
        fun x => sq_nonneg (F x - ℓ x)).mp hzero.symm) x
      simp only [mem_filter, mem_univ, true_and, Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero]
        at hx hx0
      rw [← hx0, show A = 1 by linarith only [hzero, hδ'A], hFsq x, sub_self, abs_zero] at hx
      linarith only [hx, Real.sqrt_nonneg V]
  -- hence `∑ᵢ aᵢ ^ 4 ≥ 1 - 3202 δ'`, and the largest `aᵢ ^ 2` bounds it
  have h4 : 1 - 3202 * δ' ≤ ∑ i, a i ^ 4 := by
    nlinarith only [hVle, hVeq, hδ'A, hδ'0]
  cases isEmpty_or_nonempty ι with
  | inl h =>
    -- with no coordinates `W^1[f] = 0`, so `δ' = 1 > 1 / 1600`
    have h0 : A = 0 := by simp [hA, Finset.univ_eq_empty]
    linarith only [h0, hδ'A, hδ'1]
  | inr h =>
    obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ (fun i => a i ^ 2) univ_nonempty
    have hA1 : A ≤ 1 := by linarith only [hδ'A, hδ'0]
    have hsum4 : ∑ i, a i ^ 4 ≤ a i₀ ^ 2 * A := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => by nlinarith only [hi₀ i (mem_univ _), sq_nonneg (a i)]
    have habs1 : |a i₀| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp <| by
      linarith only [hA1, single_le_sum (f := fun i => a i ^ 2) (fun j _ => sq_nonneg _)
        (mem_univ i₀)]
    refine ⟨i₀, ?_⟩
    nlinarith only [h4, hsum4, hδ'δ, hA1, habs1, abs_nonneg (a i₀), sq_abs (a i₀),
      sq_nonneg (a i₀)]

/-- **The Friedgut–Kalai–Naor (FKN) Theorem**: if a Boolean function `f`, read as signs, has
Fourier weight `W^1[f] ≥ 1 - δ` at degree one, then `f` is `1601 δ`-close to a dictator or a
negated dictator: for some coordinate `i` and bit `b`, `f x = b ⊕ x_i` except on a fraction at most
`1601 δ` of the inputs [FriedgutKalaiNaor2002] [O'Donnell, Section 2.5][ODonnell2014]. The
proof is O'Donnell's [O'Donnell, Section 9.1][ODonnell2014]; the constant `1601` is
`3202 / 2`, from his bound `|f̂({i})| ≥ 1 - 3202 δ`. -/
theorem exists_hammingDist_xor_div_le_of_le_levelWeight_one [Nonempty ι]
    {f : (ι → Bool) → Bool} {δ : ℝ} (hW : 1 - δ ≤ levelWeight 1 (fun x => signVal (f x))) :
    ∃ (i : ι) (b : Bool),
      (hammingDist f (fun x => b ^^ x i) : ℝ) / 2 ^ Fintype.card ι ≤ 1601 * δ := by
  classical
  by_cases hδ : δ ≤ 1 / 1600
  · obtain ⟨i, hi⟩ := exists_one_sub_le_abs_fourierCoeff_singleton hδ hW
    set a := fourierCoeff (fun x => signVal (f x)) {i}
    refine ⟨i, decide (a < 0), ?_⟩
    -- the correlation of `f` with `x ↦ b ⊕ x_i` is `signVal b * a = |a|`
    have hcorr := expect_signVal_mul_signVal f (fun x => decide (a < 0) ^^ x i)
    have hcorr' : 𝔼 x, signVal (f x) * signVal (decide (a < 0) ^^ x i) = |a| := by
      have : 𝔼 x, signVal (f x) * signVal (decide (a < 0) ^^ x i) =
          signVal (decide (a < 0)) * a := by
        rw [show a = 𝔼 x, signVal (f x) * chi ℝ {i} x from rfl, mul_expect]
        refine expect_congr rfl fun x _ => ?_
        rw [signVal_xor, chi_singleton]
        ring
      rw [this]
      by_cases ha : a < 0
      · rw [decide_eq_true ha, signVal_true, abs_of_neg ha]; ring
      · rw [decide_eq_false ha, signVal_false, abs_of_nonneg (not_lt.mp ha), one_mul]
    rw [hcorr', mul_div_assoc] at hcorr
    linarith only [hi, hcorr]
  · -- for `δ > 1 / 1600` the bound exceeds one and holds for any `i` and `b`
    push Not at hδ
    refine ⟨Classical.arbitrary ι, false, ?_⟩
    have h1 : (hammingDist f (fun x => false ^^ x (Classical.arbitrary ι)) : ℝ) ≤
        2 ^ Fintype.card ι := by
      have := hammingDist_le_card_fintype (x := f)
        (y := fun x => false ^^ x (Classical.arbitrary ι))
      rw [Fintype.card_fun, Fintype.card_bool] at this
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hδ, h1, pow_pos (by norm_num : (0 : ℝ) < 2) (Fintype.card ι)]

/-- **Boolean functions of degree-one weight one are signed dictators**: if `W^1[f] = 1`, then
`f x = b ⊕ x_i` for some coordinate `i` and bit `b` [O'Donnell, Exercise 1.19(a)][ODonnell2014].
This is the FKN Theorem with `δ = 0`. -/
theorem exists_eq_xor_of_levelWeight_one_eq_one {f : (ι → Bool) → Bool}
    (hW : levelWeight 1 (fun x => signVal (f x)) = 1) :
    ∃ (i : ι) (b : Bool), f = fun x => b ^^ x i := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    rw [levelWeight_one, Finset.univ_eq_empty, sum_empty] at hW
    exact absurd hW zero_ne_one
  | inr h =>
    obtain ⟨i, b, hib⟩ := exists_hammingDist_xor_div_le_of_le_levelWeight_one (f := f) (δ := 0)
      (by rw [hW]; norm_num)
    refine ⟨i, b, hammingDist_eq_zero.mp ?_⟩
    rw [mul_zero, div_le_iff₀ (by positivity), zero_mul] at hib
    exact_mod_cast le_antisymm hib (Nat.cast_nonneg _)

end Cslib.BitString
