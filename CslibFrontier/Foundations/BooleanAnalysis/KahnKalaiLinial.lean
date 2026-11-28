/-
Copyright (c) 2026 Samuel Schlesinger, Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity
import CslibFrontier.Foundations.BooleanAnalysis.Monotone
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import CslibFrontier.Foundations.BooleanAnalysis.StableInfluenceBound

/-!
# The Kahn–Kalai–Linial theorem and Talagrand's inequality

Read a Boolean function `f` as the function `F = (-1) ^ f` with values `±1`, and write
`Ĩ = I[F] / Var[F]`. By the Poincaré inequality the influences of `F` on its `n` coordinates
average at least `Var[F] / n`, and `Ĩ ≥ 1`. The **KKL Edge-Isoperimetric Theorem** of
[O'Donnell][ODonnell2014], Section 9.6, says that a nonconstant `F` has a coordinate of influence
at least `(9 / Ĩ²) 9^{-Ĩ}` (`BitString.exists_nine_div_sq_mul_one_ninth_rpow_le_influence`). We
prove it with the book's constants, in the general-variance form asked for in its Exercise 9.29;
the book's remark `Ĩ ≥ 1` is not a hypothesis. As in the book, splitting on whether
`Ĩ ≥ log n / 4` turns it into the **Kahn–Kalai–Linial theorem** [KahnKalaiLinial1988]: some
coordinate has influence at least `Var[F] · log n / (4 n)`
(`BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence`). Here `Var[F]` is written
`𝔼 x, (F x - 𝔼 y, F y) ^ 2`, the Fourier weight of `F` on the nonempty sets.

For a monotone `f` the influence of `i` is the degree-one coefficient `F̂({i})`
[O'Donnell][ODonnell2014], Proposition 2.21, and `(9 / Ĩ²) 9^{-Ĩ} ≥ exp(-5 Ĩ)`, so a nonconstant
monotone function has a coordinate with `F̂({i})² ≥ exp(-10 Ĩ)`: O'Donnell's Exercise 9.33
(`BitString.exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone`).

The same use of hypercontractivity, run separately on each coordinate, proves **Talagrand's
inequality** `Var[F] ≤ 6 ∑ᵢ Infᵢ[F] / log (1 / Infᵢ[F])`, for functions whose influences are all
less than one (`BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log`)
[Talagrand1994]; the form `Var[F] ≤ 7 ∑ᵢ Infᵢ[F] / (1 + log (1 / Infᵢ[F]))` holds for every
Boolean function (`BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`).

## Proof

The derivative `Dᵢ F` takes the values `0` and `±1`, so `‖Dᵢ F‖_{4/3} ^ 2 = Infᵢ[F] ^ (3/2)`,
and the `(4/3, 2)`-Hypercontractivity Theorem bounds the stable influence
`Infᵢ^{(1/3)}[F] = Stab_{1/3}[Dᵢ F] ≤ ‖Dᵢ F‖_{4/3} ^ 2`: this is Corollary 9.12 of the book, the
case `ρ = 1/3` of `Infᵢ^{(ρ)}[F] ≤ Infᵢ[F] ^ (2 / (1 + ρ))`
(`BitString.stableInfluence_signVal_le_influence_rpow`, Corollary 9.25, in
`CslibFrontier.Foundations.BooleanAnalysis.StableInfluenceBound`). It bounds the low-degree part of
the Fourier weight on the sets containing `i` (`BitString.mul_noiseStability_derivative`,
`BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le`):

  `∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 = 1/3 · Infᵢ^{(1/3)}[F] ≤ 1/3 · Infᵢ[F] ^ (3/2)`.

For the Edge-Isoperimetric Theorem, with `M` the largest influence, this gives the book's chain
`Var[F] 3^{-Ĩ} ≤ ∑_{S ≠ ∅} 3^{-|S|} F̂(S)² ≤ ∑ᵢ ∑_{S ∋ i} 3^{-|S|} F̂(S)² ≤ ∑ᵢ Infᵢ[F]^{3/2} / 3
≤ √M I[F] / 3`. Its first step is the hint of Exercise 9.29: Jensen's inequality for the convex
function `s ↦ 3^{-s}` and the weights `F̂(S)²` on the nonempty sets
(`BitString.expect_sub_expect_sq_mul_one_third_rpow_le`).

For Talagrand's inequality, the variance is `∑ᵢ ∑_{S ∋ i} F̂(S) ^ 2 / |S|`. For `A > 1` and every
`m ≥ 1`, `1 / m ≤ log 3 / log A + A 3 ^ (-m)`, according as `3 ^ m ≥ A` or not, so the weight on
the sets containing `i` is at most `log 3 / log A · Infᵢ[F] + A / 3 · Infᵢ[F] ^ (3/2)`. If
`Infᵢ[F] ≤ δ < 1`, the choice `A = δ ^ (-1/4)` and the bound `δ ^ (1/4) log (1 / δ) < 4` turn
this into `6 Infᵢ[F] / log (1 / δ)`; taking `δ = Infᵢ[F]` gives Talagrand's inequality.

## Main results

* `Cslib.BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le`: hypercontractivity
  bounds the low-degree weight on the sets containing a coordinate.
* `Cslib.BitString.expect_sub_expect_sq_mul_one_third_rpow_le`: the convexity step.
* `Cslib.BitString.exists_nine_div_sq_mul_one_ninth_rpow_le_influence`: the KKL
  Edge-Isoperimetric Theorem.
* `Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence`: the
  Kahn–Kalai–Linial theorem.
* `Cslib.BitString.exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone`: a nonconstant
  monotone function has a large degree-one coefficient [O'Donnell][ODonnell2014], Exercise 9.33.
* `Cslib.BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log`,
  `Cslib.BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`: Talagrand's
  inequality.

## Usage

For `f : (ι → Bool) → Bool` over a finite coordinate type `ι`, pass a proof `hV` that the
variance `𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2` is positive (that is, `f` is
nonconstant) to `exists_nine_div_sq_mul_one_ninth_rpow_le_influence f hV`; it returns a coordinate
`i` with `(9 / Ĩ²) 9^{-Ĩ} ≤ influence i (fun x => signVal (f x))`, where `Ĩ` is written out as
`totalInfluence (fun x => signVal (f x))` divided by the variance. Rewriting the variance and the
total influence of a concrete function turns the bound into a number. With `[Nonempty ι]`,
`exists_expect_sub_expect_sq_mul_log_card_div_le_influence f` needs no hypothesis; a lower bound on
the variance, such as `three_div_four_le_expect_sub_expect_sq_tribes`, makes it explicit. The
checked clients in
[CslibFrontierTests/KahnKalaiLinial.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/KahnKalaiLinial.lean)
compute variances and total influences from Fourier weights, apply the convexity step to
`χ_{0} + χ_{0,1}` on two bits (`Var = 2`, `I = 3`, giving `2 · 3^{-3/2} ≤ 4 / 9`), apply the
theorem to a dictator (`Ĩ = 1`, giving influence `1`, the maximum possible), and apply the
Kahn–Kalai–Linial bound to the nearly balanced Tribes function.

`expect_sub_expect_sq_signVal_pos` in `CslibFrontier.Foundations.BooleanAnalysis.Variance` turns
a nonconstancy witness `hc : ∃ x y, f x ≠ f y` into the hypothesis `hV`. For a monotone `f`
(`hf : Monotone f`), `exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone hf hc` returns a
coordinate `i` with `exp (-(10 * I / V)) ≤ fourierCoeff (fun x => signVal (f x)) {i} ^ 2`, where
`I = totalInfluence (fun x => signVal (f x))` and `V` is the variance. Both hypotheses are
needed: a constant function has `V = 0`, so the bound reads `exp 0 = 1`, while every degree-one
coefficient is `0`; the parity of two bits is nonconstant and has no nonzero degree-one
coefficient. The checked client
[CslibFrontierTests/BooleanAnalysisMonotoneCoefficient.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisMonotoneCoefficient.lean)
applies it to the conjunction of two bits, with `V = 3 / 4` and `I ≤ 2`, and gets a squared
degree-one coefficient of at least `exp(-27)`.

## References

* [J. Kahn, G. Kalai and N. Linial, *The influence of variables on Boolean
  functions*][KahnKalaiLinial1988]
* [M. Talagrand, *On Russo's approximate zero-one law*][Talagrand1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hypercontractivity on the derivatives -/

/-- **Hypercontractivity bounds the low-degree weight on the sets containing a coordinate**: for a
Boolean function read as signs, `∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 = 1/3 · Infᵢ^{(1/3)}[F]`, which
is at most `1/3 · Infᵢ[F] ^ (3/2)` by `stableInfluence_signVal_le_influence_rpow` at `ρ = 1/3`
[O'Donnell, Corollary 9.12][ODonnell2014]. -/
theorem sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le (f : (ι → Bool) → Bool) (i : ι) :
    ∑ S with i ∈ S, (1 / 3 : ℝ) ^ #S * fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      influence i (fun x => signVal (f x)) * √(influence i fun x => signVal (f x)) / 3 := by
  have h := stableInfluence_signVal_le_influence_rpow (ρ := 1 / 3) (by norm_num) (by norm_num) f i
  rw [show (2 : ℝ) / (1 + 1 / 3) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' (influence_nonneg i _) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow,
    stableInfluence_eq_noiseStability_derivative] at h
  rw [← mul_noiseStability_derivative]
  linarith

/-- Summing a weight over the sets containing each coordinate counts every set `|S|` times. -/
private theorem sum_sum_filter_mem (g : Finset ι → ℝ) :
    ∑ i, ∑ S with i ∈ S, g S = ∑ S, (#S : ℝ) * g S := by
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]

/-! ### The Kahn–Kalai–Linial theorem -/

/-- **The convexity step** of [O'Donnell][ODonnell2014], Exercise 9.29: for every real `F` with
variance `V` and total influence `I`, `V 3^{-I / V} ≤ ∑_{S ≠ ∅} 3^{-|S|} F̂(S)²`, by Jensen's
inequality for `s ↦ 3^{-s}` and the weights `F̂(S)²`. For `V = 0` the left side is zero. -/
theorem expect_sub_expect_sq_mul_one_third_rpow_le (F : (ι → Bool) → ℝ) :
    (𝔼 x, (F x - 𝔼 y, F y) ^ 2) * (1 / 3 : ℝ) ^ (totalInfluence F / 𝔼 x, (F x - 𝔼 y, F y) ^ 2)
      ≤ ∑ S with S ≠ ∅, (1 / 3 : ℝ) ^ #S * fourierCoeff F S ^ 2 := by
  set V := 𝔼 x, (F x - 𝔼 y, F y) ^ 2
  have hV0 : 0 ≤ V := expect_nonneg fun _ _ => sq_nonneg _
  rcases hV0.eq_or_lt with hV | hV
  · rw [← hV, zero_mul]
    positivity
  have hVsum : ∑ S with S ≠ ∅, fourierCoeff F S ^ 2 = V :=
    (expect_sub_expect_sq_eq_sum_fourierCoeff_sq F).symm
  have hIsum : ∑ S with S ≠ ∅, fourierCoeff F S ^ 2 * #S = totalInfluence F := by
    rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq, sum_filter]
    exact sum_congr rfl fun S _ => by split_ifs with h <;> simp_all [mul_comm]
  -- Jensen's inequality for `s ↦ 3^{-s}` at the points `|S|`, with the weights `F̂(S)²`
  have hJ := (convexOn_rpow_left (b := 1 / 3) (by norm_num)).map_centerMass_le
    (t := univ.filter (· ≠ ∅)) (w := fun S => fourierCoeff F S ^ 2) (p := fun S => (#S : ℝ))
    (fun _ _ => sq_nonneg _) (hVsum ▸ hV) fun _ _ => Set.mem_univ _
  simp only [centerMass, Function.comp_def, smul_eq_mul, hVsum, hIsum, rpow_natCast] at hJ
  rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀' hV] at hJ
  simpa only [mul_comm (fourierCoeff F _ ^ 2)] using hJ

/-- **The KKL Edge-Isoperimetric Theorem** of [O'Donnell][ODonnell2014], Section 9.6, in the
general-variance form of its Exercise 9.29: for a nonconstant Boolean function `f`, read as signs,
with `Ĩ = I[f] / Var[f]`, some coordinate has influence at least `(9 / Ĩ²) 9^{-Ĩ}`. -/
theorem exists_nine_div_sq_mul_one_ninth_rpow_le_influence (f : (ι → Bool) → Bool)
    (hV : 0 < 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) :
    ∃ i, 9 / (totalInfluence (fun x => signVal (f x)) /
          𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) ^ 2 *
        (1 / 9 : ℝ) ^ (totalInfluence (fun x => signVal (f x)) /
          𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) ≤
      influence i fun x => signVal (f x) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set V := 𝔼 x, (F x - 𝔼 y, F y) ^ 2
  set I := totalInfluence F
  have hI : 0 < I := hV.trans_le (expect_sub_expect_sq_le_totalInfluence F)
  -- a nonconstant function has a coordinate, hence a most influential one
  obtain ⟨i, -, hi⟩ :=
    exists_max_image univ (fun i => influence i F) (nonempty_of_sum_ne_zero hI.ne')
  refine ⟨i, ?_⟩
  set M := influence i F
  set a := (1 / 3 : ℝ) ^ (I / V)
  -- the chain `V 3^{-I/V} ≤ ∑_{S ≠ ∅} 3^{-|S|} F̂(S)² ≤ √M I / 3`
  have hchain : V * a ≤ √M * I / 3 := by
    refine (expect_sub_expect_sq_mul_one_third_rpow_le F).trans ?_
    calc ∑ S with S ≠ ∅, (1 / 3 : ℝ) ^ #S * fourierCoeff F S ^ 2
        ≤ ∑ S, (#S : ℝ) * ((1 / 3 : ℝ) ^ #S * fourierCoeff F S ^ 2) := by
          rw [sum_filter]
          refine sum_le_sum fun S _ => ?_
          split_ifs with h
          · exact le_mul_of_one_le_left (by positivity)
              (Nat.one_le_cast.2 (card_pos.2 (ne_empty_iff_nonempty.1 h)))
          · positivity
      _ = ∑ j, ∑ S with j ∈ S, (1 / 3 : ℝ) ^ #S * fourierCoeff F S ^ 2 :=
          (sum_sum_filter_mem _).symm
      _ ≤ ∑ j, influence j F * √M / 3 := sum_le_sum fun j _ =>
          (sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le f j).trans <| by
            have := influence_nonneg j F
            gcongr
            exact hi j (mem_univ j)
      _ = √M * I / 3 := by rw [← sum_div, ← sum_mul, mul_comm]; rfl
  have h3 : 3 * V * a / I ≤ √M := by rw [div_le_iff₀ hI]; linarith
  calc 9 / (I / V) ^ 2 * (1 / 9 : ℝ) ^ (I / V) = (3 * V * a / I) ^ 2 := by
        rw [show (1 / 9 : ℝ) = 1 / 3 * (1 / 3) by norm_num, mul_rpow (by norm_num) (by norm_num)]
        field_simp
        ring
    _ ≤ √M ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    _ = M := sq_sqrt (influence_nonneg i F)

/-- `L³ ≤ 576 exp (L (1 - log 9 / 4))` for `L ≥ 0`: with `L = log n`, this is
`log³ n ≤ 576 n ^ (1 - log 9 / 4)`. -/
private theorem pow_three_le_mul_exp {L : ℝ} (hL : 0 ≤ L) :
    L ^ 3 ≤ 576 * exp (L - L * log 9 / 4) := by
  -- `c = 1 - log 9 / 4 ≥ 3 / 10`, as `log 9 ≤ 4 log 2`
  have h9 : log 9 ≤ 4 * log 2 := by
    rw [← log_rpow (by norm_num)]
    exact log_le_log (by norm_num) (by norm_num)
  have h2 := log_two_lt_d9
  norm_num at h2
  have hc : 3 / 10 ≤ 1 - log 9 / 4 := by linarith
  -- `(c L)³ / 3! ≤ exp (c L)`
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg (hc.trans' (by norm_num)) hL) 3
  have hc3 : (3 / 10 : ℝ) ^ 3 * L ^ 3 ≤ (1 - log 9 / 4) ^ 3 * L ^ 3 := by gcongr
  rw [show L - L * log 9 / 4 = (1 - log 9 / 4) * L by ring]
  norm_num [Nat.factorial, mul_pow] at h
  nlinarith [exp_pos ((1 - log 9 / 4) * L)]

/-- **The Kahn–Kalai–Linial theorem** [KahnKalaiLinial1988], derived from the Edge-Isoperimetric
version as in [O'Donnell][ODonnell2014], Section 9.6: some coordinate has influence at least
`Var[F] · log n / (4 n)` on a Boolean function read as signs `F` of `n ≥ 1` coordinates. If
`Ĩ ≥ log n / 4`, the average influence `I[F] / n` is large enough; otherwise the KKL
Edge-Isoperimetric Theorem gives `MaxInf ≥ 144 / log² n · n^{-log 9 / 4}`, which is larger. -/
theorem exists_expect_sub_expect_sq_mul_log_card_div_le_influence [Nonempty ι]
    (f : (ι → Bool) → Bool) :
    ∃ i, (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * log (Fintype.card ι) /
      (4 * Fintype.card ι) ≤ influence i (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set V := 𝔼 x, (F x - 𝔼 y, F y) ^ 2
  set I := totalInfluence F
  set n : ℝ := (Fintype.card ι : ℝ)
  set L := log n
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => influence i F) univ_nonempty
  refine ⟨i, ?_⟩
  set M := influence i F
  have hn0 : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hL : 0 ≤ L := log_nonneg (Nat.one_le_cast.2 Fintype.card_pos)
  have hV1 : V ≤ 1 := expect_sub_expect_sq_signVal_le_one f
  have hIM : I ≤ n * M :=
    (sum_le_sum fun j _ => hi j (mem_univ j)).trans_eq (by rw [sum_const, card_univ, nsmul_eq_mul])
  rw [div_le_iff₀ (by positivity)]
  have hV0 : 0 ≤ V := expect_nonneg fun _ _ => sq_nonneg _
  rcases hV0.eq_or_lt with hV | hV
  · rw [← hV, zero_mul]
    exact mul_nonneg (influence_nonneg i F) (by positivity)
  rcases le_or_gt (V * L) (4 * I) with h | h
  · -- a large total influence: `V L ≤ 4 I ≤ 4 n M`
    nlinarith
  · -- `Ĩ < L / 4`: the edge-isoperimetric bound `M ≥ 144 / L² · n^{-log 9 / 4}`
    obtain ⟨j, hj⟩ := exists_nine_div_sq_mul_one_ninth_rpow_le_influence f hV
    have hjM : influence j F ≤ M := hi j (mem_univ j)
    set T := I / V
    have hT1 : 1 ≤ T := (one_le_div hV).2 (expect_sub_expect_sq_le_totalInfluence F)
    have hTL : T ≤ L / 4 := by rw [div_le_iff₀ hV]; linarith
    have hL0 : 0 < L := by linarith
    have hpow : exp (-(L * log 9 / 4)) ≤ (1 / 9 : ℝ) ^ T := by
      rw [rpow_def_of_pos (by norm_num), exp_le_exp, one_div, log_inv]
      nlinarith [log_pos (by norm_num : (1 : ℝ) < 9)]
    have hsq : 144 / L ^ 2 ≤ 9 / T ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hM : 144 / L ^ 2 * exp (-(L * log 9 / 4)) ≤ M :=
      (mul_le_mul hsq hpow (exp_pos _).le (by positivity)).trans (hj.trans hjM)
    have hkey := pow_three_le_mul_exp hL0.le
    have hnL : n = exp L := (exp_log hn0).symm
    have hsplit : exp (L - L * log 9 / 4) = n * exp (-(L * log 9 / 4)) := by
      rw [hnL, ← exp_add]; ring_nf
    rw [hsplit] at hkey
    -- `V L ≤ L = L³ / L² ≤ 576 n 9^{-L/4} / L² ≤ 4 n M`
    have : L ≤ 4 * n * (144 / L ^ 2 * exp (-(L * log 9 / 4))) := by
      rw [show 4 * n * (144 / L ^ 2 * exp (-(L * log 9 / 4))) =
        576 * (n * exp (-(L * log 9 / 4))) / L ^ 2 by ring, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith

/-! ### Monotone functions -/

/-- `exp (-5 t) ≤ (9 / t²) 9^{-t}` for `t > 0`, since `log t ≤ t - 1` and `log 9 < 3`. -/
private theorem exp_neg_five_mul_le_nine_div_sq_mul {t : ℝ} (ht : 0 < t) :
    exp (-(5 * t)) ≤ 9 / t ^ 2 * (1 / 9 : ℝ) ^ t := by
  rw [← le_log_iff_exp_le (by positivity), log_mul (by positivity) (by positivity),
    log_div (by norm_num) (by positivity), log_pow, log_rpow (by norm_num), one_div, log_inv]
  have h9 : log 9 < 3 := by
    have h3 := log_three_lt_d9
    norm_num at h3
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
    push_cast
    linarith
  have h90 : 0 < log 9 := log_pos (by norm_num)
  have := log_le_sub_one_of_pos ht
  push_cast
  nlinarith

/-- **A monotone function has a large degree-one coefficient** [O'Donnell][ODonnell2014],
Exercise 9.33: a nonconstant monotone Boolean function read as signs `F` has a coordinate `i`
with `F̂({i})² ≥ exp(-10 I[F] / Var[F])`. The book asks for some `S ≠ ∅` with
`F̂(S)² ≥ exp(-O(I[F] / Var[F]))`; this takes `S = {i}`, as the book's hint suggests. For monotone
`f` the influence of `i` is `F̂({i})` (Proposition 2.21), and the KKL Edge-Isoperimetric Theorem
`exists_nine_div_sq_mul_one_ninth_rpow_le_influence` bounds the largest influence below by
`(9 / Ĩ²) 9^{-Ĩ} ≥ exp(-5 Ĩ)`. -/
theorem exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hc : ∃ x y, f x ≠ f y) :
    ∃ i, exp (-(10 * totalInfluence (fun x => signVal (f x)) /
        𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2)) ≤
      fourierCoeff (fun x => signVal (f x)) {i} ^ 2 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set V := 𝔼 x, (F x - 𝔼 y, F y) ^ 2
  set I := totalInfluence F
  have hV : 0 < V := expect_sub_expect_sq_signVal_pos hc
  have hT : 0 < I / V := div_pos (hV.trans_le (expect_sub_expect_sq_le_totalInfluence F)) hV
  obtain ⟨i, hi⟩ := exists_nine_div_sq_mul_one_ninth_rpow_le_influence f hV
  refine ⟨i, ?_⟩
  have h : exp (-(10 * I / V)) = exp (-(5 * (I / V))) ^ 2 := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← influence_eq_fourierCoeff_singleton_of_monotone hf, h]
  exact pow_le_pow_left₀ (exp_pos _).le ((exp_neg_five_mul_le_nine_div_sq_mul hT).trans hi) 2

/-! ### The weight on the sets containing a coordinate -/

/-- The variance is the sum over the coordinates `i` of `∑_{S ∋ i} f̂(S) ^ 2 / |S|`: each
nonempty set shares its weight equally among its elements. -/
private theorem sum_sum_filter_mem_fourierCoeff_sq_div_card (f : (ι → Bool) → ℝ) :
    ∑ i, ∑ S with i ∈ S, fourierCoeff f S ^ 2 / #S = 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, sum_sum_filter_mem, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (card_ne_zero.2 (ne_empty_iff_nonempty.1 hS)))]
  · simp [not_not.1 hS]

/-- The weight `∑_{S ∋ i} f̂(S) ^ 2 / |S|` is at most the influence of `i`. -/
theorem sum_filter_mem_fourierCoeff_sq_div_card_le_influence (f : (ι → Bool) → ℝ) (i : ι) :
    ∑ S with i ∈ S, fourierCoeff f S ^ 2 / #S ≤ influence i f := by
  rw [influence_eq_sum_fourierCoeff_sq]
  refine sum_le_sum fun S hS => div_le_self (sq_nonneg _) ?_
  exact Nat.one_le_cast.2 (card_pos.2 ⟨i, (mem_filter.1 hS).2⟩)

/-- **The degree threshold**: for `A > 1`, every `m` satisfies `1 ≤ m log 3 / log A` or
`1 < A 3 ^ (-m)`, according as `3 ^ m ≥ A` or not. -/
theorem one_le_mul_log_three_div_log_or_one_lt_mul_one_third_pow {A : ℝ} (hA : 1 < A) (m : ℕ) :
    1 ≤ m * (log 3 / log A) ∨ 1 < A * (1 / 3) ^ m := by
  rcases le_or_gt A (3 ^ m) with h | h
  · left
    rw [mul_div_assoc', le_div_iff₀ (log_pos hA), one_mul, ← log_pow]
    exact log_le_log (by linarith) h
  · right
    rw [one_div, inv_pow, ← div_eq_mul_inv, one_lt_div (by positivity)]
    exact h

/-- For `A > 1` and `m ≥ 1`, `1 / m ≤ log 3 / log A + A 3 ^ (-m)`. -/
private theorem inv_le_log_div_log_add {A : ℝ} (hA : 1 < A) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ)⁻¹ ≤ log 3 / log A + A * (1 / 3) ^ m := by
  have h3 : 0 ≤ log 3 / log A := div_nonneg (log_pos (by norm_num)).le (log_pos hA).le
  have hpow : 0 ≤ A * (1 / 3 : ℝ) ^ m := mul_nonneg (by linarith) (by positivity)
  rcases one_le_mul_log_three_div_log_or_one_lt_mul_one_third_pow hA m with h | h
  · have : (m : ℝ)⁻¹ ≤ log 3 / log A := by
      rw [inv_le_iff_one_le_mul₀ (Nat.cast_pos.2 hm), mul_comm]
      exact h
    linarith
  · linarith [inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hm : (1 : ℝ) ≤ m)]

/-- **The weight on the sets containing a coordinate**: for a Boolean function read as signs and
every `A > 1`, `∑_{S ∋ i} F̂(S) ^ 2 / |S| ≤ log 3 / log A · Infᵢ[F] + A / 3 · Infᵢ[F] ^ (3/2)`. -/
private theorem sum_filter_mem_fourierCoeff_sq_div_card_le (f : (ι → Bool) → Bool) (i : ι) {A : ℝ}
    (hA : 1 < A) :
    ∑ S with i ∈ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 / #S ≤
      log 3 / log A * influence i (fun x => signVal (f x)) +
        A / 3 * (influence i (fun x => signVal (f x)) *
          √(influence i fun x => signVal (f x))) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have h := sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le f i
  calc ∑ S with i ∈ S, fourierCoeff F S ^ 2 / #S
      ≤ ∑ S with i ∈ S, (log 3 / log A * fourierCoeff F S ^ 2 +
          A * ((1 / 3) ^ #S * fourierCoeff F S ^ 2)) := by
        refine sum_le_sum fun S hS => ?_
        have hm : 1 ≤ #S := card_pos.2 ⟨i, (mem_filter.1 hS).2⟩
        have := mul_le_mul_of_nonneg_right (inv_le_log_div_log_add hA hm)
          (sq_nonneg (fourierCoeff F S))
        rw [div_eq_inv_mul]
        linarith
    _ = log 3 / log A * influence i F +
          A * ∑ S with i ∈ S, (1 / 3) ^ #S * fourierCoeff F S ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, influence_eq_sum_fourierCoeff_sq]
    _ ≤ log 3 / log A * influence i F + A / 3 * (influence i F * √(influence i F)) := by
        linarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ A)]

/-- `x ^ (1/4) log (1 / x) < 4` on `0 < x ≤ 1`, written with `√√x`. -/
private theorem sqrt_sqrt_mul_log_inv_lt {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1) :
    √√x * log x⁻¹ < 4 := by
  have hu : 0 < √√x := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  have hu1 : √√x ≤ 1 := Real.sqrt_le_one.2 (Real.sqrt_le_one.2 hx')
  have h := abs_log_mul_self_lt _ hu hu1
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (log_nonpos hu.le hu1) hu.le),
    Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le] at h
  rw [log_inv]
  linarith

/-- **The weight on the sets containing a coordinate of small influence**: if
`Infᵢ[F] ≤ δ`, then `∑_{S ∋ i} F̂(S) ^ 2 / |S| · log (1 / δ) ≤ 6 Infᵢ[F]`. For `δ < 1` this is
`∑_{S ∋ i} F̂(S) ^ 2 / |S| ≤ 6 Infᵢ[F] / log (1 / δ)`; for `δ ≥ 1` the left side is at most
zero. -/
private theorem sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le (f : (ι → Bool) → Bool) (i : ι)
    {δ : ℝ} (hδ : influence i (fun x => signVal (f x)) ≤ δ) :
    (∑ S with i ∈ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 / #S) * log δ⁻¹ ≤
      6 * influence i (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set a := influence i F
  set W := ∑ S with i ∈ S, fourierCoeff F S ^ 2 / #S
  have ha : 0 ≤ a := influence_nonneg i F
  have hW : 0 ≤ W := sum_nonneg fun S _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  rcases le_or_gt (log δ⁻¹) 0 with hL | hL
  · nlinarith
  -- now `0 < δ < 1`; take `A = δ ^ (-1/4) = (√√δ)⁻¹`
  obtain ⟨hδ0, hδ1⟩ := one_lt_inv_iff₀.1 ((log_pos_iff (inv_nonneg.2 (ha.trans hδ))).1 hL)
  set u := √√δ
  have hu : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 hδ0)
  have hu1 : u < 1 :=
    (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact (Real.sqrt_lt' one_pos).2 (by simpa))
  have hu2 : √δ = u ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg δ)).symm
  have hlogA : log u⁻¹ = log δ⁻¹ / 4 := by
    rw [log_inv, log_inv, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hδ0.le]
    ring
  have hmain := sum_filter_mem_fourierCoeff_sq_div_card_le f i (one_lt_inv_iff₀.2 ⟨hu, hu1⟩)
  have hAa : u⁻¹ / 3 * (a * √a) ≤ u / 3 * a := by
    have hsqrt : √a ≤ u ^ 2 := hu2 ▸ Real.sqrt_le_sqrt hδ
    have : u⁻¹ * √a ≤ u := by
      rw [inv_mul_le_iff₀ hu, ← sq]
      exact hsqrt
    nlinarith [Real.sqrt_nonneg a]
  have h4 := sqrt_sqrt_mul_log_inv_lt hδ0 hδ1.le
  have h3 : log 3 * a ≤ 1.1 * a := mul_le_mul_of_nonneg_right (by linarith [log_three_lt_d9]) ha
  have hua : u * log δ⁻¹ * a ≤ 4 * a := mul_le_mul_of_nonneg_right h4.le ha
  calc W * log δ⁻¹ ≤ (log 3 / log u⁻¹ * a + u / 3 * a) * log δ⁻¹ :=
        mul_le_mul_of_nonneg_right (hmain.trans (by linarith)) hL.le
    _ = 4 * (log 3 * a) + u * log δ⁻¹ * a / 3 := by
        have hL0 := hL.ne'
        have e : log 3 / (log δ⁻¹ / 4) * a * log δ⁻¹ = 4 * (log 3 * a) := by
          rw [div_div_eq_mul_div, mul_right_comm, div_mul_cancel₀ _ hL0]
          ring
        rw [hlogA, add_mul, e]
        ring
    _ ≤ 6 * a := by linarith

/-! ### Talagrand's inequality -/

/-- **Talagrand's inequality**: for a Boolean function read as signs `F` whose influences are all
less than one, `Var[F] ≤ 6 ∑ᵢ Infᵢ[F] / log (1 / Infᵢ[F])` [Talagrand1994]. A coordinate of
influence one contributes `+∞` in the usual reading of the inequality; for an unconditional form
see `expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`. -/
theorem expect_sub_expect_sq_le_six_mul_sum_influence_div_log (f : (ι → Bool) → Bool)
    (hf : ∀ i, influence i (fun x => signVal (f x)) < 1) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤
      6 * ∑ i, influence i (fun x => signVal (f x)) /
        log (influence i fun x => signVal (f x))⁻¹ := by
  rw [← sum_sum_filter_mem_fourierCoeff_sq_div_card, mul_sum]
  refine sum_le_sum fun i _ => ?_
  set a := influence i fun x => signVal (f x)
  have ha : 0 ≤ a := influence_nonneg i _
  have h := sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le f i le_rfl
  rcases ha.lt_or_eq with ha | ha
  · have hL : 0 < log a⁻¹ := log_pos (one_lt_inv_iff₀.2 ⟨ha, hf i⟩)
    rw [mul_div_assoc', le_div_iff₀ hL]
    exact h
  · rw [← ha, zero_div, mul_zero]
    exact ha ▸ sum_filter_mem_fourierCoeff_sq_div_card_le_influence _ i

/-- **Talagrand's inequality, unconditional form**: for every Boolean function read as signs `F`,
`Var[F] ≤ 7 ∑ᵢ Infᵢ[F] / (1 + log (1 / Infᵢ[F]))` [Talagrand1994]. -/
theorem expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤
      7 * ∑ i, influence i (fun x => signVal (f x)) /
        (1 + log (influence i fun x => signVal (f x))⁻¹) := by
  rw [← sum_sum_filter_mem_fourierCoeff_sq_div_card, mul_sum]
  refine sum_le_sum fun i _ => ?_
  set a := influence i fun x => signVal (f x)
  have ha : 0 ≤ a := influence_nonneg i _
  have hL : 0 ≤ log a⁻¹ := by
    rw [log_inv]
    exact neg_nonneg.2 (log_nonpos ha (influence_signVal_le_one f i))
  have hW := sum_filter_mem_fourierCoeff_sq_div_card_le_influence (fun x => signVal (f x)) i
  have hWL := sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le f i le_rfl
  rw [mul_div_assoc', le_div_iff₀ (by linarith)]
  linarith

end Cslib.BitString
