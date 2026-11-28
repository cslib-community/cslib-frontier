/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
public import CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Foundations.BooleanAnalysis.Concentration
import CslibFrontier.Foundations.BooleanAnalysis.Fibers
import CslibFrontier.Foundations.BooleanAnalysis.HammingFourier
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Friedgut's junta theorem

A Boolean function of small total influence is close to a function of few coordinates: if
`I[F] ≤ K` for a Boolean function `f` read as signs `F`, then for every `ε > 0`, `f` agrees with a
function of at most `4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates outside a fraction `ε` of the
inputs (`BitString.exists_dependsOn_hammingDist_div_le_of_totalInfluence_le`), so, for `ε ≤ 1`,
with a function of at most `3 · 2 ^ (8 K / ε)` coordinates
(`BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`) [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. A function of the coordinates in `J` is a `J`-junta,
written with Mathlib's `DependsOn`.

In the form of [O'Donnell, Theorem 9.28][ODonnell2014], where the book takes `K = I[F]`: at most
`K / τ` coordinates have influence at least `τ > 0`
(`BitString.card_filter_le_influence_le_div_of_totalInfluence_le`), which is `K³ 9ᵏ / ε²` for
`τ = ε² / (K² 9ᵏ)`; for any `J` containing the coordinates of influence more than `τ`, the
spectrum of `F` is `ε`-concentrated on `{S ⊆ J} ∪ {|S| > k}`
(`BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le`, from
`BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le` for every threshold `τ`); and
if it is also `ε`-concentrated on degree up to `k`, it is `2ε`-concentrated on
`{S ⊆ J : |S| ≤ k}` (`BitString.sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le`) and `f` is
`ε`-close to a `J`-junta
(`BitString.exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le`).

## Proof

Averaging out the coordinates outside a set `J` keeps the Fourier coefficients on the subsets of
`J` and kills the others (`BitString.fourierCoeff_expect_piecewise`), so `f` is within mean square
distance `∑_{S ⊄ J} F̂(S) ^ 2` of a function of the coordinates in `J`; rounding it to a sign on
each fiber of the coordinates in `J` costs at most half the variance on the fiber
(`BitString.two_mul_min_le_expect_sub_expect_sq_signVal`) [O'Donnell, Proposition 1.15]
[ODonnell2014], which gives a Boolean `J`-junta at relative Hamming distance at most half that
weight
(`BitString.exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq`)
[O'Donnell, Exercise 3.34][ODonnell2014]. If every coordinate outside `J` has influence at most
`τ`, the hypercontractive bound of the Kahn–Kalai–Linial theorem,
`∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 ≤ Infᵢ[F] ^ (3/2) / 3`, summed over the coordinates `i ∉ J`, bounds
the weight on the sets of size at most `k` that are not subsets of `J` by `3ᵏ / 3 · √τ · I[F]`
(Theorem 9.28). The sets of size more than `k` carry weight at most `I[F] / (k + 1)`, so for every
`A > 1` the weight outside the subsets of `J` is at most
`log 3 / log A · I[F] + A / 3 · √τ · I[F]` (`BitString.sum_filter_not_subset_fourierCoeff_sq_le`).
Taking `A = 9 ^ (K / ε)` and `√τ = 3 ε / (2 K A)` makes both terms at most `ε / 2`
(`BitString.exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le`), and `J` has
at most `K / τ` elements.

## Main results

* `Cslib.BitString.exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq`,
  `Cslib.BitString.exists_dependsOn_hammingDist_div_le_two_mul_expect_piecewise_ne`,
  `Cslib.BitString.exists_dependsOn_compl_hammingDist_div_le_two_mul_expect_piecewise_ne`: a Boolean
  function is close to a `J`-junta when its Fourier weight is concentrated on the subsets of `J`, or
  when resampling the coordinates outside `J` rarely changes its value.
* `Cslib.BitString.card_filter_le_influence_le_div_of_totalInfluence_le`,
  `Cslib.BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le`,
  `Cslib.BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le`,
  `Cslib.BitString.sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le`,
  `Cslib.BitString.exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le`:
  Theorem 9.28.
* `Cslib.BitString.sum_filter_not_subset_fourierCoeff_sq_le`: the Fourier weight outside the
  subsets of the set of influential coordinates.
* `Cslib.BitString.exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le`: a set of
  at most `4 K³/(9 ε²) · 81^(K/ε)` coordinates (`exp(O(K/ε))` for `ε ≤ 1`), outside whose subsets
  the Fourier weight is at most `ε`. The `## Usage` section of
  `CslibFrontier.Foundations.BooleanAnalysis.LargeCoefficient` shows how to use it.
* `Cslib.BitString.exists_dependsOn_hammingDist_div_le_of_totalInfluence_le`,
  `Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`: Friedgut's
  junta theorem.

## Usage

Open `Cslib.BitString`. Theorem 9.28 is stated for any bound `K ≥ I[f]` in place of the book's
`I[f]`. Write `F` for `fun x => signVal (f x)` and `hI : totalInfluence F ≤ K`. For `ht : 0 < t`,
`card_filter_le_influence_le_div_of_totalInfluence_le F ht hI` bounds the number of coordinates of
influence at least `t` by `K / t`; at the book's threshold `t = ε ^ 2 / (K ^ 2 * 9 ^ k)` this is
its `K³ 9ᵏ / ε²`. If every coordinate outside `J` has influence at most `t` (`hJ`),
`sum_filter_not_subset_and_card_le_fourierCoeff_sq_le f hJ k` bounds the Fourier weight on the
sets of size at most `k` that are not subsets of `J` by `3 ^ k / 3 * √t * totalInfluence F`. When
`hJ` uses the book's threshold and `hε : 0 ≤ ε`,
`sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le f hε hI k hJ` turns
this into `ε / 3`, so the spectrum is `ε`-concentrated on the subsets of `J` and the sets of size
more than `k`. If moreover the weight above degree `k` is at most `ε` (`hk`),
`sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le f hI k hJ hk` gives `2 ε`-concentration on
the subsets of `J` of size at most `k`, and
`exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le f hI k hJ hk` gives a
`J`-junta at relative Hamming distance at most `ε`.

That last step is the sharp form of Proposition 3.31 that the book takes from Exercise 3.34:
`exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J` gives a
`J`-junta, the sign of the average of `F` over the other coordinates, at relative distance at most
half the weight outside the subsets of `J`. The exercise rounds an `L¹` approximation at a random
threshold. The deterministic sign suffices here because the average over the other coordinates is
the conditional mean: on each fiber the sign misses the smaller of the two values, at most half the
variance on the fiber by Proposition 1.15 (`two_mul_min_le_expect_sub_expect_sq_signVal` in
`CslibFrontier.Foundations.BooleanAnalysis.Variance`). The checked examples in
[`CslibFrontierTests/BooleanAnalysisFriedgutConcentration.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisFriedgutConcentration.lean)
apply all of these to the dictator on two bits, where the count and the threshold weight bound are
attained.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach* (2007 draft)][AroraBarak07]
* [E. Friedgut, *Boolean functions with low average sensitivity depend on few
  coordinates*][Friedgut1998]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Juntas from spectral concentration -/

/-- **Spectral concentration gives a junta** [O'Donnell, Proposition 3.31 and Exercises 3.28 and
3.34][ODonnell2014]: a Boolean function is at relative Hamming distance at most
`(1/2) ∑_{S ⊄ J} F̂(S) ^ 2` from a Boolean function of the coordinates in `J`, the sign of its
average over the other coordinates. This is the conclusion of Exercise 3.34 for
`g(x) = 𝔼_z F(x_J, z) = F^{⊆J}(x)`, with deterministic rounding in place of the random threshold:
the weight outside the subsets of `J` is `‖F - g‖₂² = 𝔼_x Var_z F(x_J, z)`, which for this
conditional mean is also the `L¹` distance `‖F - g‖₁` of the exercise, and on each fiber of the
coordinates in `J` rounding `g` to a sign disagrees with `F` on the smaller of the fractions of
the two values, which is at most half the variance on the fiber [O'Donnell, Fact 1.14 and
Proposition 1.15][ODonnell2014]. -/
theorem exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq
    (f : (ι → Bool) → Bool) (J : Finset ι) :
    ∃ g : (ι → Bool) → Bool, DependsOn g (J : Set ι) ∧
      2 * ((hammingDist f g : ℝ) / 2 ^ Fintype.card ι) ≤
        ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  set h : (ι → Bool) → ℝ := fun x => 𝔼 z, signVal (f (J.piecewise x z))
  have hdep {x y : ι → Bool} (hxy : ∀ i ∈ J, x i = y i) : h x = h y :=
    expect_congr rfl fun z _ => by rw [J.piecewise_congr hxy fun _ _ => rfl]
  have hJ (x z : ι → Bool) : h (J.piecewise x z) = h x :=
    hdep fun i hi => J.piecewise_eq_of_mem _ _ hi
  -- on one fiber, rounding the mean of the signs to its sign costs at most half the variance
  have hfib (a : (ι → Bool) → Bool) :
      (𝔼 z, (signVal (a z) - signVal (decide (𝔼 w, signVal (a w) < 0))) ^ 2) / 2 ≤
        𝔼 z, (signVal (a z) - 𝔼 w, signVal (a w)) ^ 2 := by
    have h0 := expect_signVal a
    rw [mul_div_assoc] at h0
    have h1 := hammingDist_false_div_add_hammingDist_true_div a
    rw [expect_sq_signVal_sub_signVal a fun _ => _]
    refine le_trans ?_ (two_mul_min_le_expect_sub_expect_sq_signVal a)
    by_cases ht : 𝔼 w, signVal (a w) < 0
    · simp only [ht, decide_true]
      rw [min_eq_right (by linarith)]
      linarith
    · simp only [ht, decide_false]
      rw [min_eq_left (by linarith)]
      linarith
  -- resampling the coordinates outside `J` of a uniform point gives a uniform point
  have hres (φ : (ι → Bool) → ℝ) : 𝔼 x, 𝔼 z, φ (J.piecewise x z) = 𝔼 x, φ x := by
    rw [← expect_projectionAverage φ fun i => decide (i ∈ J)]
    refine expect_congr rfl fun x _ => ?_
    rw [projectionAverage_eq_expect_piecewise]
    refine expect_congr rfl fun z _ => congrArg φ (funext fun i => ?_)
    by_cases hi : i ∈ J <;> simp [hi]
  refine ⟨fun x => decide (h x < 0), fun x y hxy => ?_, ?_⟩
  · simp only [hdep fun i hi => hxy i (mem_coe.2 hi)]
  · have hd := expect_sq_signVal_sub_signVal f fun x => decide (h x < 0)
    rw [← expect_sub_expect_piecewise_sq,
      show (hammingDist f fun x => decide (h x < 0) : ℝ) / 2 ^ Fintype.card ι =
        (𝔼 x, (signVal (f x) - signVal (decide (h x < 0))) ^ 2) / 4 by rw [hd]; ring,
      ← hres fun x => (signVal (f x) - signVal (decide (h x < 0))) ^ 2,
      ← hres fun x => (signVal (f x) - h x) ^ 2]
    simp only [hJ]
    rw [show 2 * ((𝔼 x, 𝔼 z, (signVal (f (J.piecewise x z)) - signVal (decide (h x < 0))) ^ 2) /
        4) = 𝔼 x, (𝔼 z, (signVal (f (J.piecewise x z)) - signVal (decide (h x < 0))) ^ 2) / 2 by
      rw [← expect_div]; ring]
    exact expect_le_expect fun x _ => hfib fun z => f (J.piecewise x z)

/-- **Small variation outside `J` gives a `J`-junta**: a Boolean function is at relative Hamming
distance at most twice the probability that resampling the coordinates outside `J` changes its
value from a Boolean function of the coordinates in `J`
[O'Donnell, Proposition 3.31 and Exercise 3.28][ODonnell2014]
[Arora–Barak, Chapter 19, Exercise 4][AroraBarak07]. -/
theorem exists_dependsOn_hammingDist_div_le_two_mul_expect_piecewise_ne (f : (ι → Bool) → Bool)
    (J : Finset ι) :
    ∃ g : (ι → Bool) → Bool, DependsOn g (J : Set ι) ∧
      (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤
        2 * 𝔼 x, 𝔼 z, if f x = f (J.piecewise x z) then 0 else 1 := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J
  refine ⟨g, hg, ?_⟩
  have hW := expect_expect_piecewise_ne f J
  have h0 : (0 : ℝ) ≤ 𝔼 x, 𝔼 z, if f x = f (J.piecewise x z) then 0 else 1 :=
    expect_nonneg fun _ _ => expect_nonneg fun _ _ => by split_ifs <;> norm_num
  linarith

/-- **Small variation on `I` gives a junta outside `I`**: a Boolean function is at relative Hamming
distance at most twice the probability that resampling the coordinates in `I` changes its value
from a Boolean function of the coordinates outside `I`
[Arora–Barak, Chapter 19, Exercise 4][AroraBarak07]. -/
theorem exists_dependsOn_compl_hammingDist_div_le_two_mul_expect_piecewise_ne
    (f : (ι → Bool) → Bool) (I : Finset ι) :
    ∃ g : (ι → Bool) → Bool, DependsOn g ((Iᶜ : Finset ι) : Set ι) ∧
      (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤
        2 * 𝔼 x, 𝔼 z, if f x = f (I.piecewise z x) then 0 else 1 := by
  simpa only [piecewise_compl] using
    exists_dependsOn_hammingDist_div_le_two_mul_expect_piecewise_ne f Iᶜ

/-! ### The weight outside the influential coordinates -/

/-- **Few coordinates are influential** [O'Donnell, Theorem 9.28][ODonnell2014]: if `I[F] ≤ K`,
then at most `K / τ` coordinates have influence at least `τ > 0`. For the theorem's
`τ = ε² / (K² 9ᵏ)` this is its bound `K³ 9ᵏ / ε²` on the influential coordinates. -/
theorem card_filter_le_influence_le_div_of_totalInfluence_le (F : (ι → Bool) → ℝ) {K τ : ℝ}
    (hτ : 0 < τ) (hI : totalInfluence F ≤ K) :
    (#{i | τ ≤ influence i F} : ℝ) ≤ K / τ :=
  (le_div_iff₀ hτ).2 <|
    (card_filter_mul_le_sum univ _ _ (fun i _ => influence_nonneg i F) fun _ _ h => h).trans hI

/-- If every coordinate outside `J` has influence at most `τ` on `F = signVal ∘ f`, then the
`1/3`-damped Fourier weight of sets meeting `Jᶜ`, counted with multiplicity `#(S \ J)`, is at
most `√τ / 3 * totalInfluence F`. -/
private theorem sum_card_sdiff_mul_one_third_pow_fourierCoeff_sq_le
    (f : (ι → Bool) → Bool) {J : Finset ι} {τ : ℝ}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ τ) :
    ∑ S : Finset ι, (#(S \ J) : ℝ) *
      ((1 / 3) ^ #S * fourierCoeff (fun x => signVal (f x)) S ^ 2) ≤
      √τ / 3 * totalInfluence (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set g : Finset ι → ℝ := fun S => (1 / 3) ^ #S * fourierCoeff F S ^ 2
  -- the sets meeting the complement of `J`, counted with multiplicity
  have hswap : ∑ S, (#(S \ J) : ℝ) * g S = ∑ i with i ∉ J, ∑ S with i ∈ S, g S := by
    have h := sum_comm' (s := univ) (t := fun S => S \ J) (t' := univ.filter (· ∉ J))
      (s' := fun i => univ.filter (i ∈ ·)) (f := fun S _ => g S) (fun S i => by simp [and_comm])
    rw [← h]
    exact sum_congr rfl fun S _ => by rw [sum_const, nsmul_eq_mul]
  rw [hswap]
  calc ∑ i with i ∉ J, ∑ S with i ∈ S, g S
      ≤ ∑ i with i ∉ J, influence i F * √τ / 3 := by
        refine sum_le_sum fun i hi => ?_
        refine (sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le f i).trans ?_
        have := Real.sqrt_le_sqrt (hJ i (mem_filter.1 hi).2)
        have := influence_nonneg i F
        gcongr
    _ ≤ ∑ i, influence i F * √τ / 3 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ =>
          div_nonneg (mul_nonneg (influence_nonneg i F) (Real.sqrt_nonneg τ)) (by norm_num)
    _ = √τ / 3 * totalInfluence F := by
        rw [totalInfluence, mul_sum]
        exact sum_congr rfl fun i _ => by ring

/-- **Concentration on the influential coordinates and high degree** [O'Donnell, Theorem 9.28]
[ODonnell2014]: if every coordinate outside `J` has influence at most `τ` on a Boolean function
read as signs `F`, then for every `k` the Fourier weight on the sets of size at most `k` that are
not subsets of `J` is at most `3ᵏ / 3 · √τ · I[F]`. For the theorem's `τ = ε² / (I[F]² 9ᵏ)` the
bound is `ε / 3`, so the spectrum of `F` is `ε`-concentrated on `{S ⊆ J} ∪ {|S| > k}`. The proof is
the book's: such a set `S` has `F̂(S)² ≤ 3^{k - 1} |S \ J| 3^{1 - |S|} F̂(S)²`, and the sum over `S`
of the right side is `3^{k - 1} ∑_{i ∉ J} Infᵢ^{(1/3)}[F] ≤ 3^{k - 1} √τ I[F]` by the
hypercontractive bound of the Kahn–Kalai–Linial theorem. -/
theorem sum_filter_not_subset_and_card_le_fourierCoeff_sq_le (f : (ι → Bool) → Bool)
    {J : Finset ι} {τ : ℝ} (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ τ) (k : ℕ) :
    ∑ S with ¬S ⊆ J ∧ #S ≤ k, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      3 ^ k / 3 * √τ * totalInfluence (fun x => signVal (f x)) := by
  set c : Finset ι → ℝ := fun S => fourierCoeff (fun x => signVal (f x)) S ^ 2
  have hterm (S : Finset ι) (hS : S ∈ ({S | ¬S ⊆ J ∧ #S ≤ k} : Finset (Finset ι))) :
      c S ≤ 3 ^ k * ((#(S \ J) : ℝ) * ((1 / 3) ^ #S * c S)) := by
    obtain ⟨hSJ, hSk⟩ := (mem_filter.1 hS).2
    have h1 : (1 : ℝ) ≤ #(S \ J) := by
      exact_mod_cast card_pos.2 (sdiff_nonempty.2 hSJ)
    have h2 : (1 : ℝ) ≤ 3 ^ k * (1 / 3) ^ #S := by
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ (by norm_num) hSk
    have hc : 0 ≤ c S := sq_nonneg _
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  calc ∑ S with ¬S ⊆ J ∧ #S ≤ k, c S
      ≤ ∑ S with ¬S ⊆ J ∧ #S ≤ k, 3 ^ k * ((#(S \ J) : ℝ) * ((1 / 3) ^ #S * c S)) :=
        sum_le_sum hterm
    _ ≤ ∑ S, 3 ^ k * ((#(S \ J) : ℝ) * ((1 / 3) ^ #S * c S)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ => by positivity
    _ ≤ 3 ^ k * (√τ / 3 * totalInfluence fun x => signVal (f x)) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left
          (sum_card_sdiff_mul_one_third_pow_fourierCoeff_sq_le f hJ) (by positivity)
    _ = 3 ^ k / 3 * √τ * totalInfluence fun x => signVal (f x) := by ring

/-- **Concentration on the influential coordinates and high degree, with the book's threshold**
[O'Donnell, Theorem 9.28][ODonnell2014]: if a Boolean function read as signs `F` has `I[F] ≤ K`,
`ε ≥ 0` and every coordinate outside `J` has influence at most `τ = ε² / (K² 9ᵏ)`, then the
Fourier weight outside `{S ⊆ J} ∪ {|S| > k}` is at most `ε / 3`. The book takes `K = I[F]` and `J`
the set of coordinates of influence at least `τ`, and states the bound `ε`. -/
theorem sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le
    (f : (ι → Bool) → Bool) {K ε : ℝ} (hε : 0 ≤ ε)
    (hI : totalInfluence (fun x => signVal (f x)) ≤ K) (k : ℕ) {J : Finset ι}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ ε ^ 2 / (K ^ 2 * 9 ^ k)) :
    ∑ S with ¬S ⊆ J ∧ #S ≤ k, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 3 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hK0 : 0 ≤ K := (totalInfluence_nonneg F).trans hI
  have hsqrt : √(ε ^ 2 / (K ^ 2 * 9 ^ k)) = ε / (K * 3 ^ k) := by
    rw [show ε ^ 2 / (K ^ 2 * 9 ^ k) = (ε / (K * 3 ^ k)) ^ 2 by
      rw [div_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      norm_num]
    exact sqrt_sq (by positivity)
  refine (sum_filter_not_subset_and_card_le_fourierCoeff_sq_le f hJ k).trans ?_
  rw [hsqrt]
  rcases hK0.eq_or_lt with rfl | hK
  · simpa using div_nonneg hε zero_le_three
  · rw [show 3 ^ k / 3 * (ε / (K * 3 ^ k)) * totalInfluence F =
        ε / 3 * (totalInfluence F / K) by field_simp]
    have := (div_le_one hK).2 hI
    nlinarith

/-- The sets outside `{S ⊆ J : |S| ≤ k}` are those of size at most `k` that are not subsets of `J`
and those of size more than `k`. -/
private theorem sum_filter_not_subset_or_lt_card (c : Finset ι → ℝ) (J : Finset ι) (k : ℕ) :
    ∑ S with ¬S ⊆ J ∨ k < #S, c S = ∑ S with ¬S ⊆ J ∧ #S ≤ k, c S + ∑ S with k < #S, c S := by
  rw [← sum_filter_add_sum_filter_not _ (fun S => #S ≤ k), filter_filter, filter_filter]
  congr 1 <;> refine sum_congr (filter_congr fun S _ => ?_) fun _ _ => rfl
  · constructor
    · rintro ⟨h | h, hk⟩
      · exact ⟨h, hk⟩
      · omega
    · rintro ⟨h, hk⟩
      exact ⟨Or.inl h, hk⟩
  · constructor
    · rintro ⟨-, hk⟩
      omega
    · intro hk
      exact ⟨Or.inr hk, by omega⟩

/-- The weight outside the subsets of `J` is at most the weight outside `{S ⊆ J : |S| ≤ k}`. -/
private theorem sum_filter_not_subset_le_sum_filter_not_subset_or_lt_card {c : Finset ι → ℝ}
    (hc : ∀ S, 0 ≤ c S) (J : Finset ι) (k : ℕ) :
    ∑ S with ¬S ⊆ J, c S ≤ ∑ S with ¬S ⊆ J ∨ k < #S, c S :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun _ _ h => Or.inl h)
    fun S _ _ => hc S

/-- **The Fourier weight outside the influential coordinates**: if every coordinate outside `J`
has influence at most `τ` on a Boolean function read as signs `F`, then for every `A > 1`,
`∑_{S ⊄ J} F̂(S) ^ 2 ≤ log 3 / log A · I[F] + A / 3 · √τ · I[F]`, adapting the proof of
[O'Donnell, Theorem 9.28][ODonnell2014]: with `3ᵏ ≤ A < 3ᵏ⁺¹`, the sets of size at most `k`
carry at most `A / 3 · √τ · I[F]` of this weight
(`BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le`), and the larger ones at most
`I[F] / (k + 1) ≤ log 3 / log A · I[F]`. -/
theorem sum_filter_not_subset_fourierCoeff_sq_le (f : (ι → Bool) → Bool) {J : Finset ι} {τ : ℝ}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ τ) {A : ℝ} (hA : 1 < A) :
    ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      log 3 / log A * totalInfluence (fun x => signVal (f x)) +
        A / 3 * √τ * totalInfluence (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set c : Finset ι → ℝ := fun S => fourierCoeff F S ^ 2
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  have hlogA : 0 < log A := log_pos hA
  -- the degree `k` with `3 ^ k ≤ A < 3 ^ (k + 1)`
  set k := ⌊log A / log 3⌋₊
  have hk : (3 : ℝ) ^ k ≤ A := by
    have h := Nat.floor_le (div_nonneg hlogA.le hlog3.le)
    rw [le_div_iff₀ hlog3] at h
    rw [← log_le_log_iff (by positivity) (by linarith), log_pow]
    exact h
  have hk1 : 1 ≤ (k + 1) * (log 3 / log A) := by
    have h := Nat.lt_floor_add_one (log A / log 3)
    rw [div_lt_iff₀ hlog3] at h
    rw [mul_div_assoc', le_div_iff₀ hlogA, one_mul]
    exact h.le
  have hlow := sum_filter_not_subset_and_card_le_fourierCoeff_sq_le f hJ k
  have hhigh := add_one_mul_sum_fourierCoeff_sq_le_totalInfluence F k
  have hsub : ∑ S with ¬S ⊆ J, c S ≤ ∑ S with ¬S ⊆ J ∨ k < #S, c S :=
    sum_filter_not_subset_le_sum_filter_not_subset_or_lt_card (fun _ => sq_nonneg _) J k
  rw [sum_filter_not_subset_or_lt_card] at hsub
  have hW : 0 ≤ ∑ S with k < #S, c S := sum_nonneg fun _ _ => sq_nonneg _
  have hI : 0 ≤ totalInfluence F := totalInfluence_nonneg F
  have hL : 0 ≤ log 3 / log A := div_nonneg hlog3.le hlogA.le
  have hA3 : 3 ^ k / 3 * √τ * totalInfluence F ≤ A / 3 * √τ * totalInfluence F := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left hk1 hW, mul_le_mul_of_nonneg_left hhigh hL]

/-! ### Concentration on the influential coordinates of low degree -/

/-- **Concentration on the influential coordinates of low degree** [O'Donnell, Theorem 9.28]
[ODonnell2014]: if a Boolean function read as signs `F` has `I[F] ≤ K` and its Fourier spectrum is
`ε`-concentrated on degree up to `k`, then, for any `J` containing every coordinate of influence
more than `τ = ε² / (K² 9ᵏ)`, the spectrum is `2ε`-concentrated on `{S ⊆ J : |S| ≤ k}`. The book
takes `K = I[F]` and `J` the set of coordinates of influence at least `τ`. -/
theorem sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le (f : (ι → Bool) → Bool) {K ε : ℝ}
    (hI : totalInfluence (fun x => signVal (f x)) ≤ K) (k : ℕ) {J : Finset ι}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ ε ^ 2 / (K ^ 2 * 9 ^ k))
    (hk : ∑ S with k < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε) :
    ∑ S with ¬S ⊆ J ∨ k < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ 2 * ε := by
  have hε : 0 ≤ ε := (sum_nonneg fun _ _ => sq_nonneg _).trans hk
  rw [sum_filter_not_subset_or_lt_card]
  linarith [sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le f hε hI k hJ]

/-- **A junta from low-degree concentration** [O'Donnell, Theorem 9.28][ODonnell2014]: if a
Boolean function read as signs `F` has `I[F] ≤ K` and its Fourier spectrum is `ε`-concentrated on
degree up to `k`, then `f` is at relative Hamming distance at most `ε` from a Boolean function of
the coordinates of any `J` containing every coordinate of influence more than
`τ = ε² / (K² 9ᵏ)`. -/
theorem exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le
    (f : (ι → Bool) → Bool) {K ε : ℝ} (hI : totalInfluence (fun x => signVal (f x)) ≤ K) (k : ℕ)
    {J : Finset ι}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ ε ^ 2 / (K ^ 2 * 9 ^ k))
    (hk : ∑ S with k < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε) :
    ∃ g : (ι → Bool) → Bool, DependsOn g (J : Set ι) ∧
      (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  have h2 := sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le f hI k hJ hk
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J
  refine ⟨g, hg, ?_⟩
  have hsub : ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      ∑ S with ¬S ⊆ J ∨ k < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 :=
    sum_filter_not_subset_le_sum_filter_not_subset_or_lt_card (fun _ => sq_nonneg _) J k
  linarith

/-! ### Friedgut's junta theorem -/

/-- **Few coordinates carry the Fourier weight**: if a Boolean function read as signs
`F` has total influence at most `K`, then for every `ε > 0` there is a set `J` of at most
`4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates with `∑_{S ⊄ J} F̂(S) ^ 2 ≤ ε`, adapting the
proof of [O'Donnell, Theorem 9.28][ODonnell2014]. Together with the bound on the weight above
degree `K / ε` (`BitString.sum_fourierCoeff_sq_le_of_totalInfluence_le`) this is the spectral form
of Friedgut's junta theorem [O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le
    (f : (ι → Bool) → Bool) {K ε : ℝ} (hε : 0 < ε)
    (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ J : Finset ι, (#J : ℝ) ≤ 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε) ∧
      ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  rcases ((totalInfluence_nonneg F).trans hK).lt_or_eq with hK0 | hK0
  swap
  · -- with no influence at all, `J = ∅` works
    refine ⟨∅, by rw [← hK0]; simp, ?_⟩
    have h := sum_filter_not_subset_fourierCoeff_sq_le f (J := ∅) (τ := 1)
      (fun i _ => influence_signVal_le_one f i) (A := 3) (by norm_num)
    have hI0 : totalInfluence F = 0 := le_antisymm (hK0 ▸ hK) (totalInfluence_nonneg _)
    rw [hI0, mul_zero, mul_zero, add_zero] at h
    exact h.trans hε.le
  -- the parameters `A = 9 ^ (K / ε)` and `√τ = 3 ε / (2 K A)`
  set A : ℝ := 9 ^ (K / ε)
  have hA : 1 < A := one_lt_rpow (by norm_num) (div_pos hK0 hε)
  have hA0 : 0 < A := by linarith
  have hlogA : log 3 / log A = ε / (2 * K) := by
    rw [log_rpow (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
    have := (log_pos (by norm_num : (1 : ℝ) < 3)).ne'
    field_simp
    push_cast
    ring
  set s : ℝ := 3 * ε / (2 * K * A)
  have hs : 0 < s := by positivity
  set τ : ℝ := s ^ 2
  set J : Finset ι := {i | τ ≤ influence i F}
  -- `J` has at most `K / τ = 4 K ^ 3 / (9 ε ^ 2) · A ^ 2` elements
  have hA2 : A * A = 81 ^ (K / ε) := by
    rw [← mul_rpow (by norm_num) (by norm_num)]
    norm_num
  refine ⟨J, (card_filter_le_influence_le_div_of_totalInfluence_le F (by positivity) hK).trans_eq
    (by rw [← hA2, show τ = (3 * ε / (2 * K * A)) ^ 2 from rfl]; field_simp; ring), ?_⟩
  -- both terms of the weight bound are at most `ε / 2`
  have h := sum_filter_not_subset_fourierCoeff_sq_le f (J := J) (τ := τ)
    (fun i hi => (not_le.1 fun h => hi (mem_filter.2 ⟨mem_univ i, h⟩)).le) hA
  rw [hlogA, Real.sqrt_sq hs.le] at h
  refine h.trans ?_
  have e : A / 3 * s = ε / (2 * K) := by
    rw [show s = 3 * ε / (2 * K * A) from rfl]
    field_simp
  rw [e]
  have h1 : ε / (2 * K) * totalInfluence F ≤ ε / (2 * K) * K := by gcongr
  have h2 : ε / (2 * K) * K = ε / 2 := by
    field_simp
  linarith

/-- **Friedgut's junta theorem**: if a Boolean function read as signs `F` has total influence at
most `K`, then for every `ε > 0` it is at relative Hamming distance at most `ε` from a Boolean
function of at most `4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_dependsOn_hammingDist_div_le_of_totalInfluence_le (f : (ι → Bool) → Bool)
    {K ε : ℝ} (hε : 0 < ε) (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε) ∧ DependsOn g (J : Set ι) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨J, hJ, hw⟩ := exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le f hε hK
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J
  have : (0 : ℝ) ≤ (hammingDist f g : ℝ) / 2 ^ Fintype.card ι := by positivity
  exact ⟨J, g, hJ, hg, by linarith⟩

/-- **Friedgut's junta theorem, exponential form**: if a Boolean function read as signs `F` has
total influence at most `K`, then for every `0 < ε ≤ 1` it is at relative Hamming distance at most
`ε` from a Boolean function of at most `3 · 2 ^ (8 K / ε)` coordinates [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le (f : (ι → Bool) → Bool)
    {K ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 3 * 2 ^ (8 * K / ε) ∧ DependsOn g (J : Set ι) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨J, g, hJ, hg, hfg⟩ := exists_dependsOn_hammingDist_div_le_of_totalInfluence_le f hε hK
  refine ⟨J, g, hJ.trans ?_, hg, hfg⟩
  have hK0 : 0 ≤ K := (totalInfluence_nonneg _).trans hK
  set x := K / ε
  have hx : 0 ≤ x := div_nonneg hK0 hε.le
  -- `K ^ 3 / ε ^ 2 = x ^ 3 ε ≤ x ^ 3 ≤ 6 eˣ`
  have h1 : K ^ 3 / ε ^ 2 ≤ 6 * exp x := by
    have e : K ^ 3 / ε ^ 2 = x ^ 3 * ε := by
      rw [show x = K / ε from rfl]
      field_simp
    have h := Real.pow_div_factorial_le_exp x hx 3
    rw [show ((3 : ℕ).factorial : ℝ) = 6 by norm_num [Nat.factorial]] at h
    rw [e]
    nlinarith [mul_le_of_le_one_right (pow_nonneg hx 3) hε1]
  -- `eˣ 81 ^ x = (81 e) ^ x ≤ 256 ^ x = 2 ^ (8 x)`
  have h2 : exp x * 81 ^ x ≤ 2 ^ (8 * K / ε) := by
    rw [← exp_one_rpow, ← mul_rpow (exp_pos 1).le (by norm_num), mul_div_assoc,
      rpow_mul (by norm_num)]
    exact rpow_le_rpow (by positivity) (by norm_num; linarith [exp_one_lt_d9]) hx
  have h81 : (0 : ℝ) ≤ 81 ^ x := by positivity
  calc 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ x = 4 / 9 * (K ^ 3 / ε ^ 2) * 81 ^ x := by ring
    _ ≤ 4 / 9 * (6 * exp x) * 81 ^ x := by gcongr
    _ = 8 / 3 * (exp x * 81 ^ x) := by ring
    _ ≤ 3 * 2 ^ (8 * K / ε) := by nlinarith [exp_pos x]

end Cslib.BitString
