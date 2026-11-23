/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.BucketWeight
public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
import CslibFrontier.Probability.Fooling
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.SmallBias.Powering
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Deterministic estimation of Fourier coefficients and bucket weights

A *sample space* `g : σ → ι → Bool` lists the points `g s` of the cube, one for each seed `s` of a
finite type `σ`; it is `δ`-biased when the image of the uniform distribution on the seeds is
(`IsSmallBias δ ((PMF.uniformOfFintype σ).map g)`). Averaging `f (g s) χ_U(g s)` over the seeds
estimates the Fourier coefficient `f̂(U)` (`BitString.sampleSpaceCoeff`). The estimate reads `f`
only at the points of the sample space (`BitString.sampleSpaceCoeff_congr`,
`BitString.sampleSpacePoints`), one query per seed (`BitString.length_sampleSpacePoints`), so it is
deterministic. Since `‖(f χ_U)^‖₁ = ‖f̂‖₁`, Lemma 6.38 for `f χ_U` makes it accurate to within
`‖f̂‖₁ δ` (`BitString.abs_sampleSpaceCoeff_sub_fourierCoeff_le`)
[O'Donnell, Proposition 6.40][ODonnell2014].

The bucket weight `W^{S | J̄}[f] = 𝔼_z f_{J|z}^(S)²` (`BitString.bucketWeight`, where `f_{J|z}`
fixes the coordinates outside `J` to `z`) is estimated by drawing `z` from a second sample space
`h`, estimating each coefficient `f_{J|z}^(S)` from `g`, and averaging the squares
(`BitString.sampleSpaceBucketWeight`). It reads `f` only at the points `(g s, h t)`, which take the
coordinates in `J` from `g s` and the others from `h t` (`BitString.sampleSpaceBucketWeight_congr`,
`BitString.sampleSpaceBucketPoints`). For `|f| ≤ 1` it is within `2 ‖f̂‖₁ δ₁ + ‖f̂‖₁² δ₂` of the
bucket weight when `g` is `δ₁`-biased and `h` is `δ₂`-biased
(`BitString.abs_sampleSpaceBucketWeight_sub_bucketWeight_le`)
[O'Donnell, Proposition 6.41][ODonnell2014]: restrictions and the function `z ↦ f_{J|z}^(S)` have
spectral norm at most `‖f̂‖₁` (Exercise 3.7(a), and a consequence of Proposition 3.21, in
`SpectralNorm`), so Proposition 6.40 estimates each coefficient and Corollary 6.39 fools its
square.

Some sample space, obtained from the powering construction of Alon, Goldreich, Håstad and Peralta
(`BitString.exists_isSmallBias_uniformOfFintype_map`), bounds the query counts: for `n` coordinates,
spectral norm at most `s` and error `ε`, a seed of `2 m` bits with `4 ^ m ≤ 4 (n s / ε + 1) ²`
suffices for the coefficients (`BitString.exists_abs_sampleSpaceCoeff_sub_fourierCoeff_le`), and the
bucket weights of functions with `|f| ≤ 1` are read from `(4 ^ m) ²` points with
`4 ^ m ≤ 4 (n (2 s + s²) / ε + 1) ²`
(`BitString.exists_abs_sampleSpaceBucketWeight_sub_bucketWeight_le`). These theorems only assert
that such a sample space exists. They are the query bounds behind the polynomial running times of
Propositions 6.40 and 6.41; the running time itself is not certified by a machine model.

## Main definitions

* `Cslib.BitString.sampleSpacePoints`, `Cslib.BitString.sampleSpaceCoeff`: the points of a sample
  space and the estimate of a Fourier coefficient from them.
* `Cslib.BitString.sampleSpaceBucketPoints`, `Cslib.BitString.sampleSpaceBucketWeight`: the queried
  points and the estimate of a bucket weight.

## Main results

* `Cslib.BitString.abs_sampleSpaceCoeff_sub_fourierCoeff_le`,
  `Cslib.BitString.exists_abs_sampleSpaceCoeff_sub_fourierCoeff_le`: Proposition 6.40.
* `Cslib.BitString.abs_sampleSpaceBucketWeight_sub_bucketWeight_le`,
  `Cslib.BitString.exists_abs_sampleSpaceBucketWeight_sub_bucketWeight_le`: Proposition 6.41.

## Usage

Open `Cslib.BitString`. A sample space is any map `g : σ → ι → Bool` from a finite seed type, and
it is `δ`-biased when `IsSmallBias δ ((PMF.uniformOfFintype σ).map g)` holds; functions are real,
`f : (ι → Bool) → ℝ`. Unfold the estimates with `sampleSpaceCoeff_def` and
`sampleSpaceBucketWeight_def`. As for Kushilevitz–Mansour
(`CslibFrontier.MachineLearning.UniformLearning.KushilevitzMansour`), each estimate comes with an
explicit list of points, its length, and a `_congr` theorem saying that the output depends only on
the values of `f` at those points. Both estimators use the same seeds for every `U`, `J` and `S`.
The bucket weight is `bucketWeight f J S` from
`CslibFrontier.Foundations.BooleanAnalysis.BucketWeight`; the restriction keeps the coordinates in
`J` free. Proposition 6.41 is stated for every `f` with `|f x| ≤ 1`, not only for `±1`-valued `f`.
The existence theorems take a sample space from the powering construction, itself an existence
theorem; their bound on
`Fintype.card (BitString (2 * m))` makes the coefficient estimate read `O(n² s² / ε²)` points. The
book's statements are about running time: here only the queried points and their number are
certified, and no machine model is involved. The checked clients in
[CslibFrontierTests/BooleanAnalysisDeterministicEstimation.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisDeterministicEstimation.lean)
show that the whole cube, listed once, gives exact estimates and that a single seed gives values
at a point. On a thousand bits, a sample space from the existence theorems estimates a character's
coefficient within `1/10`, and its estimate of the bucket containing the character is at least
`9/10`. [O'Donnell, Theorems 6.42 and 6.43][ODonnell2014], the deterministic learners, are not
formalized: the Kushilevitz–Mansour error analysis `uniformError_kmHypothesis_le` is stated for
sampled estimates (`KMAccurate`) and would first have to be generalized to arbitrary estimates.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost k-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
-/

public section

namespace Cslib.BitString

open Finset Probability
open scoped BigOperators

variable {ι σ τ : Type*} [Fintype σ] [Fintype τ]

/-! ### The coefficient estimate -/

/-- The points of a sample space `g`, listed once for each seed. -/
noncomputable def sampleSpacePoints (g : σ → ι → Bool) : List (ι → Bool) :=
  (univ : Finset σ).toList.map g

/-- A sample space lists one point for each seed. -/
theorem length_sampleSpacePoints (g : σ → ι → Bool) :
    (sampleSpacePoints g).length = Fintype.card σ := by
  simp [sampleSpacePoints]

/-- Every point `g s` of a sample space is listed. -/
theorem mem_sampleSpacePoints (g : σ → ι → Bool) (s : σ) : g s ∈ sampleSpacePoints g :=
  List.mem_map.2 ⟨s, mem_toList.2 (mem_univ s), rfl⟩

/-- The estimate of the Fourier coefficient `f̂(U)` from the sample space `g`: the average over the
seeds `s` of `f (g s) χ_U(g s)`. -/
noncomputable def sampleSpaceCoeff (g : σ → ι → Bool) (f : (ι → Bool) → ℝ) (U : Finset ι) : ℝ :=
  𝔼 s, f (g s) * chi ℝ U (g s)

/-- The estimate of a Fourier coefficient, unfolded. -/
theorem sampleSpaceCoeff_def (g : σ → ι → Bool) (f : (ι → Bool) → ℝ) (U : Finset ι) :
    sampleSpaceCoeff g f U = 𝔼 s, f (g s) * chi ℝ U (g s) := by
  rw [sampleSpaceCoeff]

/-- **The coefficient estimate is deterministic**: it depends only on the values of `f` at the
points of the sample space. -/
theorem sampleSpaceCoeff_congr (g : σ → ι → Bool) {f f' : (ι → Bool) → ℝ}
    (h : ∀ x ∈ sampleSpacePoints g, f x = f' x) (U : Finset ι) :
    sampleSpaceCoeff g f U = sampleSpaceCoeff g f' U := by
  rw [sampleSpaceCoeff, sampleSpaceCoeff]
  exact expect_congr rfl fun s _ => by rw [h _ (mem_sampleSpacePoints g s)]

/-- A function bounded by one has coefficient estimates bounded by one. -/
theorem abs_sampleSpaceCoeff_le_one (g : σ → ι → Bool) {f : (ι → Bool) → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (U : Finset ι) : |sampleSpaceCoeff g f U| ≤ 1 := by
  rw [sampleSpaceCoeff]
  refine (abs_expect_le _ _).trans ?_
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp [Finset.univ_eq_empty]
  refine expect_le univ_nonempty fun s _ => ?_
  rw [abs_mul, abs_chi, mul_one]
  exact hf _

/-! ### The bucket-weight estimate -/

variable [DecidableEq ι]

/-- The points queried by the bucket-weight estimate: for each point `h t` of the second sample
space and each point `g s` of the first, the point taking the coordinates in `J` from `g s` and the
others from `h t`. -/
noncomputable def sampleSpaceBucketPoints (g : σ → ι → Bool) (h : τ → ι → Bool) (J : Finset ι) :
    List (ι → Bool) :=
  (univ : Finset τ).toList.flatMap fun t => (sampleSpacePoints g).map fun x => J.piecewise x (h t)

/-- The bucket-weight estimate queries `|τ| |σ|` points. -/
theorem length_sampleSpaceBucketPoints (g : σ → ι → Bool) (h : τ → ι → Bool) (J : Finset ι) :
    (sampleSpaceBucketPoints g h J).length = Fintype.card τ * Fintype.card σ := by
  simp [sampleSpaceBucketPoints, length_sampleSpacePoints, List.length_flatMap, length_toList]

/-- The estimate of the bucket weight `W^{S | J̄}[f]` (`bucketWeight f J S`) from the sample spaces
`g` and `h`: the average over the seeds `t` of `h` of the squared estimate, from `g`, of the
coefficient on `S` of the restriction fixing the coordinates outside `J` to `h t`. -/
noncomputable def sampleSpaceBucketWeight (g : σ → ι → Bool) (h : τ → ι → Bool) (f : (ι → Bool) → ℝ)
    (J S : Finset ι) : ℝ :=
  𝔼 t, sampleSpaceCoeff g (fun x => f (J.piecewise x (h t))) S ^ 2

/-- The estimate of a bucket weight, unfolded. -/
theorem sampleSpaceBucketWeight_def (g : σ → ι → Bool) (h : τ → ι → Bool) (f : (ι → Bool) → ℝ)
    (J S : Finset ι) :
    sampleSpaceBucketWeight g h f J S =
      𝔼 t, sampleSpaceCoeff g (fun x => f (J.piecewise x (h t))) S ^ 2 := by
  rw [sampleSpaceBucketWeight]

/-- **The bucket-weight estimate is deterministic**: it depends only on the values of `f` at the
points of `sampleSpaceBucketPoints g h J`. -/
theorem sampleSpaceBucketWeight_congr (g : σ → ι → Bool) (h : τ → ι → Bool) {f f' : (ι → Bool) → ℝ}
    {J : Finset ι} (hf : ∀ x ∈ sampleSpaceBucketPoints g h J, f x = f' x) (S : Finset ι) :
    sampleSpaceBucketWeight g h f J S = sampleSpaceBucketWeight g h f' J S := by
  rw [sampleSpaceBucketWeight, sampleSpaceBucketWeight]
  refine expect_congr rfl fun t _ => ?_
  rw [sampleSpaceCoeff_congr g (f' := fun x => f' (J.piecewise x (h t))) fun x hx => hf _ ?_]
  exact List.mem_flatMap.2 ⟨t, mem_toList.2 (mem_univ t), List.mem_map.2 ⟨x, hx, rfl⟩⟩

/-! ### Accuracy -/

variable [Fintype ι]

/-- **Deterministic estimation of a Fourier coefficient**
[O'Donnell, Proposition 6.40][ODonnell2014]: if the sample space `g` is `δ`-biased, with
`δ ≥ 0`, then its estimate of `f̂(U)` is within `‖f̂‖₁ δ`. -/
theorem abs_sampleSpaceCoeff_sub_fourierCoeff_le [Nonempty σ] {δ : ℝ} (hδ : 0 ≤ δ)
    {g : σ → ι → Bool} (hg : IsSmallBias δ ((PMF.uniformOfFintype σ).map g))
    (f : (ι → Bool) → ℝ) (U : Finset ι) :
    |sampleSpaceCoeff g f U - fourierCoeff f U| ≤ (∑ S, |fourierCoeff f S|) * δ := by
  have h := hg.fools hδ fun x => chi ℝ U x * f x
  rw [Fools, sum_abs_fourierCoeff_chi_mul, Probability.PMF.sum_uniformOfFintype_map_mul] at h
  have h₁ : sampleSpaceCoeff g f U = 𝔼 s, chi ℝ U (g s) * f (g s) :=
    expect_congr rfl fun s _ => mul_comm _ _
  have h₂ : fourierCoeff f U = 𝔼 x, chi ℝ U x * f x :=
    expect_congr rfl fun x _ => mul_comm _ _
  rwa [h₁, h₂]

/-- A real `r ≥ 0` is at most a positive power of two that is at most `2 (r + 1)`. -/
private theorem exists_le_two_pow (r : ℝ) (hr : 0 ≤ r) :
    ∃ m : ℕ, m ≠ 0 ∧ r ≤ 2 ^ m ∧ (2 : ℝ) ^ m ≤ 2 * (r + 1) := by
  obtain ⟨n, h₁, h₂⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ r + 1) one_lt_two
  exact ⟨n + 1, n.succ_ne_zero, by linarith, by rw [pow_succ]; linarith⟩

/-- A seed of `2 m` bits takes `(2 ^ m) ^ 2` values. -/
private theorem card_bitString_two_mul (m : ℕ) :
    (Fintype.card (BitString (2 * m)) : ℝ) = ((2 : ℝ) ^ m) ^ 2 := by
  rw [BitString.card]
  push_cast
  ring

/-- **A deterministic coefficient estimator with few queries**
[O'Donnell, Proposition 6.40][ODonnell2014]: for `n` coordinates, `s ≥ 0` and `ε > 0`, some sample
space on `2 m` seed bits with `4 ^ m ≤ 4 (n s / ε + 1) ²`, obtained from the powering construction
(`exists_isSmallBias_uniformOfFintype_map`), estimates every Fourier coefficient of every `f` with
`‖f̂‖₁ ≤ s` to within `ε`. The estimate reads `f` at the `4 ^ m` points `sampleSpacePoints g`. -/
theorem exists_abs_sampleSpaceCoeff_sub_fourierCoeff_le (n : ℕ) {s ε : ℝ} (hs : 0 ≤ s)
    (hε : 0 < ε) :
    ∃ (m : ℕ) (g : BitString (2 * m) → BitString n),
      (Fintype.card (BitString (2 * m)) : ℝ) ≤ 4 * (n * s / ε + 1) ^ 2 ∧
      ∀ f : BitString n → ℝ, ∑ S, |fourierCoeff f S| ≤ s →
        ∀ U, |sampleSpaceCoeff g f U - fourierCoeff f U| ≤ ε := by
  obtain ⟨m, hm, hle, hpow⟩ := exists_le_two_pow (n * s / ε) (by positivity)
  obtain ⟨g, hg⟩ := exists_isSmallBias_uniformOfFintype_map n hm
  refine ⟨m, g, ?_, fun f hf U => ?_⟩
  · rw [card_bitString_two_mul]
    calc ((2 : ℝ) ^ m) ^ 2 ≤ (2 * (n * s / ε + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hpow 2
      _ = 4 * (n * s / ε + 1) ^ 2 := by ring
  · have hδ : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 ^ m := by positivity
    refine (abs_sampleSpaceCoeff_sub_fourierCoeff_le hδ hg f U).trans ?_
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc (∑ S, |fourierCoeff f S|) * (((n - 1 : ℕ) : ℝ) / 2 ^ m) ≤ s * (n / 2 ^ m) := by
          gcongr
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ h2]
          rw [div_le_iff₀ hε] at hle
          nlinarith

/-- **Deterministic estimation of a bucket weight** [O'Donnell, Proposition 6.41][ODonnell2014]:
for `|f| ≤ 1`, if the sample spaces `g` and `h` are `δ₁`- and `δ₂`-biased, with `δ₁, δ₂ ≥ 0`, then
their estimate of `W^{S | J̄}[f]` is within `2 ‖f̂‖₁ δ₁ + ‖f̂‖₁² δ₂`. -/
theorem abs_sampleSpaceBucketWeight_sub_bucketWeight_le [Nonempty σ] [Nonempty τ] {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) {g : σ → ι → Bool}
    (hg : IsSmallBias δ₁ ((PMF.uniformOfFintype σ).map g)) {h : τ → ι → Bool}
    (hh : IsSmallBias δ₂ ((PMF.uniformOfFintype τ).map h)) {f : (ι → Bool) → ℝ}
    (hf : ∀ x, |f x| ≤ 1) (J S : Finset ι) :
    |sampleSpaceBucketWeight g h f J S - bucketWeight f J S| ≤
      2 * (∑ U, |fourierCoeff f U|) * δ₁ + (∑ U, |fourierCoeff f U|) ^ 2 * δ₂ := by
  set L := ∑ U, |fourierCoeff f U|
  set G : (ι → Bool) → ℝ := fun z => fourierCoeff (fun x => f (J.piecewise x z)) S
  set e : τ → ℝ := fun t => sampleSpaceCoeff g (fun x => f (J.piecewise x (h t))) S
  have hfz (z : ι → Bool) (x : ι → Bool) : |f (J.piecewise x z)| ≤ 1 := hf _
  -- each squared coefficient estimate is within `2 L δ₁`
  have hG (z : ι → Bool) : |G z| ≤ 1 :=
    (abs_fourierCoeff_le_expect_abs _ S).trans (expect_le univ_nonempty fun x _ => hfz z x)
  have he (t : τ) : |e t ^ 2 - G (h t) ^ 2| ≤ 2 * L * δ₁ := by
    have h₁ := (abs_sampleSpaceCoeff_sub_fourierCoeff_le hδ₁ hg
      (fun x => f (J.piecewise x (h t))) S).trans
      (mul_le_mul_of_nonneg_right (sum_abs_fourierCoeff_piecewise_le f J (h t)) hδ₁)
    have h₂ : |e t + G (h t)| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith [abs_sampleSpaceCoeff_le_one g (hfz (h t)) S, hG (h t)])
    rw [sq_sub_sq, abs_mul]
    nlinarith [abs_nonneg (e t - G (h t)), abs_nonneg (e t + G (h t))]
  have hsum : |sampleSpaceBucketWeight g h f J S - 𝔼 t, G (h t) ^ 2| ≤ 2 * L * δ₁ := by
    rw [sampleSpaceBucketWeight, ← expect_sub_distrib]
    exact (abs_expect_le _ _).trans (expect_le univ_nonempty fun t _ => he t)
  -- `h` fools `G ²`, and `‖Ĝ‖₁ ≤ L`
  have hfool := hh.fools_sq hδ₂ G
  rw [Fools, Probability.PMF.sum_uniformOfFintype_map_mul, ← bucketWeight_eq_expect] at hfool
  have hGnorm : (∑ V, |fourierCoeff G V|) ^ 2 * δ₂ ≤ L ^ 2 * δ₂ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _)
      (sum_abs_fourierCoeff_fourierCoeff_piecewise_le f J S) 2) hδ₂
  calc |sampleSpaceBucketWeight g h f J S - bucketWeight f J S|
      ≤ |sampleSpaceBucketWeight g h f J S - 𝔼 t, G (h t) ^ 2| +
          |𝔼 t, G (h t) ^ 2 - bucketWeight f J S| := abs_sub_le _ _ _
    _ ≤ 2 * L * δ₁ + L ^ 2 * δ₂ := add_le_add hsum (hfool.trans hGnorm)

/-- **A deterministic bucket-weight estimator with few queries**
[O'Donnell, Proposition 6.41][ODonnell2014]: for `n` coordinates, `s ≥ 0` and `ε > 0`, some sample
space `g` on `2 m` seed bits with `4 ^ m ≤ 4 (n (2 s + s²) / ε + 1) ²`, obtained from the powering
construction (`exists_isSmallBias_uniformOfFintype_map`) and used for both sample spaces,
estimates every bucket weight of every `f` with `|f| ≤ 1` and `‖f̂‖₁ ≤ s` to within `ε`. The
estimate reads `f` at the `(4 ^ m) ²` points `sampleSpaceBucketPoints g g J`. -/
theorem exists_abs_sampleSpaceBucketWeight_sub_bucketWeight_le (n : ℕ) {s ε : ℝ} (hs : 0 ≤ s)
    (hε : 0 < ε) :
    ∃ (m : ℕ) (g : BitString (2 * m) → BitString n),
      (Fintype.card (BitString (2 * m)) : ℝ) ≤ 4 * (n * (2 * s + s ^ 2) / ε + 1) ^ 2 ∧
      ∀ f : BitString n → ℝ, (∀ x, |f x| ≤ 1) → ∑ S, |fourierCoeff f S| ≤ s →
        ∀ J S, |sampleSpaceBucketWeight g g f J S - bucketWeight f J S| ≤ ε := by
  obtain ⟨m, hm, hle, hpow⟩ := exists_le_two_pow (n * (2 * s + s ^ 2) / ε) (by positivity)
  obtain ⟨g, hg⟩ := exists_isSmallBias_uniformOfFintype_map n hm
  refine ⟨m, g, ?_, fun f hf1 hf J S => ?_⟩
  · rw [card_bitString_two_mul]
    calc ((2 : ℝ) ^ m) ^ 2 ≤ (2 * (n * (2 * s + s ^ 2) / ε + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hpow 2
      _ = 4 * (n * (2 * s + s ^ 2) / ε + 1) ^ 2 := by ring
  · have hδ : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 ^ m := by positivity
    refine (abs_sampleSpaceBucketWeight_sub_bucketWeight_le hδ hδ hg hg hf1 J S).trans ?_
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have hL0 : 0 ≤ ∑ S, |fourierCoeff f S| := sum_nonneg fun _ _ => abs_nonneg _
    calc 2 * (∑ S, |fourierCoeff f S|) * (((n - 1 : ℕ) : ℝ) / 2 ^ m) +
          (∑ S, |fourierCoeff f S|) ^ 2 * (((n - 1 : ℕ) : ℝ) / 2 ^ m)
        ≤ 2 * s * (n / 2 ^ m) + s ^ 2 * (n / 2 ^ m) := by gcongr
      _ = n * (2 * s + s ^ 2) / 2 ^ m := by ring
      _ ≤ ε := by
          rw [div_le_iff₀ h2]
          rw [div_le_iff₀ hε] at hle
          nlinarith

end Cslib.BitString
