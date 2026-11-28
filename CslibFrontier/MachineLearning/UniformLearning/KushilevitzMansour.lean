/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.DecisionTreeClass
public import CslibFrontier.MachineLearning.UniformLearning.LowDegree
public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery
public import CslibFrontier.Foundations.BooleanAnalysis.BucketWeight
import CslibFrontier.Foundations.BooleanAnalysis.SpectralConcentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Computability.DecisionTree.SpectralNorm
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Kushilevitz–Mansour algorithm

The **Kushilevitz–Mansour algorithm** [KushilevitzMansour1993]
[O'Donnell, Section 3.5][ODonnell2014] learns, with membership queries, every Boolean function of
small spectral norm `∑_S |f̂(S)|` (`UniformLearning.spectralNormClass`); for instance every function
computed by a small decision tree (`UniformLearning.decisionTreeClass`). It finds the large Fourier
coefficients by the bucket search of Goldreich and Levin [GoldreichLevin1989]: the bucket of a set
`S ⊆ J` is the family of the sets `U` with `U ∩ J = S`, and its weight is the bucket weight
(`BitString.bucketWeight`, O'Donnell's `W^{S | J̄}` with `J̄` the complement of `J`). Starting from
the bucket of all sets, the search adds the coordinates one at a time, splitting each surviving
bucket `S` of `J` into the buckets `S` and `insert i S` of `insert i J`, and keeps the buckets whose
estimated weight is at least `θ² / 2` (`UniformLearning.bucketSearch`). On accurate estimates,
the bucket search finds the heavy sets and keeps few buckets: a set `U` with `|f̂(U)| ≥ θ`
contributes `θ²` to each of its buckets, so it is never discarded when every level's estimate of
its bucket reaches the threshold (`UniformLearning.inter_mem_bucketSearch`), and when the
estimates at a level are within `θ² / 4` every surviving bucket weighs more than `θ² / 4`
(`UniformLearning.lt_bucketWeight_of_mem_bucketSearch`), so at most `4 / θ²` buckets survive there
(`UniformLearning.mul_card_bucketSearch_le_one`).
At the last level a bucket is a single set `U`, of weight `f̂(U)²` (`BitString.bucketWeight_univ`).
So if every estimate is within `θ² / 4`, the found sets satisfy the list guarantees of the
Goldreich–Levin Theorem: every `U` with `|f̂(U)| ≥ θ`, only sets with `|f̂(U)| > θ / 2`, and at
most `4 / θ²` of them (`UniformLearning.mem_kmCandidates_of_sq_le_sq`,
`UniformLearning.lt_sq_of_mem_kmCandidates`, `UniformLearning.mul_card_kmCandidates_le_one`). The
search keeps a bucket whose estimate is at least `θ² / 2`, where the book discards one whose
estimate is at most `θ² / 2`; the analysis is the same. With the sample bound below, the query
tree `UniformLearning.kmCandidatesTree`, which makes at most `m (2 n + 3)` non-adaptive queries,
outputs such sets except with probability `δ` from `m ≥ (32 / θ⁴) log (2 (n + 2) 2 ^ n / δ)`
samples (`UniformLearning.uniform_not_kmCandidatesTree_heavy_le_of_log`). This is the query and
sample step toward the Goldreich–Levin Theorem [O'Donnell, Section 3.5][ODonnell2014], whose
running time `poly(n, 1 / θ)` remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131) (see **Cost**). This is the
Fourier form, with `|f̂(U)|`; `Cslib.Crypto.GoldreichLevin` has the hard-core predicate and an
oracle-PPT list decoder for the strings of agreement at least `1 / 2 + ε`, the signed form
`f̂(U) ≥ 2 ε`.

The weights are estimated from samples `(x, y, z)` of three independent uniform points, as the
average of `f (x, z) χ_S(x) f (y, z) χ_S(y)` (`UniformLearning.bucketEstimate`,
`BitString.bucketWeight_eq_expect_sample`), where `(x, z)` takes the coordinates in `J` from `x` and
the others from `z`. By Hoeffding's inequality one estimate from `(2 / γ²) log (2 / δ)` samples,
reading `f` at two points each, is within `γ` except with probability `δ`
(`UniformLearning.uniform_abs_bucketEstimate_sub_ge_le_of_log`), the sample bound in the proof of
[O'Donnell, Proposition 3.40][ODonnell2014]. Here the same `m` samples serve every bucket of every
level, so the queries are non-adaptive: the learner queries `f` at `x` and at the points `(x, z)`,
`(y, z)` of every sample and every level, `m (2 n + 3)` queries for `n` coordinates
(`UniformLearning.kmLearner_queriesAtMost`), and then runs the search on the answers. The analysis
takes a union bound over all `2 ^ n` buckets of each level, which costs a factor `n` in the number
of samples compared with fresh samples for each weighing. The hypothesis is the sign of the
expansion on the found sets with coefficients estimated from the points `x`
(`UniformLearning.kmHypothesis`, `UniformLearning.kmLearner`).

If all estimates are within `θ² / 4` of their values, the hypothesis has error at most `θ² / 4`
plus the weight of the coefficients of absolute value below `θ`
(`UniformLearning.uniformError_kmHypothesis_le_add`), since the found sets carry all the others;
for a function of spectral norm at most `L` this weight is at most `θ L`
(`BitString.sum_fourierCoeff_sq_le_mul_sum_abs`), so the error is at most `θ² / 4 + θ L`
(`UniformLearning.uniformError_kmHypothesis_le`). Hoeffding's inequality and the union bound
make the estimates accurate except with probability at most `2 (n + 2) 2 ^ n exp (-m θ⁴ / 32)`
(`UniformLearning.uniform_not_accurate_le`). With `θ = ε / (2 L)` this gives the query and
sample step toward the **Kushilevitz–Mansour theorem** [O'Donnell, Theorem 3.38][ODonnell2014]:
the functions of spectral norm at most `L` are learned with error `ε` and confidence `1 - δ` from
`m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence `m (2 n + 3)` membership queries,
polynomial in `n`, `L`, `1 / ε` and `log (1 / δ)` (`UniformLearning.kmLearner_learns`). The
theorem's running time `poly(n, L, 1 / ε)` remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131) (see **Cost**). By the
spectral norm bound for decision trees (`DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount`),
this applies to the functions computed by decision trees with at most `L` leaves, the
decision-tree case of Theorem 3.38 (`UniformLearning.kmLearner_learns_decisionTree`), with the
same gap.

More generally, if the spectrum of `f` is `ε / 4`-concentrated on some collection of at most `M`
sets (`UniformLearning.concentratedClass`), its coefficients below `θ` weigh at most
`ε / 4 + M θ²` (`BitString.sum_fourierCoeff_sq_le_sum_compl_add`). With `θ² = ε / (4 M)` the
algorithm learns such functions with error `ε` from `m ≥ (512 M² / ε²) log (2 (n + 2) 2 ^ n / δ)`
samples, hence `m (2 n + 3)` membership queries, polynomial in `n`, `M`, `1 / ε` and `log (1 / δ)`
(`UniformLearning.kmLearner_learns_concentrated`). This is the query and sample step toward
[O'Donnell, Theorem 3.37][ODonnell2014]; the theorem's running time `poly(M, n, 1 / ε)` remains
open on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131) (see **Cost**). The
book's route (Exercise 3.39) applies the Goldreich–Levin list guarantee and then Theorem 3.29 to
the listed sets; here the proof goes through the combined error bound on accurate samples
(`UniformLearning.uniformError_kmHypothesis_le_add`) instead. Functions of
spectral norm at most `L` are `ε / 4`-concentrated on about `4 L² / ε` sets, but the spectral-norm
step above, with its own threshold, needs fewer samples.

**Cost.** Only the numbers of samples and queries are certified; the running time is not certified
by a machine model. On accurate samples the search computes at most `8 / θ²` bucket estimates at
each level, each from the `m` samples, and estimates at most `4 / θ²` coefficients; this count of
arithmetic operations is informal. The search has no cap on the number of buckets: the book
bounds the active buckets by `4 / θ²` only on accurate estimates, and `UniformLearning.bucketSearch`
keeps every bucket whose estimate passes the threshold, so on inaccurate samples it can keep up to
`2 ^ k` buckets at level `k` and is not polynomial, even informally. The same holds for the query
tree `UniformLearning.kmCandidatesTree`: its samples and queries are certified, its running time is
not. Its bounds are those of the Kushilevitz–Mansour learner, so they are loose for listing the
coefficients alone. It queries all of `kmQueries ω`: the `2 m` points `(x, z)`, `(y, z)` at each
of the `n + 1` levels, `2 m (n + 1)` in all, which the search reads, plus the `m` points `x` that
only the hypothesis reads, `m (2 n + 3)` in all. Its sample bound goes through `KMAccurate`, whose
union bound counts `2 ^ n` buckets at each of the `n + 1` levels and also the `2 ^ n` sample
coefficients, `(n + 2) 2 ^ n` events; the search alone needs `(n + 1) 2 ^ n`.

## Usage

Open `Cslib.MachineLearning.UniformLearning`. A class `C` of Boolean functions whose spectra, read
as signs, are `ε / 4`-concentrated on at most `M ≥ 1` sets is a subset of
`concentratedClass ι M (ε / 4)`; apply
`UniformLearning.kmLearner_learns_concentrated_and_queriesAtMost` with threshold `√(ε / (4 M))`
and any `m` at least `(512 M² / ε²) log (2 (n + 2) 2 ^ n / δ)` (for instance its ceiling), and
restrict to `C` with `QueryLearner.Learns.mono`. This certifies the samples and queries of
[O'Donnell, Theorem 3.37][ODonnell2014], not its running time, which remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). To bound the error of the hypothesis for another
class, prove the samples accurate with `UniformLearning.uniform_not_accurate_le_of_log` and bound
the weight of the small coefficients in `UniformLearning.uniformError_kmHypothesis_le_add`, for
instance by `BitString.sum_fourierCoeff_sq_le_sum_compl_add` or
`BitString.sum_fourierCoeff_sq_le_mul_sum_abs`. For a single bucket weight `bucketWeight F J S`,
which is O'Donnell's `W^{S | J̄}[F]` for `S ⊆ J` and `0` otherwise,
`UniformLearning.uniform_abs_bucketEstimate_sub_ge_le_of_log` takes `m ≥ (2 / γ²) log (2 / δ)`
samples; the estimate reads `f` at `2 m` points, but that theorem certifies neither queries nor
time. Turning another tail bound `c exp (-(a m))` into a sample size is
`Real.mul_exp_neg_le_of_log`. To list the large Fourier coefficients of a Boolean function `f`
with threshold `τ > 0`, take any `m` at least `(32 / τ⁴) log (2 (n + 2) 2 ^ n / δ)` and apply
`UniformLearning.uniform_not_kmCandidatesTree_heavy_le_of_log`: except with probability `δ` over
the samples `ω`, the list `(kmCandidatesTree τ ω).eval f` has the Goldreich–Levin guarantees, and
`UniformLearning.depth_kmCandidatesTree_le` bounds its queries by `m (2 n + 3)`; on samples known
to be accurate, use `UniformLearning.mem_kmCandidates_of_sq_le_sq`,
`UniformLearning.lt_sq_of_mem_kmCandidates` and `UniformLearning.mul_card_kmCandidates_le_one`
directly. Checked clients show that a parity is concentrated on one set and
not on none, that the small-coefficient bound is attained by a parity, bound the hypothesis error
for parities, instantiate the sample bound on two bits, learn the parities through `Learns.mono`,
instantiate the query and sample step for `M = 3` on two bits, estimate two bucket weights of a
parity, and find exactly a parity's own set with the query tree, on accurate samples and with
probability `1 / 2` from `⌈32 log 64⌉` samples on two bits, in
[`CslibFrontierTests/KushilevitzMansourConcentrated.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/KushilevitzMansourConcentrated.lean);
the spectral-norm and decision-tree steps are checked in
[`CslibFrontierTests/FourierLearning.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/FourierLearning.lean).

## Main definitions

* `Cslib.MachineLearning.UniformLearning.spectralNormClass`: the functions of bounded spectral
  norm.
* `Cslib.MachineLearning.UniformLearning.bucketSearch`: the bucket search of Goldreich–Levin and
  Kushilevitz–Mansour.
* `Cslib.MachineLearning.UniformLearning.bucketEstimate`,
  `Cslib.MachineLearning.UniformLearning.sampleCoeff`: the empirical bucket weights and Fourier
  coefficients of the samples.
* `Cslib.MachineLearning.UniformLearning.kmHypothesis`,
  `Cslib.MachineLearning.UniformLearning.kmLearner`: the Kushilevitz–Mansour algorithm.
* `Cslib.MachineLearning.UniformLearning.kmCandidatesTree`: the bucket search of the
  Goldreich–Levin algorithm as a non-adaptive query tree.
* `Cslib.MachineLearning.UniformLearning.KMAccurate`: accurate samples.
* `Cslib.MachineLearning.UniformLearning.concentratedClass`: the functions whose spectrum is
  concentrated on few sets.

## Main results

* `Cslib.MachineLearning.UniformLearning.inter_mem_bucketSearch`,
  `Cslib.MachineLearning.UniformLearning.lt_bucketWeight_of_mem_bucketSearch`,
  `Cslib.MachineLearning.UniformLearning.mul_card_bucketSearch_le_one`: on accurate estimates, the
  bucket search finds the heavy sets and keeps only heavy buckets, hence few.
* `Cslib.MachineLearning.UniformLearning.mem_kmCandidates_of_sq_le_sq`,
  `Cslib.MachineLearning.UniformLearning.lt_sq_of_mem_kmCandidates`,
  `Cslib.MachineLearning.UniformLearning.mul_card_kmCandidates_le_one`: the found sets on accurate
  samples.
* `Cslib.MachineLearning.UniformLearning.depth_kmCandidatesTree_le`: the query tree makes at most
  `m (2 n + 3)` queries.
* `Cslib.MachineLearning.UniformLearning.uniform_not_kmCandidatesTree_heavy_le_of_log`: the query
  and sample step toward the Goldreich–Levin Theorem [O'Donnell, Section 3.5][ODonnell2014],
  whose running time remains open on
  [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).
* `Cslib.MachineLearning.UniformLearning.uniformError_kmHypothesis_le_add`,
  `Cslib.MachineLearning.UniformLearning.uniformError_kmHypothesis_le`: the error on accurate
  samples.
* `Cslib.MachineLearning.UniformLearning.uniform_abs_bucketEstimate_sub_ge_le`,
  `Cslib.MachineLearning.UniformLearning.uniform_abs_bucketEstimate_sub_ge_le_of_log`: the
  sample bound in the proof of Proposition 3.40, estimating one bucket weight.
* `Cslib.MachineLearning.UniformLearning.uniform_not_accurate_le`,
  `Cslib.MachineLearning.UniformLearning.uniform_not_accurate_le_of_log`: the samples are accurate
  with high probability.
* `Cslib.MachineLearning.UniformLearning.kmLearner_learns`,
  `Cslib.MachineLearning.UniformLearning.kmLearner_learns_and_queriesAtMost`: the query and sample
  step toward the Kushilevitz–Mansour theorem, [O'Donnell, Theorem 3.38][ODonnell2014], whose
  running time remains open on
  [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).
* `Cslib.MachineLearning.UniformLearning.kmLearner_learns_decisionTree`,
  `Cslib.MachineLearning.UniformLearning.kmLearner_learns_decisionTree_and_queriesAtMost`: learning
  decision trees with membership queries, the query and sample step toward the decision-tree case
  of Theorem 3.38, with the same gap.
* `Cslib.MachineLearning.UniformLearning.kmLearner_learns_concentrated`,
  `Cslib.MachineLearning.UniformLearning.kmLearner_learns_concentrated_and_queriesAtMost`:
  learning concentrated classes, the query and sample step toward
  [O'Donnell, Theorem 3.37][ODonnell2014], whose running time remains open on
  [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).

## References

* [E. Kushilevitz and Y. Mansour, *Learning decision trees using the Fourier
  spectrum*][KushilevitzMansour1993]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning Cslib.Probability
open scoped BigOperators ENNReal

variable {ι : Type*} {m : ℕ}

/-! ### The bucket search -/

section BucketSearch

variable [DecidableEq ι]

/-- The sets of coordinates weighed by the bucket search over the list `l`: the sets of
coordinates of the suffixes of `l`, from `l` itself down to the empty list. -/
def searchLevels : List ι → List (Finset ι)
  | [] => [∅]
  | i :: l => insert i l.toFinset :: searchLevels l

@[simp] theorem length_searchLevels (l : List ι) : (searchLevels l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [searchLevels, ih]

/-- The coordinates of `l` are its first level. -/
theorem toFinset_mem_searchLevels (l : List ι) : l.toFinset ∈ searchLevels l := by
  cases l with
  | nil => simp [searchLevels]
  | cons i l => simp [searchLevels]

/-- **The bucket search** of Goldreich–Levin and Kushilevitz–Mansour over the list `l` of
coordinates, given estimates `est J S` of the bucket weights `W^{S | J̄}` and a threshold `τ`.
Starting from the bucket of all sets, it adds the coordinates of `l` from the last to the first,
splits each surviving bucket `S` of `J` into the buckets `S` and `insert i S` of `insert i J`, and
keeps the buckets whose estimated weight is at least `τ`. -/
noncomputable def bucketSearch (est : Finset ι → Finset ι → ℝ) (τ : ℝ) :
    List ι → Finset (Finset ι)
  | [] => ({∅} : Finset (Finset ι)).filter fun S => τ ≤ est ∅ S
  | i :: l => (bucketSearch est τ l ∪ (bucketSearch est τ l).image (insert i)).filter
      fun S => τ ≤ est (insert i l.toFinset) S

/-- The bucket search reads the estimates only at its levels. -/
theorem bucketSearch_congr {est est' : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    (h : ∀ J ∈ searchLevels l, ∀ S, est J S = est' J S) :
    bucketSearch est τ l = bucketSearch est' τ l := by
  induction l with
  | nil =>
    simp only [searchLevels, List.mem_singleton, forall_eq] at h
    simp only [bucketSearch, h]
  | cons i l ih =>
    simp only [searchLevels, List.mem_cons, forall_eq_or_imp] at h
    simp only [bucketSearch, ih h.2, h.1]

/-- Every bucket kept by the search over `l` has estimated weight at least `τ` at the level of
the coordinates of `l`. -/
theorem le_of_mem_bucketSearch {est : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    {S : Finset ι} (hS : S ∈ bucketSearch est τ l) : τ ≤ est l.toFinset S := by
  cases l with
  | nil => exact (mem_filter.1 hS).2
  | cons i l =>
    rw [List.toFinset_cons]
    exact (mem_filter.1 hS).2

/-- **Completeness of the bucket search**: if at every level `J` the bucket of `U ∩ J` has
estimated weight at least `τ`, then the search over `l` keeps the bucket `U ∩ l`. -/
theorem inter_mem_bucketSearch {est : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    {U : Finset ι} (h : ∀ J ∈ searchLevels l, τ ≤ est J (U ∩ J)) :
    U ∩ l.toFinset ∈ bucketSearch est τ l := by
  induction l with
  | nil =>
    simp only [searchLevels, List.mem_singleton, forall_eq, inter_empty] at h
    simp [bucketSearch, h]
  | cons i l ih =>
    simp only [searchLevels, List.mem_cons, forall_eq_or_imp] at h
    rw [List.toFinset_cons]
    refine mem_filter.2 ⟨?_, h.1⟩
    by_cases hi : i ∈ U
    · rw [inter_insert_of_mem hi]
      exact mem_union_right _ (mem_image_of_mem _ (ih h.2))
    · rw [inter_insert_of_notMem hi]
      exact mem_union_left _ (ih h.2)

variable [Fintype ι]

/-- **A kept bucket is heavy**: if the estimate of the bucket weight of `S` at the level of the
coordinates of `l` is within `θ² / 4`, and the search over `l` with threshold `θ² / 2` keeps `S`,
then the bucket weighs more than `θ² / 4`. -/
theorem lt_bucketWeight_of_mem_bucketSearch (F : (ι → Bool) → ℝ) {θ : ℝ}
    {est : Finset ι → Finset ι → ℝ} {l : List ι} {S : Finset ι}
    (hW : |est l.toFinset S - bucketWeight F l.toFinset S| < θ ^ 2 / 4)
    (hS : S ∈ bucketSearch est (θ ^ 2 / 2) l) :
    θ ^ 2 / 4 < bucketWeight F l.toFinset S := by
  have h₁ := le_of_mem_bucketSearch hS
  have h₂ := (abs_lt.1 hW).2
  linarith

/-- **Few buckets survive**: if the estimates at the level of the coordinates of `l` are within
`θ² / 4` of the bucket weights of a Boolean function, then the search over `l` with threshold
`θ² / 2` keeps at most `4 / θ²` buckets. -/
theorem mul_card_bucketSearch_le_one (f : (ι → Bool) → Bool) {θ : ℝ} (est : Finset ι → Finset ι → ℝ)
    (l : List ι)
    (hW : ∀ S, |est l.toFinset S - bucketWeight (fun x => signVal (f x)) l.toFinset S| <
      θ ^ 2 / 4) :
    θ ^ 2 / 4 * #(bucketSearch est (θ ^ 2 / 2) l) ≤ 1 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hS (S : Finset ι) (hS : S ∈ bucketSearch est (θ ^ 2 / 2) l) :
      θ ^ 2 / 4 ≤ bucketWeight F l.toFinset S :=
    (lt_bucketWeight_of_mem_bucketSearch F (hW S) hS).le
  calc θ ^ 2 / 4 * #(bucketSearch est (θ ^ 2 / 2) l)
      = ∑ _S ∈ bucketSearch est (θ ^ 2 / 2) l, θ ^ 2 / 4 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ bucketSearch est (θ ^ 2 / 2) l, bucketWeight F l.toFinset S := sum_le_sum hS
    _ ≤ ∑ U, fourierCoeff F U ^ 2 := sum_bucketWeight_le F _ _
    _ = 1 := sum_fourierCoeff_sq_signVal f

end BucketSearch

/-! ### The algorithm -/

variable [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The Boolean functions whose spectral norm `∑_S |f̂(S)|`, read as signs, is at most `L`. -/
def spectralNormClass (L : ℝ) : ConceptClass (ι → Bool) Bool :=
  {f | ∑ S, |fourierCoeff (fun x => signVal (f x)) S| ≤ L}

/-- The empirical estimate of the bucket weight `W^{S | J̄}` of `g`, read as signs, from the
samples `ω j = (x, y, z)`: the average of `g (x, z) χ_S(x) g (y, z) χ_S(y)`, where `(x, z)` takes
the coordinates in `J` from `x` and the others from `z`. -/
noncomputable def bucketEstimate (g : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (J S : Finset ι) : ℝ :=
  (∑ j,
    let (x, y, z) := ω j
    signVal (g (J.piecewise x z)) * chi ℝ S x *
      (signVal (g (J.piecewise y z)) * chi ℝ S y)) / m

/-- The empirical Fourier coefficient of `g` on `S` from the first points of the samples. -/
noncomputable def sampleCoeff (g : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (S : Finset ι) : ℝ :=
  empiricalCoeff (examples g fun j => (ω j).1) S

/-- The sets found by the Kushilevitz–Mansour algorithm with threshold `θ`: the bucket search over
all coordinates, keeping the buckets with estimated weight at least `θ² / 2`. -/
noncomputable def kmCandidates (g : (ι → Bool) → Bool) (θ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : Finset (Finset ι) :=
  bucketSearch (bucketEstimate g ω) (θ ^ 2 / 2) (univ : Finset ι).toList

/-- The hypothesis of the Kushilevitz–Mansour algorithm: the sign of the expansion on the found
sets, with the empirical coefficients of the samples. -/
noncomputable def kmHypothesis (g : (ι → Bool) → Bool) (θ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : (ι → Bool) → Bool :=
  signRound fun x => ∑ S ∈ kmCandidates g θ ω, sampleCoeff g ω S * chi ℝ S x

/-- The points queried by the Kushilevitz–Mansour algorithm: the first point `x` of each sample,
and the points `(x, z)` and `(y, z)` of each sample `(x, y, z)` at every level `J` of the
search. -/
noncomputable def kmQueries (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    List (ι → Bool) :=
  (List.finRange m).map (fun j => (ω j).1) ++
    (searchLevels (univ : Finset ι).toList).flatMap fun J =>
      (List.finRange m).flatMap fun j =>
        let (x, y, z) := ω j
        [J.piecewise x z, J.piecewise y z]

/-- The algorithm queries `m (2 n + 3)` points for `n` coordinates. -/
theorem length_kmQueries (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmQueries ω).length = m * (2 * Fintype.card ι + 3) := by
  have hlen (J : Finset ι) :
      ((List.finRange m).map fun j =>
        (let (x, y, z) := ω j; [J.piecewise x z, J.piecewise y z]).length) =
      (List.finRange m).map fun _ => 2 :=
    List.map_congr_left fun j _ => by rcases ω j with ⟨x, y, z⟩; rfl
  simp only [kmQueries, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, hlen, List.map_const', List.sum_replicate, smul_eq_mul,
    length_searchLevels, length_toList, card_univ]
  ring

/-- The found sets depend only on the values of the target at the queried points. -/
theorem kmCandidates_congr (θ : ℝ) (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))
    {g g' : (ι → Bool) → Bool} (h : ∀ x ∈ kmQueries ω, g x = g' x) :
    kmCandidates g θ ω = kmCandidates g' θ ω := by
  have hmem (J : Finset ι) (hJ : J ∈ searchLevels (univ : Finset ι).toList) (j : Fin m)
      (p : ι → Bool)
      (hp : p ∈ (let (x, y, z) := ω j; [J.piecewise x z, J.piecewise y z])) :
      g p = g' p :=
    h p (List.mem_append_right _ (List.mem_flatMap.2
      ⟨J, hJ, List.mem_flatMap.2 ⟨j, List.mem_finRange j, hp⟩⟩))
  refine bucketSearch_congr fun J hJ S => ?_
  simp only [bucketEstimate]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hωj : ω j with ⟨x, y, z⟩
  have h₁ : g (J.piecewise x z) = g' (J.piecewise x z) :=
    hmem J hJ j _ (by simp [hωj])
  have h₂ : g (J.piecewise y z) = g' (J.piecewise y z) :=
    hmem J hJ j _ (by simp [hωj])
  simp only [h₁, h₂]

/-- The hypothesis depends only on the answers at the queried points. -/
theorem kmHypothesis_congr (θ : ℝ) (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))
    {g g' : (ι → Bool) → Bool} (h : ∀ x ∈ kmQueries ω, g x = g' x) :
    kmHypothesis g θ ω = kmHypothesis g' θ ω := by
  have hx (j : Fin m) : g (ω j).1 = g' (ω j).1 :=
    h _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))
  have hcoeff : sampleCoeff g ω = sampleCoeff g' ω := by
    funext S
    simp only [sampleCoeff, empiricalCoeff, examples_apply, hx]
  simp only [kmHypothesis, hcoeff, kmCandidates_congr θ ω h]

variable (ι m) in
/-- **The Kushilevitz–Mansour algorithm** with threshold `θ` from `m` samples: draw `m`
independent samples of three uniform points, query the target at the points `kmQueries`, run the
bucket search with threshold `θ² / 2` on the estimated bucket weights, and output the sign of the
expansion on the found sets with estimated coefficients. Its queries are non-adaptive. -/
noncomputable def kmLearner (θ : ℝ) :
    QueryLearner ι (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :=
  QueryLearner.ofNonadaptive kmQueries fun g ω => kmHypothesis g θ ω

/-- Run on the target `f`, the algorithm outputs `kmHypothesis f θ ω`. -/
theorem eval_kmLearner (θ : ℝ) (f : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmLearner ι m θ ω).eval f = kmHypothesis f θ ω :=
  QueryLearner.eval_ofNonadaptive (fun ω _ _ h => kmHypothesis_congr θ ω h) f ω

/-- **The Kushilevitz–Mansour algorithm makes `m (2 n + 3)` membership queries** for `n`
coordinates. -/
theorem kmLearner_queriesAtMost (θ : ℝ) :
    (kmLearner ι m θ).QueriesAtMost (m * (2 * Fintype.card ι + 3)) := fun ω =>
  (QueryLearner.depth_ofNonadaptive_le _ _ ω).trans_eq (length_kmQueries ω)

/-- **The Goldreich–Levin bucket search** with threshold `θ` on the samples `ω`, as a query tree:
query the target at the points `kmQueries ω`, then output the sets found by the bucket search on
the answers. Its queries are non-adaptive; its running time is not certified. -/
noncomputable def kmCandidatesTree (θ : ℝ) (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    DecisionTree (ι → Bool) (Finset (Finset ι)) :=
  DecisionTree.queryAll (fun g => kmCandidates g θ ω) (kmQueries ω) fun _ => false

/-- Run on the target `f`, the query tree outputs `kmCandidates f θ ω`. -/
theorem eval_kmCandidatesTree (θ : ℝ) (f : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmCandidatesTree θ ω).eval f = kmCandidates f θ ω :=
  DecisionTree.eval_queryAll_of_congr (fun _ _ h => kmCandidates_congr θ ω h) _ f

/-- The query tree makes at most `m (2 n + 3)` membership queries for `n` coordinates. -/
theorem depth_kmCandidatesTree_le (θ : ℝ) (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmCandidatesTree θ ω).depth ≤ m * (2 * Fintype.card ι + 3) :=
  (DecisionTree.depth_queryAll_le _ _ _).trans_eq (length_kmQueries ω)

/-! ### The analysis -/

/-- The samples `ω` are *accurate* for `f` at precision `γ`: every bucket estimate at every level
of the search over all coordinates, and every sample coefficient, is within `γ` of its value. -/
def KMAccurate (f : (ι → Bool) → Bool) (γ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : Prop :=
  (∀ J ∈ searchLevels (univ : Finset ι).toList, ∀ S,
      |bucketEstimate f ω J S - bucketWeight (fun x => signVal (f x)) J S| < γ) ∧
    ∀ S, |sampleCoeff f ω S - fourierCoeff (fun x => signVal (f x)) S| < γ

/-- On samples accurate at precision `θ² / 4`, the found sets include every set whose coefficient
has square at least `θ²`. -/
theorem mem_kmCandidates_of_sq_le_sq (f : (ι → Bool) → Bool) {θ : ℝ}
    {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)} (hω : KMAccurate f (θ ^ 2 / 4) ω)
    {U : Finset ι} (hU : θ ^ 2 ≤ fourierCoeff (fun x => signVal (f x)) U ^ 2) :
    U ∈ kmCandidates f θ ω := by
  have huniv : ((univ : Finset ι).toList).toFinset = univ := toList_toFinset _
  have h := inter_mem_bucketSearch (est := bucketEstimate f ω) (τ := θ ^ 2 / 2)
    (l := (univ : Finset ι).toList) (U := U) fun J hJ => by
      have h₁ := (abs_lt.1 (hω.1 J hJ (U ∩ J))).1
      have h₂ := sq_fourierCoeff_le_bucketWeight (fun x => signVal (f x)) J U
      nlinarith
  rwa [huniv, inter_univ] at h

/-- On samples accurate at precision `θ² / 4`, every found set has a coefficient of square above
`θ² / 4`: at the last level a bucket is a single set, of weight `f̂(U)²`. -/
theorem lt_sq_of_mem_kmCandidates (f : (ι → Bool) → Bool) {θ : ℝ}
    {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)} (hω : KMAccurate f (θ ^ 2 / 4) ω)
    {U : Finset ι} (hU : U ∈ kmCandidates f θ ω) :
    θ ^ 2 / 4 < fourierCoeff (fun x => signVal (f x)) U ^ 2 := by
  have h := lt_bucketWeight_of_mem_bucketSearch _ (hω.1 _ (toFinset_mem_searchLevels _) U) hU
  rwa [toList_toFinset, bucketWeight_univ] at h

/-- On samples accurate at precision `θ² / 4`, at most `4 / θ²` sets are found. -/
theorem mul_card_kmCandidates_le_one (f : (ι → Bool) → Bool) {θ : ℝ}
    {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)} (hω : KMAccurate f (θ ^ 2 / 4) ω) :
    θ ^ 2 / 4 * #(kmCandidates f θ ω) ≤ 1 :=
  mul_card_bucketSearch_le_one f _ _ fun S => hω.1 _ (toFinset_mem_searchLevels _) S

/-- **The Kushilevitz–Mansour algorithm on accurate samples.** Let `θ > 0`. If the samples are
accurate at precision `θ² / 4`, then the hypothesis has error at most `θ² / 4` plus the Fourier
weight of `f`, read as signs, on the sets whose coefficient has absolute value below `θ`. -/
theorem uniformError_kmHypothesis_le_add (f : (ι → Bool) → Bool) {θ : ℝ} (hθ : 0 < θ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (hω : KMAccurate f (θ ^ 2 / 4) ω) :
    uniformError f (kmHypothesis f θ ω) ≤
      θ ^ 2 / 4 + ∑ S with fourierCoeff (fun x => signVal (f x)) S ^ 2 < θ ^ 2,
        fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  have hc := hω.2
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set T := kmCandidates f θ ω
  have hcard : θ ^ 2 / 4 * #T ≤ 1 := mul_card_kmCandidates_le_one f hω
  -- every set with a coefficient of absolute value at least `θ` is found
  have hheavy (U : Finset ι) (hU : θ ^ 2 ≤ fourierCoeff F U ^ 2) : U ∈ T :=
    mem_kmCandidates_of_sq_le_sq f hω hU
  have herr := hammingDist_signRound_sum_mul_chi_div_le f T (sampleCoeff f ω)
  have hin : ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2 ≤ θ ^ 2 / 4 :=
    calc ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2
        ≤ ∑ _S ∈ T, (θ ^ 2 / 4) ^ 2 := sum_le_sum fun S _ => by
          rw [← sq_abs, abs_sub_comm]
          exact pow_le_pow_left₀ (abs_nonneg _) (hc S).le 2
      _ = θ ^ 2 / 4 * #T * (θ ^ 2 / 4) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 * (θ ^ 2 / 4) := by gcongr
      _ = θ ^ 2 / 4 := one_mul _
  have hout : ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 ≤
      ∑ S with fourierCoeff F S ^ 2 < θ ^ 2, fourierCoeff F S ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun S hS => mem_filter.2 ⟨mem_univ S,
      lt_of_not_ge fun h => mem_compl.1 hS (hheavy S h)⟩) fun _ _ _ => sq_nonneg _
  have : uniformError f (kmHypothesis f θ ω) ≤
      ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2 + ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 :=
    herr
  linarith

/-- **The Kushilevitz–Mansour algorithm on accurate samples, for small spectral norm.** Let the
spectral norm of `f`, read as signs, be at most `L`, and let `θ > 0`. If the samples are accurate
at precision `θ² / 4`, then the hypothesis has error at most `θ² / 4 + θ L`. -/
theorem uniformError_kmHypothesis_le (f : (ι → Bool) → Bool) {L θ : ℝ} (hθ : 0 < θ)
    (hL : ∑ S, |fourierCoeff (fun x => signVal (f x)) S| ≤ L)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (hω : KMAccurate f (θ ^ 2 / 4) ω) :
    uniformError f (kmHypothesis f θ ω) ≤ θ ^ 2 / 4 + θ * L := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hlight : ∑ S with fourierCoeff F S ^ 2 < θ ^ 2, fourierCoeff F S ^ 2 ≤ θ * L :=
    (sum_fourierCoeff_sq_le_mul_sum_abs hθ.le fun S hS =>
      (abs_lt_of_sq_lt_sq (mem_filter.1 hS).2 hθ.le).le).trans (by gcongr)
  linarith [uniformError_kmHypothesis_le_add f hθ ω hω]

omit [Fintype ι] [DecidableEq ι] in
/-- A product of two signs and two characters has absolute value at most one. -/
private theorem abs_signVal_mul_chi_mul_le_one (a b : Bool) (S : Finset ι) (x y : ι → Bool) :
    |signVal a * chi ℝ S x * (signVal b * chi ℝ S y)| ≤ 1 := by
  rw [abs_mul, abs_mul, abs_mul, abs_signVal, abs_signVal, abs_chi, abs_chi]
  norm_num

/-- **Estimating a bucket weight**, the sample bound in the proof of
[O'Donnell, Proposition 3.40][ODonnell2014]: from `m` samples of three independent uniform points,
the empirical bucket weight of `f` on `S` with respect to `J` is off from the bucket weight of
`f` read as signs, O'Donnell's `W^{S | J̄}[f]` when `S ⊆ J` and `0` otherwise, by at least `γ`
with probability at most `2 exp (-m γ² / 2)`, by Hoeffding's inequality. The estimate reads `f`
at the two points `(x, z)` and `(y, z)` of each sample. -/
theorem uniform_abs_bucketEstimate_sub_ge_le (f : (ι → Bool) → Bool) (J S : Finset ι)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | γ ≤ |bucketEstimate f ω J S - bucketWeight (fun x => signVal (f x)) J S|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  have h := PMF.uniform_abs_sum_div_sub_expect_ge_le (m := m)
    (fun ((x, y, z) : (ι → Bool) × (ι → Bool) × (ι → Bool)) =>
      signVal (f (J.piecewise x z)) * chi ℝ S x * (signVal (f (J.piecewise y z)) * chi ℝ S y))
    (fun (x, y, z) => abs_signVal_mul_chi_mul_le_one _ _ S _ _) hγ
  rwa [show (𝔼 p : (ι → Bool) × (ι → Bool) × (ι → Bool),
      let (x, y, z) := p
      signVal (f (J.piecewise x z)) * chi ℝ S x * (signVal (f (J.piecewise y z)) * chi ℝ S y)) =
      bucketWeight (fun x => signVal (f x)) J S by
    rw [bucketWeight_eq_expect_sample]] at h

/-- **Estimating a bucket weight with confidence**, the sample bound in the proof of
[O'Donnell, Proposition 3.40][ODonnell2014]: from `m ≥ (2 / γ²) log (2 / δ)` samples, the
empirical bucket weight is within `γ` of `W^{S | J̄}[f]` for `S ⊆ J` (and of `0` otherwise)
except with probability at most `δ`. The estimate reads `f` at `2 m` points; queries and time are
not certified here. -/
theorem uniform_abs_bucketEstimate_sub_ge_le_of_log (f : (ι → Bool) → Bool) (J S : Finset ι)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hm : 2 / γ ^ 2 * Real.log (2 / δ) ≤ m) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | γ ≤ |bucketEstimate f ω J S - bucketWeight (fun x => signVal (f x)) J S|} ≤
        ENNReal.ofReal δ := by
  refine (uniform_abs_bucketEstimate_sub_ge_le f J S hγ.le).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [show -(m * γ ^ 2) / 2 = -(γ ^ 2 / 2 * m) by ring]
  exact Real.mul_exp_neg_le_of_log le_rfl two_pos (by positivity) hδ
    (hm.trans_eq' (by ring))

/-- **The samples are accurate with high probability**: `m` samples fail to be accurate at
precision `θ² / 4` with probability at most `2 (n + 2) 2 ^ n exp (-m θ⁴ / 32)` for `n`
coordinates. -/
theorem uniform_not_accurate_le (f : (ι → Bool) → Bool) (θ : ℝ) (m : ℕ) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | ¬ KMAccurate f (θ ^ 2 / 4) ω} ≤
      ENNReal.ofReal (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι *
        Real.exp (-(m * θ ^ 4) / 32)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set n := Fintype.card ι
  set μ := (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
  set c : ℝ := 2 * Real.exp (-(m * θ ^ 4) / 32) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hγ : (0 : ℝ) ≤ θ ^ 2 / 4 := by positivity
  have hexp : -(m * (θ ^ 2 / 4) ^ 2) / 2 = -(m * θ ^ 4) / 32 := by ring
  -- one bucket estimate
  have hbucket (J S : Finset ι) :
      μ {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|} ≤ ENNReal.ofReal c := by
    have h := uniform_abs_bucketEstimate_sub_ge_le (m := m) f J S hγ
    rwa [hexp] at h
  -- one sample coefficient
  have hcoeff (S : Finset ι) :
      μ {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} ≤ ENNReal.ofReal c := by
    have h := PMF.uniform_abs_sum_div_sub_expect_ge_le (m := m)
      (fun p : (ι → Bool) × (ι → Bool) × (ι → Bool) => F p.1 * chi ℝ S p.1)
      (fun p => by rw [abs_mul, abs_signVal, abs_chi, one_mul]) hγ
    have hmean : 𝔼 p : (ι → Bool) × (ι → Bool) × (ι → Bool), F p.1 * chi ℝ S p.1 =
        fourierCoeff F S := by
      rw [← univ_product_univ, expect_product]
      exact expect_congr rfl fun x _ => expect_const univ_nonempty (F x * chi ℝ S x)
    rw [hmean, hexp] at h
    exact h
  -- the union bound
  clear_value c
  set A := (searchLevels (univ : Finset ι).toList).toFinset
  have hA : (#A : ℝ) ≤ n + 1 := by
    have := List.toFinset_card_le (searchLevels (univ : Finset ι).toList)
    rw [length_searchLevels, length_toList, card_univ] at this
    exact_mod_cast this
  have hsub : {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool) |
      ¬ KMAccurate f (θ ^ 2 / 4) ω} ⊆
      (⋃ J ∈ A, ⋃ S ∈ (univ : Finset (Finset ι)),
        {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|}) ∪
      ⋃ S ∈ (univ : Finset (Finset ι)),
        {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, KMAccurate, not_and_or, not_forall, not_lt] at hω
    rcases hω with ⟨J, hJ, S, hS⟩ | ⟨S, hS⟩
    · exact Or.inl (Set.mem_biUnion (List.mem_toFinset.2 hJ)
        (Set.mem_biUnion (mem_univ S) hS))
    · exact Or.inr (Set.mem_biUnion (mem_univ S) hS)
  have hpow : ((#(univ : Finset (Finset ι)) : ℕ) : ℝ) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset]
    push_cast
    rfl
  calc μ _ ≤ μ ((⋃ J ∈ A, ⋃ S ∈ (univ : Finset (Finset ι)),
          {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|}) ∪
        ⋃ S ∈ (univ : Finset (Finset ι)),
          {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|}) := μ.mono hsub
    _ ≤ ∑ J ∈ A, ∑ S ∈ (univ : Finset (Finset ι)),
          μ {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|} +
        ∑ S ∈ (univ : Finset (Finset ι)),
          μ {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} := by
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_)
        · refine (MeasureTheory.measure_biUnion_finset_le A _).trans (sum_le_sum fun J _ => ?_)
          exact MeasureTheory.measure_biUnion_finset_le _ _
        · exact MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _J ∈ A, ∑ _S ∈ (univ : Finset (Finset ι)), ENNReal.ofReal c +
        ∑ _S ∈ (univ : Finset (Finset ι)), ENNReal.ofReal c :=
        add_le_add (sum_le_sum fun J _ => sum_le_sum fun S _ => hbucket J S)
          (sum_le_sum fun S _ => hcoeff S)
    _ = ENNReal.ofReal (∑ _J ∈ A, ∑ _S ∈ (univ : Finset (Finset ι)), c +
          ∑ _S ∈ (univ : Finset (Finset ι)), c) := by
        rw [ENNReal.ofReal_add (sum_nonneg fun _ _ => sum_nonneg fun _ _ => hc0)
          (sum_nonneg fun _ _ => hc0),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => sum_nonneg fun _ _ => hc0,
          ENNReal.ofReal_sum_of_nonneg fun _ _ => hc0]
    _ ≤ ENNReal.ofReal (2 * (n + 2) * 2 ^ n * Real.exp (-(m * θ ^ 4) / 32)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [sum_const, nsmul_eq_mul, hpow]
        have h2n : (0 : ℝ) ≤ 2 ^ n * c := by positivity
        calc (#A : ℝ) * (2 ^ n * c) + 2 ^ n * c = (#A + 1) * (2 ^ n * c) := by ring
          _ ≤ (n + 1 + 1) * (2 ^ n * c) := by gcongr
          _ = 2 * (n + 2) * 2 ^ n * Real.exp (-(m * θ ^ 4) / 32) := by rw [hcdef]; ring

/-- **Enough samples are accurate**: for `n` coordinates, `θ > 0` and `δ > 0`, from
`m ≥ (32 / θ⁴) log (2 (n + 2) 2 ^ n / δ)` samples, the samples fail to be accurate at precision
`θ² / 4` with probability at most `δ`. -/
theorem uniform_not_accurate_le_of_log (f : (ι → Bool) → Bool) {θ δ : ℝ} (hθ : 0 < θ)
    (hδ : 0 < δ) {m : ℕ}
    (hm : 32 / θ ^ 4 * Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | ¬ KMAccurate f (θ ^ 2 / 4) ω} ≤ ENNReal.ofReal δ := by
  refine (uniform_not_accurate_le f θ m).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [show -(m * θ ^ 4) / 32 = -(θ ^ 4 / 32 * m) by ring]
  exact Real.mul_exp_neg_le_of_log le_rfl (by positivity) (by positivity) hδ
    (hm.trans_eq' (by ring))

/-- **Listing the large Fourier coefficients** by the bucket search of Goldreich and Levin
[GoldreichLevin1989], the query and sample step toward the Goldreich–Levin Theorem
[O'Donnell, Section 3.5][ODonnell2014]: for `n` coordinates and `τ > 0`, from
`m ≥ (32 / τ⁴) log (2 (n + 2) 2 ^ n / δ)` uniform samples, except with probability at most `δ`,
the query tree `kmCandidatesTree τ ω` run on the target `f` outputs every set `U` with
`|f̂(U)| ≥ τ`, only sets with `|f̂(U)| > τ / 2`, and at most `4 / τ²` sets. The tree makes at most
`m (2 n + 3)` non-adaptive membership queries (`depth_kmCandidatesTree_le`), polynomially many in
`n`, `1 / τ` and `log (1 / δ)`; these bounds are loose for the search alone (see **Cost** in the
module docstring). Only samples and queries are certified: the book's `poly(n, 1 / τ)` running
time is not, and the bucket search has no cap on the number of buckets, so it remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem uniform_not_kmCandidatesTree_heavy_le_of_log (f : (ι → Bool) → Bool) {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) {m : ℕ}
    (hm : 32 / τ ^ 4 * Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | ¬ ((∀ U, τ ≤ |fourierCoeff (fun x => signVal (f x)) U| →
            U ∈ (kmCandidatesTree τ ω).eval f) ∧
          (∀ U ∈ (kmCandidatesTree τ ω).eval f,
            τ / 2 < |fourierCoeff (fun x => signVal (f x)) U|) ∧
          τ ^ 2 / 4 * #((kmCandidatesTree τ ω).eval f) ≤ 1)} ≤ ENNReal.ofReal δ := by
  simp only [eval_kmCandidatesTree]
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans
    (uniform_not_accurate_le_of_log f hτ hδ hm)
  intro ω hω hacc
  refine hω ⟨fun U hU => mem_kmCandidates_of_sq_le_sq f hacc ?_, fun U hU => ?_,
    mul_card_kmCandidates_le_one f hacc⟩
  · rwa [sq_le_sq, abs_of_pos hτ]
  · have h := lt_sq_of_mem_kmCandidates f hacc hU
    rw [← abs_of_pos (half_pos hτ), ← sq_lt_sq, div_pow]
    linarith

/-- The confidence step of the learning theorems: if, for every `f ∈ C`, the threshold `θ` is
positive, `m ≥ (32 / θ⁴) log (2 (n + 2) 2 ^ n / δ)` and the hypothesis has error at most `ε` on
samples accurate at precision `θ² / 4`, then the algorithm learns `C` with error `ε` and
confidence `1 - δ`. The conditions are asked of the members of `C`, so that a caller may use
membership to bound its threshold. -/
private theorem kmLearner_learns_of_forall_accurate {C : ConceptClass (ι → Bool) Bool}
    {θ ε δ : ℝ} (hδ : 0 < δ) {m : ℕ}
    (h : ∀ f ∈ C, 0 < θ ∧
      32 / θ ^ 4 * Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m ∧
      ∀ ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool),
        KMAccurate f (θ ^ 2 / 4) ω → uniformError f (kmHypothesis f θ ω) ≤ ε) :
    (kmLearner ι m θ).Learns (PMF.uniformOfFintype _) C ε δ := by
  rw [QueryLearner.learns_iff]
  intro f hf
  obtain ⟨hθ, hm, herr⟩ := h f hf
  simp only [eval_kmLearner]
  -- an error above `ε` makes the samples inaccurate
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans
    (uniform_not_accurate_le_of_log f hθ hδ hm)
  intro ω hω hgood
  exact (not_le.2 hω) (herr ω hgood)

/-- **The query and sample step toward the Kushilevitz–Mansour theorem** [KushilevitzMansour1993],
[O'Donnell, Theorem 3.38][ODonnell2014]: for `n` coordinates, the Kushilevitz–Mansour algorithm
with threshold `ε / (2 L)` from `m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence
`m (2 n + 3)` membership queries (`kmLearner_queriesAtMost`), learns the Boolean functions whose
spectral norm, read as signs, is at most `L`, with error `ε` and confidence `1 - δ`. Only samples
and queries are certified: the book's running time `poly(n, L, 1 / ε)` is not, and the bucket
search has no cap on the number of buckets, so it remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns {L ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * L ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (spectralNormClass ι L) ε δ := by
  refine kmLearner_learns_of_forall_accurate hδ fun f hf => ?_
  have hL1 : 1 ≤ L := (one_le_sum_abs_fourierCoeff_signVal f).trans hf
  have hL : 0 < L := one_pos.trans_le hL1
  set θ := ε / (2 * L)
  have hθ : 0 < θ := by positivity
  refine ⟨hθ, hm.trans_eq' (by simp only [θ]; field_simp; ring), fun ω hgood => ?_⟩
  -- on accurate samples the error is at most `ε`
  rcases le_or_gt 1 ε with hε1 | hε1
  · exact (uniformError_le_one _ _).trans hε1
  have h := uniformError_kmHypothesis_le f hθ hf ω hgood
  have hθL : θ * L = ε / 2 := by simp only [θ]; field_simp
  have hθ2 : θ ^ 2 / 4 ≤ ε / 16 := by
    have : θ ^ 2 = ε ^ 2 / (4 * L ^ 2) := by simp only [θ]; ring
    rw [this, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_left hL1 hL.le]
  linarith

/-- **The query and sample step toward learning decision trees with membership queries**
[KushilevitzMansour1993], the decision-tree case of [O'Donnell, Theorem 3.38][ODonnell2014]: for
`n` coordinates, the Kushilevitz–Mansour algorithm with threshold `ε / (2 L)` from
`m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence `m (2 n + 3)` membership queries,
learns the functions computed by decision trees with at most `L` leaves, with error `ε` and
confidence `1 - δ`. Only samples and queries are certified; the book's running time
`poly(n, L, 1 / ε)` remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns_decisionTree {L : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * (L : ℝ) ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (decisionTreeClass ι L) ε δ := by
  refine (kmLearner_learns hε hδ hm).mono (fun f ⟨t, ht, hL⟩ => ?_) le_rfl le_rfl
  have hf : f = t.eval := (DecisionTree.computes_iff.1 ht).symm
  subst hf
  exact (DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount id t).trans
    (by exact_mod_cast hL)

/-- **The query and sample step toward the Kushilevitz–Mansour theorem, with the query count**:
under the hypotheses of `kmLearner_learns`, the algorithm learns the functions of spectral norm at
most `L` with `m (2 n + 3)` membership queries for `n` coordinates, the samples and queries of
[O'Donnell, Theorem 3.38][ODonnell2014]. Its running time remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns_and_queriesAtMost {L ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * L ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (spectralNormClass ι L) ε δ ∧
      (kmLearner ι m (ε / (2 * L))).QueriesAtMost (m * (2 * Fintype.card ι + 3)) :=
  ⟨kmLearner_learns hε hδ hm, kmLearner_queriesAtMost _⟩

/-- **The query and sample step toward learning decision trees with membership queries, with the
query count**: under the hypotheses of `kmLearner_learns_decisionTree`, the algorithm learns the
functions computed by decision trees with at most `L` leaves with `m (2 n + 3)` membership queries
for `n` coordinates, the samples and queries of the decision-tree case of
[O'Donnell, Theorem 3.38][ODonnell2014]. Its running time remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns_decisionTree_and_queriesAtMost {L : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * (L : ℝ) ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (decisionTreeClass ι L) ε δ ∧
      (kmLearner ι m (ε / (2 * L))).QueriesAtMost (m * (2 * Fintype.card ι + 3)) :=
  ⟨kmLearner_learns_decisionTree hε hδ hm, kmLearner_queriesAtMost _⟩

/-! ### Concentrated classes -/

variable (ι) in
/-- The Boolean functions whose Fourier spectrum, read as signs, is `η`-concentrated on some
collection of at most `M` sets: the weight off the collection is at most `η`
[O'Donnell, Definition 3.28][ODonnell2014]. -/
def concentratedClass (M : ℕ) (η : ℝ) : ConceptClass (ι → Bool) Bool :=
  {f | ∃ T : Finset (Finset ι), #T ≤ M ∧
    ∑ S ∈ Tᶜ, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ η}

/-- **Learning concentrated classes with membership queries** [KushilevitzMansour1993], the query
and sample step toward [O'Donnell, Theorem 3.37][ODonnell2014]: for `n` coordinates and `M ≥ 1`,
the Kushilevitz–Mansour algorithm with threshold `√(ε / (4 M))` from
`m ≥ (512 M² / ε²) log (2 (n + 2) 2 ^ n / δ)` samples, hence `m (2 n + 3)` membership queries
(`kmLearner_queriesAtMost`), learns, with error `ε` and confidence `1 - δ`, the Boolean functions
whose Fourier spectrum, read as signs, is `ε / 4`-concentrated on at most `M` sets. Only samples
and queries are certified: the book's running time `poly(M, n, 1 / ε)` is not, and the bucket
search has no cap on the number of buckets, so it remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns_concentrated {M : ℕ} (hM : 0 < M) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {m : ℕ} (hm : 512 * (M : ℝ) ^ 2 / ε ^ 2 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (Real.sqrt (ε / (4 * M)))).Learns (PMF.uniformOfFintype _)
      (concentratedClass ι M (ε / 4)) ε δ := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.2 hM
  set θ := Real.sqrt (ε / (4 * M))
  have hθ : 0 < θ := Real.sqrt_pos.2 (by positivity)
  have hθ2 : θ ^ 2 = ε / (4 * M) := Real.sq_sqrt (by positivity)
  have hm' : 32 / θ ^ 4 * Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m := by
    refine hm.trans_eq' ?_
    rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, hθ2]
    field_simp
    ring
  refine kmLearner_learns_of_forall_accurate hδ fun f hf => ⟨hθ, hm', fun ω hgood => ?_⟩
  -- on accurate samples the error is at most `ε`
  have h := uniformError_kmHypothesis_le_add f hθ ω hgood
  obtain ⟨T, hT, hη⟩ := hf
  have hlight : ∑ S with fourierCoeff (fun x => signVal (f x)) S ^ 2 < θ ^ 2,
      fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
        ∑ S ∈ Tᶜ, fourierCoeff (fun x => signVal (f x)) S ^ 2 + #T * θ ^ 2 :=
    sum_fourierCoeff_sq_le_sum_compl_add
      (fun S hS => (abs_lt_of_sq_lt_sq (mem_filter.1 hS).2 hθ.le).le) T
  have hTθ : (#T : ℝ) * θ ^ 2 ≤ M * θ ^ 2 := by gcongr
  have hMθ : (M : ℝ) * θ ^ 2 = ε / 4 := by rw [hθ2]; field_simp
  linarith [mul_le_mul_of_nonneg_right hM1 (sq_nonneg θ)]

/-- **Learning concentrated classes, with the query count**: under the hypotheses of
`kmLearner_learns_concentrated`, the algorithm learns the functions `ε / 4`-concentrated on at
most `M` sets with `m (2 n + 3)` membership queries for `n` coordinates: the query and sample step
toward [O'Donnell, Theorem 3.37][ODonnell2014]. Only samples and queries are certified; the book's
running time `poly(M, n, 1 / ε)` remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem kmLearner_learns_concentrated_and_queriesAtMost {M : ℕ} (hM : 0 < M) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ} (hm : 512 * (M : ℝ) ^ 2 / ε ^ 2 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (Real.sqrt (ε / (4 * M)))).Learns (PMF.uniformOfFintype _)
      (concentratedClass ι M (ε / 4)) ε δ ∧
      (kmLearner ι m (Real.sqrt (ε / (4 * M)))).QueriesAtMost (m * (2 * Fintype.card ι + 3)) :=
  ⟨kmLearner_learns_concentrated hM hε hδ hm, kmLearner_queriesAtMost _⟩

end Cslib.MachineLearning.UniformLearning
