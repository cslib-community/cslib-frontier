/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.MachineLearning.UniformLearning.LowDegree
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity
import Mathlib.Algebra.Order.Round

/-!
# Exact learning of low-degree functions

A Boolean function of degree at most `k ≥ 1`, read as signs, has Fourier coefficients in
`2 ^ (1 - k) ℤ` (`BitString.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree`).
So if every empirical coefficient on the sets of at most `k` coordinates is within `2 ^ (-k)` of the
true one, rounding it to the nearest multiple of `2 ^ (1 - k)` recovers the coefficient exactly,
the rounded expansion is the function itself, and its sign has error `0`
(`UniformLearning.exactLowDegreeHypothesis_eq`). By Hoeffding's inequality and a union bound over
the `N` sets of at most `k` coordinates
(`UniformLearning.uniform_exists_abs_empiricalCoeff_sub_ge_le`), `2 · 4 ^ k · log (2 N / δ)`
uniform random examples suffice (`UniformLearning.exactLowDegreeLearner_learns`). This is the
sample-complexity step toward [O'Donnell, Theorem 3.36][ODonnell2014], following the book's
Exercise 3.36. Since `N ≤ (n + 1) ^ k` (`BitString.card_filter_card_le_le_pow`), it is
`O(4 ^ k (k log (n + 1) + log (1 / δ)))` examples. The learner is noncomputable and its running
time is not certified, so Theorem 3.36 itself, learning in time `n ^ k · poly(n, 2 ^ k)` with a
circuit as output, remains open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).

## Usage

Open `Cslib.MachineLearning.UniformLearning` and `Cslib.MachineLearning.PACLearning`. For
`1 ≤ k`, `0 < δ` and a number of examples `m` with
`2 * 4 ^ k * Real.log (2 * #{S : Finset ι | #S ≤ k} / δ) ≤ m` (for instance its ceiling,
`Nat.le_ceil _`), `exactLowDegreeLearner_learns hk hδ hm` gives
`Learns (exactLowDegreeLearner ι k m) {f | (fun x => signVal (f x)) ∈ lowDegree ℝ ι k} 0 δ`.
A smaller class is learned through `Learns.mono`; the decision trees of depth at most `k` are one,
by `DecisionTree.comp_eval_mem_lowDegree` and `BitString.lowDegree_mono`. To reason about a fixed
sample, `exactLowDegreeHypothesis_eq` turns estimates within `2 ^ (-k)` into the function itself.
The union bound over the estimates, `uniform_exists_abs_empiricalCoeff_sub_ge_le`, is in
`CslibFrontier.MachineLearning.UniformLearning.LowDegree` and shared with the low-degree learner.
Checked clients bound the union bound for sixteen examples of a parity, recover the one-bit
dictator from two examples, and learn the functions of degree two on five bits, and so the
decision trees of depth two, with confidence `9 / 10`, in
[`CslibFrontierTests/BooleanAnalysisExactLearning.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisExactLearning.lean).

## Main definitions

* `Cslib.MachineLearning.UniformLearning.exactLowDegreeHypothesis`,
  `Cslib.MachineLearning.UniformLearning.exactLowDegreeLearner`: the low-degree algorithm with
  rounded coefficients.

## Main results

* `Cslib.MachineLearning.UniformLearning.exactLowDegreeHypothesis_eq`: estimates within `2 ^ (-k)`
  give back the function.
* `Cslib.MachineLearning.UniformLearning.exactLowDegreeLearner_learns`: the number of examples
  that suffices to learn the functions of degree at most `k` with error `0`, a step toward
  Theorem 3.36.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning

variable {ι : Type*} {m : ℕ}

/-- Rounding to the nearest multiple of `2 ^ (-j)` recovers such a multiple from any number within
`2 ^ (-(j + 1))` of it. -/
private theorem round_mul_two_pow_div_eq {j : ℕ} {c : ℝ} {z : ℤ}
    (h : |c - z / 2 ^ j| < 1 / 2 ^ (j + 1)) : (round (c * 2 ^ j) : ℝ) / 2 ^ j = z / 2 ^ j := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h' : |c * 2 ^ j - z| < 1 / 2 := by
    have : c * 2 ^ j - z = (c - z / 2 ^ j) * 2 ^ j := by field_simp
    rw [this, abs_mul, abs_of_pos hpos]
    calc _ < 1 / 2 ^ (j + 1) * 2 ^ j := mul_lt_mul_of_pos_right h hpos
      _ = 1 / 2 := by rw [pow_succ]; field_simp
  rw [(round_eq_iff (n := z)).2
    ⟨by linarith [(abs_lt.1 h').1], by linarith [(abs_lt.1 h').2]⟩]

variable [Fintype ι] [DecidableEq ι]

/-- The hypothesis of the exact low-degree algorithm of degree `k`: the sign of the expansion
`∑_{#S ≤ k} c̃(S) χ_S` truncated at degree `k`, with each empirical coefficient `c̃(S)` rounded to
the nearest multiple of `2 ^ (1 - k)` (of `1` when `k = 0`). -/
noncomputable def exactLowDegreeHypothesis (k : ℕ) (e : LabeledSample (ι → Bool) Bool m) :
    (ι → Bool) → Bool :=
  signRound fun x => ∑ S with #S ≤ k,
    (round (empiricalCoeff e S * 2 ^ (k - 1)) / 2 ^ (k - 1) : ℝ) * chi ℝ S x

variable (ι) in
/-- **The exact low-degree algorithm** of degree `k` from `m` examples: estimate the Fourier
coefficients on the sets of at most `k` coordinates empirically, round them to the nearest
multiples of `2 ^ (1 - k)` (of `1` when `k = 0`), and output the sign of the truncated expansion.
It is a deterministic learner. -/
noncomputable def exactLowDegreeLearner (k m : ℕ) : Learner (ι → Bool) Bool m :=
  exactLowDegreeHypothesis k

/-- If every empirical coefficient on the sets of at most `k ≥ 1` coordinates is within `2 ^ (-k)`
of the true coefficient of a function of degree at most `k`, the exact low-degree hypothesis is the
function itself. -/
theorem exactLowDegreeHypothesis_eq {k : ℕ} (hk : 1 ≤ k) {f : (ι → Bool) → Bool}
    (hf : (fun x => signVal (f x)) ∈ lowDegree ℝ ι k) {e : LabeledSample (ι → Bool) Bool m}
    (he : ∀ S : Finset ι, #S ≤ k →
      |empiricalCoeff e S - fourierCoeff (fun x => signVal (f x)) S| < 1 / 2 ^ k) :
    exactLowDegreeHypothesis k e = f := by
  have hround (S : Finset ι) (hS : #S ≤ k) :
      (round (empiricalCoeff e S * 2 ^ (k - 1)) / 2 ^ (k - 1) : ℝ) =
        fourierCoeff (fun x => signVal (f x)) S := by
    obtain ⟨z, hz⟩ := exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree f hf S
    exact hz ▸ round_mul_two_pow_div_eq (by simpa only [hz, Nat.sub_add_cancel hk] using he S hS)
  have hhigh := mem_lowDegree_iff_fourierCoeff_eq_zero.1 hf
  funext x
  have hsum : ∑ S with #S ≤ k,
      (round (empiricalCoeff e S * 2 ^ (k - 1)) / 2 ^ (k - 1) : ℝ) * chi ℝ S x =
        signVal (f x) := by
    rw [← sum_fourierCoeff_mul_chi (fun x => signVal (f x)) x,
      ← sum_filter_add_sum_filter_not univ fun S => #S ≤ k]
    rw [sum_eq_zero (s := univ.filter fun S => ¬#S ≤ k) fun S hS => by
      rw [hhigh S (not_le.1 (mem_filter.1 hS).2), zero_mul], add_zero]
    exact sum_congr rfl fun S hS => by rw [hround S (mem_filter.1 hS).2]
  rw [exactLowDegreeHypothesis, signRound_apply, hsum]
  cases f x <;> norm_num

/-- **Sample complexity of exact learning of low-degree functions**, a step toward
[O'Donnell, Theorem 3.36][ODonnell2014], following Exercise 3.36: let `N` be the number of sets of
at most `k ≥ 1` coordinates (at most `(n + 1) ^ k` for `n = Fintype.card ι`,
`BitString.card_filter_card_le_le_pow`). From `m ≥ 2 · 4 ^ k · log (2 N / δ)` uniform random
examples, the exact low-degree algorithm of degree `k` learns the Boolean functions of degree at
most `k`, read as signs, with error `0` and confidence `1 - δ`. Only the number of examples is
certified: the learner is noncomputable, and the book's running time `n ^ k · poly(n, 2 ^ k)` and
circuit output remain open on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). -/
theorem exactLowDegreeLearner_learns {k m : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hm : 2 * 4 ^ k * Real.log (2 * #{S : Finset ι | #S ≤ k} / δ) ≤ m) :
    Learns (exactLowDegreeLearner ι k m) {f | (fun x => signVal (f x)) ∈ lowDegree ℝ ι k} 0 δ := by
  rw [learns_iff]
  intro f hf
  set T : Finset (Finset ι) := {S : Finset ι | #S ≤ k}
  set N : ℝ := (#T : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 (card_filter_card_le_pos k)
  set γ : ℝ := 1 / 2 ^ k
  have hγ : 0 ≤ γ := by positivity
  have hγsq : γ ^ 2 = 1 / 4 ^ k := by
    rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  -- if every estimate is within `γ`, the hypothesis is `f`
  have hsub : {x : Fin m → ι → Bool | 0 < uniformError f (exactLowDegreeLearner ι k m
      (examples f x))} ⊆
        {x | ∃ S ∈ T, γ ≤ |empiricalCoeff (examples f x) S -
          fourierCoeff (fun x => signVal (f x)) S|} := by
    intro x hx
    by_contra hgood
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hgood
    simp [Set.mem_ofPred_eq, exactLowDegreeLearner, uniformError_self,
      exactLowDegreeHypothesis_eq hk hf fun S hS => hgood S (mem_filter.2 ⟨mem_univ S, hS⟩)] at hx
  refine (MeasureTheory.measure_mono hsub).trans
    ((uniform_exists_abs_empiricalCoeff_sub_ge_le f T hγ).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hγsq, show N * (2 * Real.exp (-(m * (1 / 4 ^ k)) / 2)) =
      2 * N * Real.exp (-(1 / (2 * 4 ^ k) * m)) by ring_nf]
  exact Real.mul_exp_neg_le_of_log le_rfl (by positivity) (by positivity) hδ
    (by rw [div_div_eq_mul_div, div_one]; linarith)

end Cslib.MachineLearning.UniformLearning
