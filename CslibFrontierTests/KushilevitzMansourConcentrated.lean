/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.UniformLearning.KushilevitzMansour
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.BooleanAnalysis.SpectralConcentration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for learning concentrated classes with membership queries

A parity has all its weight on its own set, so it is concentrated on one set, while it is not
`η`-concentrated on the empty collection for `η < 1`. Against the collection of its own set, its
coefficients weigh at most `0 + 1 · 1²`, and they weigh exactly `1`, so the bound is attained. On
samples accurate at precision `1 / 4` the Kushilevitz–Mansour hypothesis with threshold `1` has
error at most `1 / 4`. The sample bound `(32 / θ⁴) log (2 (n + 2) 2 ^ n / δ)` is instantiated on
two bits. The Kushilevitz–Mansour algorithm learns the parities as functions
`ε / 4`-concentrated on at most one set; on two bits, with `ε = δ = 1 / 2`, it learns the
functions `1 / 8`-concentrated on at most three sets from `⌈18432 log 64⌉` samples and `7`
queries per sample.

For Proposition 3.40, the empirical bucket weight of the parity of the first of two bits on `{0}`
with respect to `∅`, whose bucket weight is `0`, is at least `γ` in absolute value with
probability at most `2 exp (-m γ² / 2)`; and `⌈8 log 4⌉` samples estimate its bucket weight on
`{0}` with respect to `{0}`, which is `1`, within `1 / 2` except with probability `1 / 2`. The
step from a tail bound to a sample size gives `2 exp (-log 4) ≤ 1 / 2`.

For the query and sample step toward the Goldreich–Levin Theorem, with no samples the found sets
of a parity and of a constant agree, since nothing is queried; with threshold `1`, on samples
accurate at precision `1 / 4` at most four sets are found, and for a parity exactly its own set
is found, also by the query tree, which on two bits makes at most `7 m` queries; on two bits
`⌈32 log 64⌉` samples make the query tree output exactly that set except with probability
`1 / 2`. -/

public section

namespace CslibFrontierTests.KushilevitzMansourConcentrated

open Cslib Cslib.MachineLearning Cslib.MachineLearning.UniformLearning Cslib.BitString
open Cslib.Probability Finset

/-- A parity is concentrated on its own set. -/
theorem parityOn_mem_concentratedClass {n : ℕ} (S : Finset (Fin n)) {η : ℝ} (hη : 0 ≤ η) :
    parityOn S ∈ concentratedClass (Fin n) 1 η := by
  refine ⟨{S}, by simp, le_of_eq_of_le (sum_eq_zero fun U hU => ?_) hη⟩
  rw [fourierCoeff_signVal_parityOn, ite_eq_right (by simpa using hU)]
  norm_num

/-- A parity is not `η`-concentrated on the empty collection for `η < 1`: its weight is `1`. -/
theorem parityOn_not_mem_concentratedClass_zero {n : ℕ} (S : Finset (Fin n)) {η : ℝ}
    (hη : η < 1) : parityOn S ∉ concentratedClass (Fin n) 0 η := by
  rintro ⟨F, hF, hsum⟩
  rw [card_eq_zero.1 (Nat.le_zero.1 hF), compl_empty] at hsum
  simp only [fourierCoeff_signVal_parityOn, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sum_ite_eq', mem_univ, ite_true] at hsum
  linarith

/-- Against the collection `{{0}}`, the coefficients of the parity of the first of two bits, all
of absolute value at most `1`, weigh at most `0 + 1 · 1²`
(`sum_fourierCoeff_sq_parityOn_eq_one` shows that the bound is attained). -/
theorem sum_fourierCoeff_sq_parityOn_le :
    ∑ S, fourierCoeff (fun x => signVal (parityOn ({0} : Finset (Fin 2)) x)) S ^ 2 ≤ 1 := by
  have h := sum_fourierCoeff_sq_le_sum_compl_add (T := univ) (θ := 1)
    (f := fun x => signVal (parityOn ({0} : Finset (Fin 2)) x))
    (fun S _ => by rw [fourierCoeff_signVal_parityOn]; split_ifs <;> norm_num) {{0}}
  have hz : ∑ S ∈ ({{0}} : Finset (Finset (Fin 2)))ᶜ,
      fourierCoeff (fun x => signVal (parityOn ({0} : Finset (Fin 2)) x)) S ^ 2 = 0 :=
    sum_eq_zero fun S hS => by
      have hS0 : S ≠ {0} := by simpa using hS
      rw [fourierCoeff_signVal_parityOn]
      simp [hS0]
  rw [hz] at h
  norm_num at h
  exact h

/-- The coefficients of the parity of the first of two bits weigh exactly `1`, as for every
Boolean function, so the bound `0 + 1 · 1²` of `sum_fourierCoeff_sq_parityOn_le` is attained. -/
theorem sum_fourierCoeff_sq_parityOn_eq_one :
    ∑ S, fourierCoeff (fun x => signVal (parityOn ({0} : Finset (Fin 2)) x)) S ^ 2 = 1 :=
  sum_fourierCoeff_sq_signVal _

/-- On samples accurate at precision `1 / 4`, the hypothesis with threshold `1` errs on at most a
quarter of the inputs for a parity: no coefficient of a parity lies strictly between `0` and
`1`. -/
theorem uniformError_kmHypothesis_parityOn_le {n m : ℕ} (U : Finset (Fin n))
    (ω : Fin m → (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    (hω : KMAccurate (parityOn U) (1 ^ 2 / 4) ω) :
    uniformError (parityOn U) (kmHypothesis (parityOn U) 1 ω) ≤ 1 / 4 := by
  have h := uniformError_kmHypothesis_le_add (parityOn U) one_pos ω hω
  have hz : ∑ S with fourierCoeff (fun x => signVal (parityOn U x)) S ^ 2 < 1 ^ 2,
      fourierCoeff (fun x => signVal (parityOn U x)) S ^ 2 = 0 :=
    sum_eq_zero fun S hS => by
      have hlt := (mem_filter.1 hS).2
      rw [fourierCoeff_signVal_parityOn] at hlt ⊢
      split_ifs at hlt ⊢
      · norm_num at hlt
      · norm_num
  rw [hz] at h
  norm_num at h
  exact h

/-- On two bits, `⌈32 log 64⌉` samples are accurate at precision `1 / 4` except with probability
`1 / 2`. -/
theorem uniform_not_accurate_fin_two_le (f : (Fin 2 → Bool) → Bool) :
    (PMF.uniformOfFintype (Fin ⌈32 * Real.log 64⌉₊ →
        (Fin 2 → Bool) × (Fin 2 → Bool) × (Fin 2 → Bool))).toOuterMeasure
      {ω | ¬ KMAccurate f (1 ^ 2 / 4) ω} ≤ ENNReal.ofReal (1 / 2) :=
  uniform_not_accurate_le_of_log f one_pos (by norm_num)
    ((le_of_eq (by norm_num)).trans (Nat.le_ceil _))

/-- The parities are learned with membership queries, as functions concentrated on one set. -/
theorem kmLearner_learns_parityOn {n m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : 512 / ε ^ 2 * Real.log (2 * (n + 2) * 2 ^ n / δ) ≤ m) :
    (kmLearner (Fin n) m (Real.sqrt (ε / 4))).Learns (PMF.uniformOfFintype _)
      (Set.range parityOn) ε δ := by
  have h := kmLearner_learns_concentrated (ι := Fin n) (M := 1) one_pos hε hδ (by simpa using hm)
  simp only [Nat.cast_one, mul_one] at h
  exact h.mono (by rintro _ ⟨S, rfl⟩; exact parityOn_mem_concentratedClass S (by positivity))
    le_rfl le_rfl

/-- The query and sample step toward Theorem 3.37 on two bits, with `ε = δ = 1 / 2` and `M = 3`:
`⌈18432 log 64⌉` samples, hence `7` queries per sample, learn the functions `1 / 8`-concentrated
on at most three sets. -/
theorem kmLearner_learns_concentrated_fin_two :
    (kmLearner (Fin 2) ⌈18432 * Real.log 64⌉₊ (Real.sqrt (1 / 2 / (4 * 3)))).Learns
        (PMF.uniformOfFintype _) (concentratedClass (Fin 2) 3 (1 / 2 / 4)) (1 / 2) (1 / 2) ∧
      (kmLearner (Fin 2) ⌈18432 * Real.log 64⌉₊ (Real.sqrt (1 / 2 / (4 * 3)))).QueriesAtMost
        (⌈18432 * Real.log 64⌉₊ * 7) := by
  simpa using kmLearner_learns_concentrated_and_queriesAtMost (ι := Fin 2) (M := 3)
    (by norm_num) (ε := 1 / 2) (δ := 1 / 2) (by norm_num) (by norm_num)
    ((le_of_eq (by norm_num)).trans (Nat.le_ceil _))

/-- A bucket weight that vanishes, since `{0} ⊈ ∅`, is estimated near `0`. -/
theorem uniform_abs_bucketEstimate_parityOn_empty_ge_le (m : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → (Fin 2 → Bool) × (Fin 2 → Bool) × (Fin 2 → Bool))).toOuterMeasure
      {ω | γ ≤ |bucketEstimate (parityOn ({0} : Finset (Fin 2))) ω ∅ {0}|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  have hW : bucketWeight (fun x => signVal (parityOn ({0} : Finset (Fin 2)) x)) ∅ {0} = 0 := by
    simp [bucketWeight, (Finset.singleton_nonempty (0 : Fin 2)).ne_empty.symm]
  have h := uniform_abs_bucketEstimate_sub_ge_le (m := m) (parityOn ({0} : Finset (Fin 2))) ∅ {0} hγ
  simpa only [hW, sub_zero] using h

/-- The sample bound of Proposition 3.40 on two bits: `⌈8 log 4⌉` samples estimate the bucket
weight `1` of the parity of the first bit on `{0}` with respect to `{0}` within `1 / 2` with
confidence `1 / 2`. -/
theorem uniform_abs_bucketEstimate_parityOn_ge_le :
    (PMF.uniformOfFintype (Fin ⌈8 * Real.log 4⌉₊ →
        (Fin 2 → Bool) × (Fin 2 → Bool) × (Fin 2 → Bool))).toOuterMeasure
      {ω | 1 / 2 ≤ |bucketEstimate (parityOn ({0} : Finset (Fin 2))) ω {0} {0} - 1|} ≤
        ENNReal.ofReal (1 / 2) := by
  have hW : bucketWeight (fun x => signVal (parityOn ({0} : Finset (Fin 2)) x)) {0} {0} = 1 := by
    rw [bucketWeight, sum_eq_single_of_mem {0} (by simp) fun U _ hU => by
      rw [fourierCoeff_signVal_parityOn]; simp [hU]]
    rw [fourierCoeff_signVal_parityOn]
    simp
  have h := uniform_abs_bucketEstimate_sub_ge_le_of_log (m := ⌈8 * Real.log 4⌉₊)
    (parityOn ({0} : Finset (Fin 2))) {0} {0} (γ := 1 / 2) (δ := 1 / 2) (by norm_num) (by norm_num)
    ((le_of_eq (by norm_num)).trans (Nat.le_ceil _))
  rwa [hW] at h

/-- A tail bound `2 exp (-(1 · log 4))` is at most `1 / 2`, by the sample-size step with
`c = K = 2`, `a = 1` and `δ = 1 / 2`. -/
theorem two_mul_exp_neg_log_four_le : 2 * Real.exp (-(1 * Real.log 4)) ≤ 1 / 2 :=
  Real.mul_exp_neg_le_of_log le_rfl two_pos one_pos (by norm_num) (by norm_num)

/-- With no samples nothing is queried, so the found sets do not depend on the target: the sets
found for a parity and for the constant `false` function agree. -/
theorem kmCandidates_parityOn_fin_zero {n : ℕ} (U : Finset (Fin n)) (θ : ℝ)
    (ω : Fin 0 → (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) :
    kmCandidates (parityOn U) θ ω = kmCandidates (fun _ => false) θ ω := by
  refine kmCandidates_congr θ ω fun x hx => ?_
  have h := length_kmQueries ω
  rw [zero_mul, List.length_eq_zero_iff] at h
  simp [h] at hx

/-- With threshold `1`, on samples accurate at precision `1 / 4`, at most four sets are found. -/
theorem card_kmCandidates_le_four {n m : ℕ} (f : (Fin n → Bool) → Bool)
    (ω : Fin m → (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    (hω : KMAccurate f (1 ^ 2 / 4) ω) : #(kmCandidates f 1 ω) ≤ 4 := by
  have h := mul_card_kmCandidates_le_one f hω
  have h' : (#(kmCandidates f 1 ω) : ℝ) ≤ 4 := by linarith
  exact_mod_cast h'

/-- A list of sets that contains the set of a parity, and only sets where the parity has a
nonzero coefficient, is that set alone. -/
theorem eq_singleton_of_fourierCoeff_parityOn_ne_zero {n : ℕ} (U : Finset (Fin n))
    {L : Finset (Finset (Fin n))} (hU : U ∈ L)
    (hL : ∀ V ∈ L, fourierCoeff (fun x => signVal (parityOn U x)) V ≠ 0) : L = {U} := by
  refine eq_singleton_iff_unique_mem.2 ⟨hU, fun V hV => ?_⟩
  by_contra hVU
  exact hL V hV (by simp [fourierCoeff_signVal_parityOn, hVU])

/-- With threshold `1`, on samples accurate at precision `1 / 4`, the only set found for a parity
is its own set. -/
theorem kmCandidates_parityOn_eq {n m : ℕ} (U : Finset (Fin n))
    (ω : Fin m → (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    (hω : KMAccurate (parityOn U) (1 ^ 2 / 4) ω) : kmCandidates (parityOn U) 1 ω = {U} := by
  refine eq_singleton_of_fourierCoeff_parityOn_ne_zero U
    (mem_kmCandidates_of_sq_le_sq _ hω (by simp [fourierCoeff_signVal_parityOn]))
    fun V hV h => ?_
  have h' := lt_sq_of_mem_kmCandidates _ hω hV
  rw [h] at h'
  norm_num at h'

/-- With threshold `1`, on samples accurate at precision `1 / 4`, the query tree run on a parity
outputs its own set. -/
theorem eval_kmCandidatesTree_parityOn_eq {n m : ℕ} (U : Finset (Fin n))
    (ω : Fin m → (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    (hω : KMAccurate (parityOn U) (1 ^ 2 / 4) ω) :
    (kmCandidatesTree 1 ω).eval (parityOn U) = {U} := by
  rw [eval_kmCandidatesTree, kmCandidates_parityOn_eq U ω hω]

/-- On two bits, the query tree makes at most `7 m` queries. -/
theorem depth_kmCandidatesTree_fin_two_le {m : ℕ} (θ : ℝ)
    (ω : Fin m → (Fin 2 → Bool) × (Fin 2 → Bool) × (Fin 2 → Bool)) :
    (kmCandidatesTree θ ω).depth ≤ 7 * m := by
  have h := depth_kmCandidatesTree_le θ ω
  simp only [Fintype.card_fin] at h
  omega

/-- The query and sample step toward the Goldreich–Levin Theorem for a parity on two bits:
`⌈32 log 64⌉` samples find exactly its own set, as the output of the query tree, except with
probability `1 / 2`. -/
theorem uniform_eval_kmCandidatesTree_parityOn_ne_le (U : Finset (Fin 2)) :
    (PMF.uniformOfFintype (Fin ⌈32 * Real.log 64⌉₊ →
        (Fin 2 → Bool) × (Fin 2 → Bool) × (Fin 2 → Bool))).toOuterMeasure
      {ω | (kmCandidatesTree 1 ω).eval (parityOn U) ≠ {U}} ≤ ENNReal.ofReal (1 / 2) := by
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans
    (uniform_not_kmCandidatesTree_heavy_le_of_log (parityOn U) one_pos
      (by norm_num : (0 : ℝ) < 1 / 2)
      ((le_of_eq (by norm_num)).trans (Nat.le_ceil _)))
  rintro ω hω ⟨hmem, hlt, _⟩
  refine hω (eq_singleton_of_fourierCoeff_parityOn_ne_zero U
    (hmem U (by simp [fourierCoeff_signVal_parityOn])) fun V hV h => ?_)
  have h' := hlt V hV
  rw [h] at h'
  norm_num at h'

end CslibFrontierTests.KushilevitzMansourConcentrated
