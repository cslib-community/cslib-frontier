/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
public import CslibFrontier.Probability.Minimax
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact

/-!
# Blackwell's approachability theorem

Formalizes **Blackwell's approachability theorem** [Blackwell1956] for vector-valued repeated
games with finite action sets `I, J` and payoff matrix `m : I → J → E` into a real inner product
space `E`, targeting a nonempty complete convex set `S : Set E`.

In the classic characterization (`satisfiesResponseCondition_iff_halfspace`), the following two
conditions on `(m, S)` are equivalent (without assuming finite dimensionality or completeness of
`E`):

* **Response condition** (`SatisfiesResponseCondition m S`): for every mixed adversary strategy
  `q ∈ Δ(J)`, there exists a mixed learner strategy `p ∈ Δ(I)` such that the bilinear expected
  payoff `∑ i, ∑ j, (p i * q j) • m i j` lies in `S`.
* **Halfspace condition** (`SatisfiesHalfspaceCondition m S`): every closed halfspace
  `{x | ⟪w, x⟫ ≤ c}` containing `S` is forceable, i.e., there exists `p ∈ Δ(I)` such that
  `⟪w, ∑ i, p i • m i j⟫ ≤ c` for every pure action `j : J`.

The forward direction applies von Neumann's minimax theorem
(`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`) to the scalar game
`M i j = ⟪w, m i j⟫`; the converse derives the separating hyperplane `w = c* - Π_S(c*)` from the
nearest-pair variational inequality using `Cslib.metricProjection` on compact convex
`{m(p, q) | p ∈ Δ(I)}`.

We establish both quantitative directions of approachability:

* **Deterministic (expected-payoff) and cone bounds** (`blackwell_dist_sq_le_sum`,
  `blackwell_dist_le_div_sqrt`, `blackwell_cone_dist_le`): a single round-by-round potential
  recursion bounds the distance of the running average `vecAvg v T` to `S`. For an arbitrary
  nonempty complete convex `S` containing `s₀` with `‖v t - s₀‖ ≤ R`, the rate is `2 * R / √T`
  (works even for unbounded `S`, such as the nonpositive orthant). When `S` is a convex cone,
  Moreau scaling removes the reference offset and improves the rate to `R / √T`.
* **Randomized pure-action play against adaptive adversaries** (`ApproachStrategy`,
  `expectHistory`, `blackwell_expect_dist_sq_le`, `blackwell_expect_dist_le`,
  `blackwell_prob_dist_ge_le`): against *any* adaptive adversary `adv : List I → J` observing the
  learner's realized pure actions `h : List I` (stored most-recent-first), an explicit Blackwell
  strategy achieves `𝔼[dist(x̄_T, S) ^ 2] ≤ 4 * R ^ 2 / T`, `𝔼[dist(x̄_T, S)] ≤ 2 * R / √T`, and the
  Markov tail `Pr[dist(x̄_T, S) ≥ ε] ≤ 4 * R ^ 2 / (T * ε ^ 2)`.
* **Necessity (non-approachability)** (`exists_nonapproachable_dist_ge`): if
  `¬ SatisfiesResponseCondition m S`, some stationary mixed adversary `q ∈ Δ(J)` forces
  `dist(vecAvg_T, S) ≥ δ > 0` uniformly across *all* horizons `T ≥ 1` and *all* learner sequences
  `p : ℕ → I → ℝ` in `Δ(I)`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Blackwell.vecAvg`: running average
  `(T : ℝ)⁻¹ • ∑ t < T, v t`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.distToSet`: Euclidean distance
  `‖x - metricProjection S x‖` to a complete convex set `S`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.expectedPayoff`: bilinear payoff
  `∑ i, p i • m i j`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.SatisfiesResponseCondition`: mixed response
  condition (`∀ q ∈ Δ(J), ∃ p ∈ Δ(I), m(p, q) ∈ S`).
* `Cslib.MachineLearning.OnlineLearning.Blackwell.SatisfiesHalfspaceCondition`: every closed
  halfspace containing `S` is forceable by some `p ∈ Δ(I)`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.ApproachStrategy`: randomized adaptive-history
  learner outputting a distribution on `I`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.FeedbackRule`: stationary adversary-independent
  rule selecting mixed weights from the current average payoff `y : E`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.expectHistory`: exact `T`-round expectation over
  realized action histories of length `T`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.sumPayoff`: realized cumulative vector payoff
  along a reverse-ordered history `h : List I`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Blackwell.satisfiesResponseCondition_iff_halfspace`:
  equivalence of the response and halfspace conditions for complete convex sets.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_dist_sq_le_sum`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_dist_le_div_sqrt`: deterministic
  Euclidean potential and `2 * R / √T` rate.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_cone_dist_le`: tight `R / √T` rate
  for complete convex cones.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_expect_dist_sq_le`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_expect_dist_le`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.blackwell_prob_dist_ge_le`: adaptive randomized
  approachability (squared, `L¹`, and Markov probability bounds).
* `Cslib.MachineLearning.OnlineLearning.Blackwell.exists_approachStrategy_of_response`:
  existence of a Blackwell-approachable randomized strategy under `SatisfiesResponseCondition`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.exists_nonapproachable_dist_ge`:
  necessity converse when `SatisfiesResponseCondition` fails.

## References

* [D. Blackwell, *An analog of the minimax theorem for vector payoffs*][Blackwell1956]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.Blackwell

section Potential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Running average `(T : ℝ)⁻¹ • ∑ t ∈ range T, v t` of a vector sequence over `T` rounds. -/
@[expose] noncomputable def vecAvg (v : ℕ → E) (T : ℕ) : E :=
  ((T : ℝ)⁻¹) • ∑ t ∈ range T, v t

@[simp] theorem vecAvg_zero (v : ℕ → E) : vecAvg v 0 = 0 := by
  simp [vecAvg]

theorem smul_vecAvg (v : ℕ → E) {T : ℕ} (hT : 0 < T) :
    (T : ℝ) • vecAvg v T = ∑ t ∈ range T, v t := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [vecAvg, smul_smul, mul_inv_cancel₀ hTne, one_smul]

/-- Distance `‖x - metricProjection S x‖` from `x` to a nonempty complete convex set `S`. -/
@[expose] noncomputable def distToSet (S : Set E) (x : E) : ℝ :=
  ‖x - metricProjection S x‖

omit [InnerProductSpace ℝ E] in
theorem distToSet_nonneg (S : Set E) (x : E) : 0 ≤ distToSet S x :=
  norm_nonneg _

theorem distToSet_le_norm_sub {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s : E} (hs : s ∈ S) (x : E) :
    distToSet S x ≤ ‖x - s‖ := by
  have hne : S.Nonempty := ⟨s, hs⟩
  rw [distToSet, norm_sub_metricProjection hne hc hS x]
  have hbd : BddBelow (Set.range fun w : S => ‖x - (w : E)‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  exact ciInf_le hbd ⟨s, hs⟩

theorem distToSet_eq_zero_of_mem {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {x : E} (hx : x ∈ S) : distToSet S x = 0 :=
  le_antisymm ((distToSet_le_norm_sub hc hS hx x).trans_eq (by simp)) (distToSet_nonneg S x)

theorem distToSet_pos_of_not_mem {S : Set E} (hne : S.Nonempty) (hc : IsComplete S)
    (hS : Convex ℝ S) {x : E} (hx : x ∉ S) : 0 < distToSet S x := by
  refine lt_of_le_of_ne (distToSet_nonneg S x) (Ne.symm fun h => ?_)
  have h0 : x - metricProjection S x = 0 := norm_eq_zero.mp h
  have heq : x = metricProjection S x := sub_eq_zero.mp h0
  exact hx (heq ▸ metricProjection_mem hne hc hS x)

/-- Nearest-point distance in an inner product space scales positively with the target, for
`t • vecAvg` comparisons. -/
private theorem sum_sub_smul_metricProjection_le {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s : E} (hs : s ∈ S) (X : E) {n : ℕ} (hn : 0 < n) :
    ‖X - (n : ℝ) • metricProjection S ((n : ℝ)⁻¹ • X)‖ ≤ ‖X - (n : ℝ) • s‖ := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : ‖(n : ℝ)⁻¹ • X - metricProjection S ((n : ℝ)⁻¹ • X)‖ ≤
      ‖(n : ℝ)⁻¹ • X - s‖ := distToSet_le_norm_sub hc hS hs _
  have hscale := mul_le_mul_of_nonneg_left h1 hn'.le
  have hL : (n : ℝ) * ‖(n : ℝ)⁻¹ • X - metricProjection S ((n : ℝ)⁻¹ • X)‖ =
      ‖X - (n : ℝ) • metricProjection S ((n : ℝ)⁻¹ • X)‖ := by
    have heq : (n : ℝ) • ((n : ℝ)⁻¹ • X - metricProjection S ((n : ℝ)⁻¹ • X)) =
        X - (n : ℝ) • metricProjection S ((n : ℝ)⁻¹ • X) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hn'.ne', one_smul]
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hn']
  have hR : (n : ℝ) * ‖(n : ℝ)⁻¹ • X - s‖ = ‖X - (n : ℝ) • s‖ := by
    have heq : (n : ℝ) • ((n : ℝ)⁻¹ • X - s) = X - (n : ℝ) • s := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hn'.ne', one_smul]
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hn']
  rwa [hL, hR] at hscale

/-- **Core quadratic Blackwell recursion**: if each vector `v t` (`1 ≤ t < T`) satisfies the
supporting-halfspace condition `⟪vecAvg v t - s_t, v t - s_t⟫ ≤ 0` where
`s_t = metricProjection S (vecAvg v t)`, then for any initial reference `s₀ ∈ S`,
`T ^ 2 * distToSet S (vecAvg v T) ^ 2 ≤ ∑ t < T, ‖v t - s_t‖ ^ 2`. -/
theorem blackwell_dist_sq_le_sum {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s₀ : E} (hs₀ : s₀ ∈ S) (v : ℕ → E) (T : ℕ)
    (hstep : ∀ t, 0 < t → t < T →
      let s := metricProjection S (vecAvg v t)
      ⟪vecAvg v t - s, v t - s⟫ ≤ 0) :
    ‖(∑ t ∈ range T, v t) - (T : ℝ) • metricProjection S (vecAvg v T)‖ ^ 2 ≤
      ∑ t ∈ range T,
        ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero =>
      simp only [zero_add, range_one, sum_singleton, Nat.cast_one, one_smul, ↓reduceIte]
      have h1 : ‖v 0 - metricProjection S (vecAvg v 1)‖ ≤ ‖v 0 - s₀‖ := by
        simpa [vecAvg, distToSet] using distToSet_le_norm_sub hc hS hs₀ (v 0)
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    | succ m =>
      set k := m + 1
      have hkpos : 0 < k := Nat.succ_pos m
      have hkr : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
      have hk1pos : 0 < k + 1 := Nat.succ_pos k
      have hih := ih fun t ht1 ht2 => hstep t ht1 (lt_trans ht2 (Nat.lt_succ_self k))
      set sk := metricProjection S (vecAvg v k)
      have hsk_mem : sk ∈ S := metricProjection_mem ⟨s₀, hs₀⟩ hc hS _
      have hmin :
          ‖(∑ t ∈ range (k + 1), v t) -
              ((k + 1 : ℕ) : ℝ) • metricProjection S (vecAvg v (k + 1))‖ ≤
            ‖(∑ t ∈ range (k + 1), v t) - ((k + 1 : ℕ) : ℝ) • sk‖ :=
        sum_sub_smul_metricProjection_le hc hS hsk_mem _ hk1pos
      have hmin_sq :
          ‖(∑ t ∈ range (k + 1), v t) -
              ((k + 1 : ℕ) : ℝ) • metricProjection S (vecAvg v (k + 1))‖ ^ 2 ≤
            ‖(∑ t ∈ range (k + 1), v t) - ((k + 1 : ℕ) : ℝ) • sk‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmin 2
      have hdecomp :
          (∑ t ∈ range (k + 1), v t) - ((k + 1 : ℕ) : ℝ) • sk =
            ((∑ t ∈ range k, v t) - (k : ℝ) • sk) + (v k - sk) := by
        rw [sum_range_succ, Nat.cast_succ, add_smul, one_smul]
        abel
      have hnorm :
          ‖(∑ t ∈ range (k + 1), v t) - ((k + 1 : ℕ) : ℝ) • sk‖ ^ 2 =
            ‖(∑ t ∈ range k, v t) - (k : ℝ) • sk‖ ^ 2 +
              2 * ⟪(∑ t ∈ range k, v t) - (k : ℝ) • sk, v k - sk⟫ +
              ‖v k - sk‖ ^ 2 := by
        rw [hdecomp, norm_add_sq_real]
      have hinner : ⟪(∑ t ∈ range k, v t) - (k : ℝ) • sk, v k - sk⟫ ≤ 0 := by
        have hvec : (∑ t ∈ range k, v t) - (k : ℝ) • sk = (k : ℝ) • (vecAvg v k - sk) := by
          rw [smul_sub, smul_vecAvg v hkpos]
        rw [hvec, real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos hkr.le (hstep k hkpos (Nat.lt_succ_self k))
      have hrhs_split :
          ∑ t ∈ range (k + 1),
              ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2 =
            (∑ t ∈ range k,
              ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2) +
              ‖v k - sk‖ ^ 2 := by
        rw [sum_range_succ]
        simp [k, sk]
      rw [hrhs_split]
      calc ‖(∑ t ∈ range (k + 1), v t) -
              ((k + 1 : ℕ) : ℝ) • metricProjection S (vecAvg v (k + 1))‖ ^ 2
          ≤ ‖(∑ t ∈ range (k + 1), v t) - ((k + 1 : ℕ) : ℝ) • sk‖ ^ 2 := hmin_sq
        _ = ‖(∑ t ∈ range k, v t) - (k : ℝ) • sk‖ ^ 2 +
              2 * ⟪(∑ t ∈ range k, v t) - (k : ℝ) • sk, v k - sk⟫ +
              ‖v k - sk‖ ^ 2 := hnorm
        _ ≤ ‖(∑ t ∈ range k, v t) - (k : ℝ) • sk‖ ^ 2 + ‖v k - sk‖ ^ 2 := by linarith
        _ ≤ (∑ t ∈ range k,
              ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2) +
              ‖v k - sk‖ ^ 2 := by linarith

/-- Bounding the projection offset `‖v t - Π_S(vecAvg v t)‖ ≤ 2 * R` using only a fixed base
point `s₀ ∈ S` with `‖v s - s₀‖ ≤ R` (so `S` need *not* be bounded). -/
private theorem norm_sub_metricProjection_vecAvg_le {S : Set E} (hc : IsComplete S)
    (hS : Convex ℝ S) {s₀ : E} (hs₀ : s₀ ∈ S) {v : ℕ → E} {R : ℝ} {t : ℕ} (ht : 0 < t)
    (hR : ∀ s ≤ t, ‖v s - s₀‖ ≤ R) :
    ‖v t - metricProjection S (vecAvg v t)‖ ≤ 2 * R := by
  have htpos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht
  have havg : ‖vecAvg v t - s₀‖ ≤ R := by
    have hmul : (t : ℝ) • (vecAvg v t - s₀) = ∑ s ∈ range t, (v s - s₀) := by
      rw [smul_sub, smul_vecAvg v ht, sum_sub_distrib, sum_const, card_range,
        Nat.cast_smul_eq_nsmul]
    have hnorm : (t : ℝ) * ‖vecAvg v t - s₀‖ = ‖∑ s ∈ range t, (v s - s₀)‖ := by
      rw [← hmul, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hsum : ‖∑ s ∈ range t, (v s - s₀)‖ ≤ ∑ s ∈ range t, ‖v s - s₀‖ := norm_sum_le ..
    have hbd : ∑ s ∈ range t, ‖v s - s₀‖ ≤ (t : ℝ) * R := by
      calc ∑ s ∈ range t, ‖v s - s₀‖
          ≤ ∑ _s ∈ range t, R :=
            sum_le_sum fun s hs => hR s (le_of_lt (mem_range.mp hs))
        _ = (t : ℝ) * R := by simp [nsmul_eq_mul]
    have hle : (t : ℝ) * ‖vecAvg v t - s₀‖ ≤ (t : ℝ) * R := by linarith
    exact le_of_mul_le_mul_left hle htpos
  have hproj : ‖metricProjection S (vecAvg v t) - s₀‖ ≤ ‖vecAvg v t - s₀‖ :=
    norm_metricProjection_sub_le hc hS (vecAvg v t) hs₀
  calc ‖v t - metricProjection S (vecAvg v t)‖
      ≤ ‖v t - s₀‖ + ‖s₀ - metricProjection S (vecAvg v t)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖v t - s₀‖ + ‖metricProjection S (vecAvg v t) - s₀‖ := by
          rw [norm_sub_rev s₀ (metricProjection S (vecAvg v t))]
    _ ≤ R + R := add_le_add (hR t le_rfl) (hproj.trans havg)
    _ = 2 * R := by ring

/-- **Deterministic `2 * R / √T` Blackwell approachability rate**: works for arbitrary (possibly
unbounded) complete convex `S` containing `s₀`, whenever `‖v t - s₀‖ ≤ R` and each `v t` (`t ≥ 1`)
lies in the supporting halfspace `⟪vecAvg v t - s_t, v t - s_t⟫ ≤ 0`. -/
theorem blackwell_dist_le_div_sqrt {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s₀ : E} (hs₀ : s₀ ∈ S) {v : ℕ → E} {R : ℝ} (hRnn : 0 ≤ R) {T : ℕ} (hT : 0 < T)
    (hR : ∀ t < T, ‖v t - s₀‖ ≤ R)
    (hstep : ∀ t, 0 < t → t < T →
      let s := metricProjection S (vecAvg v t)
      ⟪vecAvg v t - s, v t - s⟫ ≤ 0) :
    distToSet S (vecAvg v T) ≤ 2 * R / Real.sqrt T := by
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hbase := blackwell_dist_sq_le_sum hc hS hs₀ v T hstep
  have hL : ‖(∑ t ∈ range T, v t) - (T : ℝ) • metricProjection S (vecAvg v T)‖ =
      (T : ℝ) * distToSet S (vecAvg v T) := by
    have heq : (∑ t ∈ range T, v t) - (T : ℝ) • metricProjection S (vecAvg v T) =
        (T : ℝ) • (vecAvg v T - metricProjection S (vecAvg v T)) := by
      rw [smul_sub, smul_vecAvg v hT]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hTpos, distToSet]
  have hsum : ∑ t ∈ range T,
      ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2 ≤
      (T : ℝ) * (2 * R) ^ 2 := by
    calc ∑ t ∈ range T,
          ‖v t - (if t = 0 then s₀ else metricProjection S (vecAvg v t))‖ ^ 2
        ≤ ∑ _t ∈ range T, (2 * R) ^ 2 := by
          refine sum_le_sum fun t ht => ?_
          rw [mem_range] at ht
          split_ifs with ht0
          · have hbd : ‖v t - s₀‖ ≤ 2 * R := by linarith [hR t ht]
            exact pow_le_pow_left₀ (norm_nonneg _) hbd 2
          · have hbd := norm_sub_metricProjection_vecAvg_le hc hS hs₀ (Nat.pos_of_ne_zero ht0)
              (fun s hs => hR s (lt_of_le_of_lt hs ht))
            exact pow_le_pow_left₀ (norm_nonneg _) hbd 2
      _ = (T : ℝ) * (2 * R) ^ 2 := by simp [nsmul_eq_mul]
  have hsq : ((T : ℝ) * distToSet S (vecAvg v T)) ^ 2 ≤ (T : ℝ) * (2 * R) ^ 2 := by
    rw [← hL]
    exact hbase.trans hsum
  have hdiv : distToSet S (vecAvg v T) ^ 2 ≤ (2 * R / Real.sqrt T) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hTpos.le, mul_pow] at *
    rw [le_div_iff₀ hTpos]
    have hT2 : (T : ℝ) ^ 2 * distToSet S (vecAvg v T) ^ 2 ≤ (T : ℝ) * (2 * R) ^ 2 := hsq
    have : (T : ℝ) * (distToSet S (vecAvg v T) ^ 2 * (T : ℝ)) =
        (T : ℝ) ^ 2 * distToSet S (vecAvg v T) ^ 2 := by ring
    exact le_of_mul_le_mul_left (by nlinarith) hTpos
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rwa [Real.sqrt_sq (distToSet_nonneg S _),
    Real.sqrt_sq (div_nonneg (by linarith) (Real.sqrt_nonneg _))] at hsqrt

/-- **Tight quadratic recursion for complete convex cones**: when `S` contains `0` and is closed
under nonnegative scalar multiplication, dropping the projection shift gives the unaveraged bound
`distToSet S (∑ t < T, v t) ^ 2 ≤ ∑ t < T, ‖v t‖ ^ 2` (saving a factor of `2` over general convex
sets). -/
theorem blackwell_cone_dist_sq_le_sum {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    (hzero : (0 : E) ∈ S) (v : ℕ → E) (T : ℕ)
    (hstep : ∀ t < T,
      let X := ∑ s ∈ range t, v s
      ⟪X - metricProjection S X, v t⟫ ≤ 0) :
    distToSet S (∑ t ∈ range T, v t) ^ 2 ≤ ∑ t ∈ range T, ‖v t‖ ^ 2 := by
  induction T with
  | zero =>
    simp only [range_zero, sum_empty]
    rw [distToSet_eq_zero_of_mem hc hS hzero]
    norm_num
  | succ k ih =>
    have hih := ih fun t ht => hstep t (lt_trans ht (Nat.lt_succ_self k))
    set X := ∑ t ∈ range k, v t
    set s := metricProjection S X
    have hs_mem : s ∈ S := metricProjection_mem ⟨0, hzero⟩ hc hS X
    have hmin : distToSet S (X + v k) ^ 2 ≤ ‖(X + v k) - s‖ ^ 2 :=
      pow_le_pow_left₀ (distToSet_nonneg S _) (distToSet_le_norm_sub hc hS hs_mem (X + v k)) 2
    have hexp : ‖(X + v k) - s‖ ^ 2 = ‖X - s‖ ^ 2 + 2 * ⟪X - s, v k⟫ + ‖v k‖ ^ 2 := by
      have : X + v k - s = (X - s) + v k := by abel
      rw [this, norm_add_sq_real]
    have hinner : ⟪X - s, v k⟫ ≤ 0 := hstep k (Nat.lt_succ_self k)
    rw [sum_range_succ, sum_range_succ (fun t => ‖v t‖ ^ 2)]
    change distToSet S (X + v k) ^ 2 ≤ (∑ t ∈ range k, ‖v t‖ ^ 2) + ‖v k‖ ^ 2
    have hdistX : ‖X - s‖ ^ 2 = distToSet S X ^ 2 := rfl
    linarith

/-- Square-root form of `blackwell_cone_dist_sq_le_sum` (`distToSet S (∑ t < T, v t) ≤ R * √T`). -/
theorem blackwell_cone_dist_le {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    (hzero : (0 : E) ∈ S) {v : ℕ → E} {R : ℝ} (hRnn : 0 ≤ R) (T : ℕ)
    (hR : ∀ t < T, ‖v t‖ ≤ R)
    (hstep : ∀ t < T,
      let X := ∑ s ∈ range t, v s
      ⟪X - metricProjection S X, v t⟫ ≤ 0) :
    distToSet S (∑ t ∈ range T, v t) ≤ R * Real.sqrt T := by
  have h1 := blackwell_cone_dist_sq_le_sum hc hS hzero v T hstep
  have h2 : ∑ t ∈ range T, ‖v t‖ ^ 2 ≤ (T : ℝ) * R ^ 2 := by
    calc ∑ t ∈ range T, ‖v t‖ ^ 2
        ≤ ∑ _t ∈ range T, R ^ 2 :=
          sum_le_sum fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hR t (mem_range.mp ht)) 2
      _ = (T : ℝ) * R ^ 2 := by simp [nsmul_eq_mul]
  have hsq : distToSet S (∑ t ∈ range T, v t) ^ 2 ≤ (R * Real.sqrt T) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
    linarith
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (distToSet_nonneg S _),
    Real.sqrt_sq (mul_nonneg hRnn (Real.sqrt_nonneg _))] at hs

end Potential

section Conditions

variable {I J E : Type*} [Fintype I] [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expected vector payoff `∑ i, p i • m i j` when the row player plays mixed weights `p` against
pure column action `j`. -/
@[expose] noncomputable def expectedPayoff (m : I → J → E) (p : I → ℝ) (j : J) : E :=
  ∑ i, p i • m i j

/-- Bilinear expected vector payoff `∑ i, ∑ j, (p i * q j) • m i j`. -/
@[expose] noncomputable def bilinearPayoff (m : I → J → E) (p : I → ℝ) (q : J → ℝ) : E :=
  ∑ i, ∑ j, (p i * q j) • m i j

theorem bilinearPayoff_eq_sum_row (m : I → J → E) (p : I → ℝ) (q : J → ℝ) :
    bilinearPayoff m p q = ∑ i, p i • ∑ j, q j • m i j := by
  simp only [bilinearPayoff, smul_sum, smul_smul]

theorem bilinearPayoff_eq_sum_col (m : I → J → E) (p : I → ℝ) (q : J → ℝ) :
    bilinearPayoff m p q = ∑ j, q j • expectedPayoff m p j := by
  simp only [bilinearPayoff, expectedPayoff, smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/-- **Blackwell's response condition**: for every mixed column strategy `q ∈ Δ(J)`, there exists a
mixed row strategy `p ∈ Δ(I)` placing the expected vector payoff `bilinearPayoff m p q` in `S`. -/
@[expose] def SatisfiesResponseCondition (m : I → J → E) (S : Set E) : Prop :=
  ∀ q : J → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 →
    ∃ p : I → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ bilinearPayoff m p q ∈ S

/-- **Blackwell's halfspace condition**: every closed halfspace `{x | ⟪w, x⟫ ≤ c}` containing `S`
is forceable by some mixed row strategy `p ∈ Δ(I)` against all pure column actions `j : J`. -/
@[expose] def SatisfiesHalfspaceCondition (m : I → J → E) (S : Set E) : Prop :=
  ∀ (w : E) (c : ℝ), (∀ s ∈ S, ⟪w, s⟫ ≤ c) →
    ∃ p : I → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∀ j, ⟪w, expectedPayoff m p j⟫ ≤ c

/-- The closed simplex `{p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}` is compact. -/
private theorem isCompact_probSimplex :
    IsCompact {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
  have hsub : {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} ⊆
      Set.pi Set.univ fun _ : I => Set.Icc (0 : ℝ) 1 := by
    intro p ⟨hp0, hp1⟩ i _
    refine ⟨hp0 i, ?_⟩
    have hi : p i ≤ ∑ k, p k := Finset.single_le_sum (fun k _ => hp0 k) (mem_univ i)
    linarith
  have hclosed : IsClosed {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
    have h1 : IsClosed {p : I → ℝ | ∀ i, 0 ≤ p i} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {p : I → ℝ | ∑ i, p i = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact h1.inter h2
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub

/-- The attainable payoff set `C_q = {m(p, q) | p ∈ Δ(I)}` is nonempty, convex, and compact. -/
private theorem attainable_compact_convex [Nonempty I] (m : I → J → E) (q : J → ℝ) :
    let C : Set E := (fun p : I → ℝ => bilinearPayoff m p q) ''
      {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
    C.Nonempty ∧ Convex ℝ C ∧ IsCompact C := by
  intro C
  classical
  have hsim_ne : ({p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}).Nonempty := by
    obtain ⟨i₀⟩ := ‹Nonempty I›
    refine ⟨fun i => if i = i₀ then 1 else 0, fun i => ?_, by simp⟩
    dsimp only
    split_ifs <;> norm_num
  have hsim_cvx : Convex ℝ {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
    intro p hp p' hp' a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hp'.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2, hp'.2,
      mul_one]
    exact hab
  have hcont : Continuous (fun p : I → ℝ => bilinearPayoff m p q) := by
    simp only [bilinearPayoff_eq_sum_row]
    fun_prop
  refine ⟨hsim_ne.image _, ?_, isCompact_probSimplex.image hcont⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ a b ha hb hab
  refine ⟨a • p + b • p', hsim_cvx hp hp' ha hb hab, ?_⟩
  simp only [bilinearPayoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_sum, smul_smul]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [add_mul, add_smul, mul_assoc, mul_assoc]

/-- Separating-hyperplane lemma: if `C` is nonempty, compact, convex and `S` is nonempty, complete,
convex, and `Disjoint C S`, then a nearest point `c₀ ∈ C` to `S` gives `δ = distToSet S c₀ > 0`
separating `S` and `C` by `⟪c₀ - Π_S c₀, s⟫ ≤ ⟪c₀ - Π_S c₀, Π_S c₀⟫` for all `s ∈ S` and
`⟪c₀ - Π_S c₀, Π_S c₀⟫ + δ ^ 2 ≤ ⟪c₀ - Π_S c₀, v⟫` for all `v ∈ C`. -/
private theorem exists_strict_sep_compact_complete {C S : Set E}
    (hCne : C.Nonempty) (hCcmp : IsCompact C) (hCcvx : Convex ℝ C)
    (hSne : S.Nonempty) (hSc : IsComplete S) (hScvx : Convex ℝ S)
    (hdisj : Disjoint C S) :
    ∃ (c₀ : E) (δ : ℝ), c₀ ∈ C ∧ 0 < δ ∧
      (∀ v ∈ C, δ ≤ distToSet S v) ∧
      (∀ s ∈ S, ⟪c₀ - metricProjection S c₀, s⟫ ≤
        ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫) ∧
      (∀ v ∈ C,
        ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫ + δ ^ 2 ≤
          ⟪c₀ - metricProjection S c₀, v⟫) := by
  have hproj_cont : Continuous (metricProjection S) :=
    (lipschitzWith_metricProjection hSne hSc hScvx).continuous
  have hdist_cont : Continuous (distToSet S) :=
    (continuous_id.sub hproj_cont).norm
  obtain ⟨c₀, hc₀_mem, hc₀_min⟩ := hCcmp.exists_isMinOn hCne hdist_cont.continuousOn
  have hc₀_not : c₀ ∉ S := Set.disjoint_left.mp hdisj hc₀_mem
  set s₀ := metricProjection S c₀
  have hs₀_mem : s₀ ∈ S := metricProjection_mem hSne hSc hScvx c₀
  set δ := distToSet S c₀
  have hδ_pos : 0 < δ := distToSet_pos_of_not_mem hSne hSc hScvx hc₀_not
  refine ⟨c₀, δ, hc₀_mem, hδ_pos, fun v hv => hc₀_min hv, ?_, ?_⟩
  · intro s hs
    have hvar := inner_sub_metricProjection_le_zero hSc hScvx c₀ hs
    rw [inner_sub_right] at hvar
    linarith
  · intro v hv
    have hinner_ge : 0 ≤ ⟪c₀ - s₀, v - c₀⟫ := by
      by_contra hneg
      have hlt : ⟪c₀ - s₀, v - c₀⟫ < 0 := lt_of_not_ge hneg
      have hquad : ∀ t : ℝ, 0 < t → t ≤ 1 →
          0 ≤ 2 * ⟪c₀ - s₀, v - c₀⟫ + t * ‖v - c₀‖ ^ 2 := by
        intro t ht0 ht1
        have hxt_mem : (1 - t) • c₀ + t • v ∈ C :=
          hCcvx hc₀_mem hv (sub_nonneg.mpr ht1) ht0.le (by ring)
        have h1 : δ ≤ distToSet S ((1 - t) • c₀ + t • v) := hc₀_min hxt_mem
        have h2 : distToSet S ((1 - t) • c₀ + t • v) ≤ ‖((1 - t) • c₀ + t • v) - s₀‖ :=
          distToSet_le_norm_sub hSc hScvx hs₀_mem _
        have hsq : δ ^ 2 ≤ ‖((1 - t) • c₀ + t • v) - s₀‖ ^ 2 :=
          pow_le_pow_left₀ hδ_pos.le (h1.trans h2) 2
        have hre : (1 - t) • c₀ + t • v - s₀ = (c₀ - s₀) + t • (v - c₀) := by
          rw [sub_smul, one_smul, smul_sub]
          abel
        rw [hre, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0] at hsq
        have hmul : 0 ≤ t * (2 * ⟪c₀ - s₀, v - c₀⟫ + t * ‖v - c₀‖ ^ 2) := by
          have : δ ^ 2 = ‖c₀ - s₀‖ ^ 2 := rfl
          linarith [show (t * ‖v - c₀‖) ^ 2 = t * (t * ‖v - c₀‖ ^ 2) by ring]
        exact nonneg_of_mul_nonneg_right hmul ht0
      by_cases hnv : ‖v - c₀‖ = 0
      · have := hquad 1 zero_lt_one le_rfl
        simp only [hnv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          add_zero] at this
        linarith
      · have hnv2 : 0 < ‖v - c₀‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnv))
        set t := min 1 (-⟪c₀ - s₀, v - c₀⟫ / ‖v - c₀‖ ^ 2)
        have ht0 : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr hlt) hnv2)
        have ht1 : t ≤ 1 := min_le_left _ _
        have ht2 : t * ‖v - c₀‖ ^ 2 ≤ -⟪c₀ - s₀, v - c₀⟫ := by
          calc t * ‖v - c₀‖ ^ 2
              ≤ (-⟪c₀ - s₀, v - c₀⟫ / ‖v - c₀‖ ^ 2) * ‖v - c₀‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hnv2.le
            _ = -⟪c₀ - s₀, v - c₀⟫ := div_mul_cancel₀ _ hnv2.ne'
        linarith [hquad t ht0 ht1]
    have hsplit : ⟪c₀ - s₀, v⟫ - ⟪c₀ - s₀, s₀⟫ =
        ⟪c₀ - s₀, v - c₀⟫ + ⟪c₀ - s₀, c₀ - s₀⟫ := by
      rw [inner_sub_right, inner_sub_right]
      ring
    have hself : ⟪c₀ - s₀, c₀ - s₀⟫ = δ ^ 2 := real_inner_self_eq_norm_sq _
    linarith

/-- Von Neumann minimax implies **Blackwell's halfspace condition** from the **response condition**
[Blackwell1956]. -/
theorem halfspace_of_response [Nonempty I] {m : I → J → E} {S : Set E}
    (hresp : SatisfiesResponseCondition m S) :
    SatisfiesHalfspaceCondition m S := by
  intro w c hS_half
  let M : I → J → ℝ := fun i j => ⟪w, m i j⟫
  have hcol : ∀ q : Convexity.StdSimplex ℝ J, ∃ i : I, ∑ j, q.weights j * M i j ≤ c := by
    intro q
    have hq0 : ∀ j, 0 ≤ q.weights j := fun j => q.nonneg j
    have hq1 : ∑ j, q.weights j = 1 := by simp
    obtain ⟨p, hp0, hp1, hpS⟩ := hresp q.weights hq0 hq1
    have hle : ∑ i, p i * ∑ j, q.weights j * M i j ≤ c := by
      have hlin : ⟪w, bilinearPayoff m p q.weights⟫ =
          ∑ i, p i * ∑ j, q.weights j * M i j := by
        simp only [bilinearPayoff, inner_sum, real_inner_smul_right, M, mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
      rw [← hlin]
      exact hS_half _ hpS
    by_contra hnot
    push Not at hnot
    have hgt : c < ∑ i, p i * ∑ j, q.weights j * M i j := by
      have h1 : ∀ i, p i * c ≤ p i * ∑ j, q.weights j * M i j := fun i =>
        mul_le_mul_of_nonneg_left (hnot i).le (hp0 i)
      obtain ⟨i₀, hi₀⟩ : ∃ i : I, 0 < p i := by
        by_contra h0
        push Not at h0
        have : ∑ i, p i ≤ 0 := sum_nonpos fun i _ => h0 i
        linarith
      have hstrict : p i₀ * c < p i₀ * ∑ j, q.weights j * M i₀ j :=
        mul_lt_mul_of_pos_left (hnot i₀) hi₀
      have hsum_lt := Finset.sum_lt_sum (fun i _ => h1 i) ⟨i₀, mem_univ _, hstrict⟩
      rwa [← sum_mul, hp1, one_mul] at hsum_lt
    linarith
  obtain ⟨p, hp⟩ := Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le M hcol
  refine ⟨p.weights, fun i => p.nonneg i, ?_, fun j => ?_⟩
  · simp
  · have hlin : ⟪w, expectedPayoff m p.weights j⟫ = ∑ i, p.weights i * M i j := by
      simp only [expectedPayoff, inner_sum, real_inner_smul_right, M]
    rw [hlin]
    exact hp j

/-- **Blackwell's characterization theorem for convex sets** [Blackwell1956]: for a nonempty
complete convex set `S` in a real inner product space `E`, `SatisfiesResponseCondition m S` holds
iff `SatisfiesHalfspaceCondition m S` holds. -/
theorem satisfiesResponseCondition_iff_halfspace [Nonempty I]
    {m : I → J → E} {S : Set E} (hSne : S.Nonempty) (hSc : IsComplete S) (hScvx : Convex ℝ S) :
    SatisfiesResponseCondition m S ↔ SatisfiesHalfspaceCondition m S := by
  refine ⟨halfspace_of_response, fun hhalf q hq0 hq1 => ?_⟩
  by_contra hnot
  set C : Set E := (fun p : I → ℝ => bilinearPayoff m p q) ''
    {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
  have hdisj : Disjoint C S := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, ⟨hp0, hp1⟩, rfl⟩ hxS
    exact hnot ⟨p, hp0, hp1, hxS⟩
  obtain ⟨hCne, hCcvx, hCcmp⟩ := attainable_compact_convex m q
  obtain ⟨c₀, δ, _, hδ, _, hS_le, hC_ge⟩ :=
    exists_strict_sep_compact_complete hCne hCcmp hCcvx hSne hSc hScvx hdisj
  obtain ⟨p, hp0, hp1, hp_half⟩ := hhalf (c₀ - metricProjection S c₀)
    ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫ hS_le
  have hupper : ⟪c₀ - metricProjection S c₀, bilinearPayoff m p q⟫ ≤
      ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫ := by
    rw [bilinearPayoff_eq_sum_col, inner_sum]
    calc ∑ j, ⟪c₀ - metricProjection S c₀, q j • expectedPayoff m p j⟫
        = ∑ j, q j * ⟪c₀ - metricProjection S c₀, expectedPayoff m p j⟫ := by
          refine sum_congr rfl fun j _ => real_inner_smul_right ..
      _ ≤ ∑ j, q j * ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫ :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp_half j) (hq0 j)
      _ = ⟪c₀ - metricProjection S c₀, metricProjection S c₀⟫ := by
          rw [← sum_mul, hq1, one_mul]
  have hlower := hC_ge (bilinearPayoff m p q) ⟨p, ⟨hp0, hp1⟩, rfl⟩
  have : 0 < δ ^ 2 := sq_pos_of_pos hδ
  linarith

/-- **Necessity of Blackwell's condition** [Blackwell1956]: if `¬ SatisfiesResponseCondition m S`
for a nonempty complete convex set `S`, then there exist a stationary mixed adversary strategy
`q ∈ Δ(J)` and a gap `δ > 0` such that *every* horizon `T ≥ 1` and *every* sequence of mixed row
strategies `p t ∈ Δ(I)` has `δ ≤ distToSet S (vecAvg (fun t => bilinearPayoff m (p t) q) T)`. -/
theorem exists_nonapproachable_dist_ge [Nonempty I] {m : I → J → E} {S : Set E}
    (hSne : S.Nonempty) (hSc : IsComplete S) (hScvx : Convex ℝ S)
    (hfail : ¬ SatisfiesResponseCondition m S) :
    ∃ (q : J → ℝ) (δ : ℝ),
      (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧ 0 < δ ∧
      ∀ (T : ℕ), 0 < T →
        ∀ (p : ℕ → I → ℝ), (∀ t < T, (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) →
          δ ≤ distToSet S (vecAvg (fun t => bilinearPayoff m (p t) q) T) := by
  have hex : ∃ q : J → ℝ, (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧
      ∀ p : I → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → bilinearPayoff m p q ∉ S := by
    by_contra h
    apply hfail
    intro q hq0 hq1
    by_contra hno
    exact h ⟨q, hq0, hq1, fun p hp0 hp1 hpS => hno ⟨p, hp0, hp1, hpS⟩⟩
  obtain ⟨q, hq0, hq1, hq_out⟩ := hex
  set C : Set E := (fun p : I → ℝ => bilinearPayoff m p q) ''
    {p : I → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
  have hdisj : Disjoint C S := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, ⟨hp0, hp1⟩, rfl⟩ hxS
    exact hq_out p hp0 hp1 hxS
  obtain ⟨hCne, hCcvx, hCcmp⟩ := attainable_compact_convex m q
  obtain ⟨_, δ, _, hδ, hmin, _, _⟩ :=
    exists_strict_sep_compact_complete hCne hCcmp hCcvx hSne hSc hScvx hdisj
  refine ⟨q, δ, hq0, hq1, hδ, fun T hT p hp => ?_⟩
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  let pbar : I → ℝ := fun i => (T : ℝ)⁻¹ * ∑ t ∈ range T, p t i
  have hpbar0 : ∀ i, 0 ≤ pbar i := fun i =>
    mul_nonneg (inv_nonneg.mpr hTpos.le)
      (sum_nonneg fun t ht => (hp t (mem_range.mp ht)).1 i)
  have hpbar1 : ∑ i, pbar i = 1 := by
    simp only [pbar, ← mul_sum]
    rw [sum_comm]
    have hones : ∑ t ∈ range T, ∑ i, p t i = (T : ℝ) := by
      calc ∑ t ∈ range T, ∑ i, p t i
          = ∑ _t ∈ range T, (1 : ℝ) :=
            sum_congr rfl fun t ht => (hp t (mem_range.mp ht)).2
        _ = (T : ℝ) := by simp
    rw [hones, inv_mul_cancel₀ hTpos.ne']
  have havg_eq : vecAvg (fun t => bilinearPayoff m (p t) q) T = bilinearPayoff m pbar q := by
    simp only [vecAvg, bilinearPayoff_eq_sum_row, pbar]
    rw [sum_comm, smul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_smul, smul_smul]
  rw [havg_eq]
  exact hmin _ ⟨pbar, ⟨hpbar0, hpbar1⟩, rfl⟩

end Conditions

section AdaptiveRandomized

variable {I J E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A randomized causal strategy for repeated play: given the reverse-ordered history `h : List I`
of realized pure row actions played so far, selects a probability distribution over `I`. -/
structure ApproachStrategy (I : Type*) [Fintype I] where
  /-- Mixed action weights `prob h : I → ℝ` played after observing history `h`. -/
  prob : List I → I → ℝ
  /-- Every probability weight is nonnegative. -/
  nonneg : ∀ h i, 0 ≤ prob h i
  /-- Weights sum to `1` at every history. -/
  sum_eq_one : ∀ h, ∑ i, prob h i = 1

/-- Exact `t`-round expectation of a real-valued function `f : List I → ℝ` along randomized play
of `strat`, starting from prefix history `h : List I` (stored most-recent-first). -/
@[expose] noncomputable def expectHistory (strat : ApproachStrategy I) :
    ℕ → List I → (List I → ℝ) → ℝ
  | 0, h, f => f h
  | t + 1, h, f => ∑ i : I, strat.prob h i * expectHistory strat t (i :: h) f

theorem expectHistory_const (strat : ApproachStrategy I) (t : ℕ) (h : List I) (c : ℝ) :
    expectHistory strat t h (fun _ => c) = c := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [expectHistory, ih, ← sum_mul, strat.sum_eq_one, one_mul]

theorem expectHistory_add (strat : ApproachStrategy I) (t : ℕ) (h : List I)
    (f g : List I → ℝ) :
    expectHistory strat t h (fun x => f x + g x) =
      expectHistory strat t h f + expectHistory strat t h g := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [expectHistory, ih, mul_add, sum_add_distrib]

theorem expectHistory_smul (strat : ApproachStrategy I) (t : ℕ) (h : List I)
    (c : ℝ) (f : List I → ℝ) :
    expectHistory strat t h (fun x => c * f x) = c * expectHistory strat t h f := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [expectHistory, ih]
    rw [mul_sum]
    refine sum_congr rfl fun i _ => by ring

theorem expectHistory_mono (strat : ApproachStrategy I) {t : ℕ} {h : List I}
    {f g : List I → ℝ} (hfg : ∀ x, x.length = h.length + t → f x ≤ g x) :
    expectHistory strat t h f ≤ expectHistory strat t h g := by
  induction t generalizing h with
  | zero => exact hfg h rfl
  | succ t ih =>
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih fun x hx => hfg x ?_)
      (strat.nonneg h i)
    simp only [List.length_cons] at hx
    omega

theorem expectHistory_nonneg (strat : ApproachStrategy I) {t : ℕ} {h : List I}
    {f : List I → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectHistory strat t h f := by
  simpa only [expectHistory_const] using
    expectHistory_mono strat (t := t) (h := h) (f := fun _ => 0) (g := f) fun x _ => hf x

/-- Discrete one-step expansion appending `expectHistory strat (t + 1) h f`. -/
theorem expectHistory_succ_right (strat : ApproachStrategy I) (t : ℕ) (h : List I)
    (f : List I → ℝ) :
    expectHistory strat (t + 1) h f =
      expectHistory strat t h (fun x => ∑ i : I, strat.prob x i * f (i :: x)) := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    change ∑ i : I, strat.prob h i * expectHistory strat (t + 1) (i :: h) f =
      ∑ i : I, strat.prob h i *
        expectHistory strat t (i :: h) (fun x => ∑ k : I, strat.prob x k * f (k :: x))
    refine sum_congr rfl fun i _ => congrArg (strat.prob h i * ·) (ih (i :: h))

/-- Jensen / Cauchy–Schwarz inequality for `expectHistory`: `𝔼[f] ^ 2 ≤ 𝔼[f ^ 2]`. -/
theorem sq_expectHistory_le (strat : ApproachStrategy I) (t : ℕ) (h : List I)
    (f : List I → ℝ) :
    expectHistory strat t h f ^ 2 ≤ expectHistory strat t h (fun x => f x ^ 2) := by
  induction t generalizing h with
  | zero => simp [expectHistory]
  | succ t ih =>
    simp only [expectHistory]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset I)
      (fun i => Real.sqrt (strat.prob h i))
      (fun i => Real.sqrt (strat.prob h i) * expectHistory strat t (i :: h) f)
    have hL : ∑ i, Real.sqrt (strat.prob h i) *
        (Real.sqrt (strat.prob h i) * expectHistory strat t (i :: h) f) =
        ∑ i, strat.prob h i * expectHistory strat t (i :: h) f := by
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (strat.nonneg h i)]
    have hR1 : ∑ i, Real.sqrt (strat.prob h i) ^ 2 = 1 := by
      have : ∑ i, Real.sqrt (strat.prob h i) ^ 2 = ∑ i, strat.prob h i :=
        sum_congr rfl fun i _ => Real.sq_sqrt (strat.nonneg h i)
      rw [this, strat.sum_eq_one]
    have hR2 : ∑ i, (Real.sqrt (strat.prob h i) * expectHistory strat t (i :: h) f) ^ 2 =
        ∑ i, strat.prob h i * expectHistory strat t (i :: h) f ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (strat.nonneg h i)]
    rw [hL, hR1, one_mul, hR2] at hcs
    exact hcs.trans (sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (ih (i :: h)) (strat.nonneg h i))

/-- Markov's inequality for `expectHistory`: `Pr[c ≤ f] ≤ 𝔼[f] / c` for nonnegative `f` and
`c > 0`. -/
theorem expectHistory_indicator_le (strat : ApproachStrategy I) (t : ℕ) (h : List I)
    (f : List I → ℝ) (hf : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 < c) :
    expectHistory strat t h (fun x => if c ≤ f x then (1 : ℝ) else 0) ≤
      expectHistory strat t h f / c := by
  have h1 : expectHistory strat t h (fun x => c * if c ≤ f x then (1 : ℝ) else 0) ≤
      expectHistory strat t h f := by
    refine expectHistory_mono strat fun x _ => ?_
    split_ifs with hx
    · linarith
    · simpa using hf x
  rw [expectHistory_smul] at h1
  rwa [le_div_iff₀ hc, mul_comm]

/-- Cumulative realized vector payoff along a reverse-ordered history `h : List I` against an
adaptive adversary `adv : List I → J` (at step `h`, the adversary sees the realized prefix `h` and
picks `adv h`). -/
@[expose] def sumPayoff (m : I → J → E) (adv : List I → J) : List I → E
  | [] => 0
  | i :: rest => sumPayoff m adv rest + m i (adv rest)

omit [Fintype I] [InnerProductSpace ℝ E] in
@[simp] theorem sumPayoff_nil (m : I → J → E) (adv : List I → J) :
    sumPayoff m adv [] = 0 := rfl

omit [Fintype I] [InnerProductSpace ℝ E] in
@[simp] theorem sumPayoff_cons (m : I → J → E) (adv : List I → J) (i : I) (h : List I) :
    sumPayoff m adv (i :: h) = sumPayoff m adv h + m i (adv h) := rfl

omit [Fintype I] in
private theorem norm_sumPayoff_sub_le (m : I → J → E) (adv : List I → J)
    {s₀ : E} {R : ℝ} (hR : ∀ i j, ‖m i j - s₀‖ ≤ R) (h : List I) :
    ‖sumPayoff m adv h - (h.length : ℝ) • s₀‖ ≤ (h.length : ℝ) * R := by
  induction h with
  | nil => simp
  | cons i rest ih =>
    simp only [sumPayoff_cons, List.length_cons, Nat.cast_succ, add_smul, one_smul]
    have hre : sumPayoff m adv rest + m i (adv rest) - ((rest.length : ℝ) • s₀ + s₀) =
        (sumPayoff m adv rest - (rest.length : ℝ) • s₀) + (m i (adv rest) - s₀) := by abel
    rw [hre]
    calc ‖(sumPayoff m adv rest - (rest.length : ℝ) • s₀) + (m i (adv rest) - s₀)‖
        ≤ ‖sumPayoff m adv rest - (rest.length : ℝ) • s₀‖ + ‖m i (adv rest) - s₀‖ :=
          norm_add_le ..
      _ ≤ (rest.length : ℝ) * R + R := add_le_add ih (hR i (adv rest))
      _ = ((rest.length : ℝ) + 1) * R := by ring

/-- **Randomized adaptive Blackwell squared-distance bound** [Blackwell1956]: if at every nonempty
history `h`, `strat.prob h` places the expected vector payoff inside the supporting halfspace at
`s = metricProjection S (h.length⁻¹ • sumPayoff m adv h)`, then for all `T ≥ 1`,
`𝔼[distToSet S (T⁻¹ • sumPayoff m adv h) ^ 2] ≤ (2 * R) ^ 2 / T`. -/
theorem blackwell_expect_dist_sq_le {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s₀ : E} (hs₀ : s₀ ∈ S) (m : I → J → E) {R : ℝ} (hRnn : 0 ≤ R)
    (hR : ∀ i j, ‖m i j - s₀‖ ≤ R)
    (strat : ApproachStrategy I) (adv : List I → J)
    (hstep : ∀ (h : List I), 0 < h.length →
      let y := (h.length : ℝ)⁻¹ • sumPayoff m adv h
      let s := metricProjection S y
      ⟪y - s, expectedPayoff m (strat.prob h) (adv h) - s⟫ ≤ 0)
    (T : ℕ) (hT : 0 < T) :
    expectHistory strat T []
      (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2) ≤
      (2 * R) ^ 2 / (T : ℝ) := by
  have hcore : ∀ t : ℕ,
      expectHistory strat t []
        (fun h => ‖sumPayoff m adv h -
          (t : ℝ) • metricProjection S ((t : ℝ)⁻¹ • sumPayoff m adv h)‖ ^ 2) ≤
        (t : ℝ) * (2 * R) ^ 2 := by
    intro t
    induction t with
    | zero => simp [expectHistory]
    | succ k ih =>
      rw [expectHistory_succ_right]
      cases k with
      | zero =>
        simp only [expectHistory, zero_add, Nat.cast_one, inv_one, one_smul,
          sumPayoff_cons, sumPayoff_nil, zero_add, one_mul]
        calc ∑ i : I, strat.prob [] i *
              ‖m i (adv []) - metricProjection S (m i (adv []))‖ ^ 2
            ≤ ∑ i : I, strat.prob [] i * (2 * R) ^ 2 := by
              refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (strat.nonneg [] i)
              have h1 := distToSet_le_norm_sub hc hS hs₀ (m i (adv []))
              have h2 : distToSet S (m i (adv [])) ≤ 2 * R := by linarith [hR i (adv [])]
              exact pow_le_pow_left₀ (distToSet_nonneg S _) h2 2
          _ = (2 * R) ^ 2 := by rw [← sum_mul, strat.sum_eq_one, one_mul]
      | succ q =>
        set k := q + 1
        have hkpos : 0 < k := Nat.succ_pos q
        have hkr : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
        have hk1pos : 0 < k + 1 := Nat.succ_pos k
        have hpt : ∀ (h : List I), h.length = k →
            ∑ i : I, strat.prob h i *
              ‖sumPayoff m adv (i :: h) -
                ((k + 1 : ℕ) : ℝ) • metricProjection S
                  (((k + 1 : ℕ) : ℝ)⁻¹ • sumPayoff m adv (i :: h))‖ ^ 2 ≤
              ‖sumPayoff m adv h -
                (k : ℝ) • metricProjection S ((k : ℝ)⁻¹ • sumPayoff m adv h)‖ ^ 2 +
              (2 * R) ^ 2 := by
          intro h hh
          set X := sumPayoff m adv h
          set y := (k : ℝ)⁻¹ • X
          set s := metricProjection S y
          have hs_mem : s ∈ S := metricProjection_mem ⟨s₀, hs₀⟩ hc hS y
          have hys : ‖y - s₀‖ ≤ R := by
            have h1 := norm_sumPayoff_sub_le m adv hR h
            rw [hh] at h1
            have hsc : (k : ℝ) * ‖y - s₀‖ = ‖X - (k : ℝ) • s₀‖ := by
              have : (k : ℝ) • (y - s₀) = X - (k : ℝ) • s₀ := by
                rw [smul_sub, smul_smul, mul_inv_cancel₀ hkr.ne', one_smul]
              rw [← this, norm_smul, Real.norm_eq_abs, abs_of_pos hkr]
            exact le_of_mul_le_mul_left (hsc ▸ h1) hkr
          have hss₀ : ‖s - s₀‖ ≤ R :=
            (norm_metricProjection_sub_le hc hS y hs₀).trans hys
          have hms : ∀ i : I, ‖m i (adv h) - s‖ ^ 2 ≤ (2 * R) ^ 2 := fun i => by
            have htri : ‖m i (adv h) - s‖ ≤ 2 * R := by
              calc ‖m i (adv h) - s‖
                  ≤ ‖m i (adv h) - s₀‖ + ‖s₀ - s‖ := norm_sub_le_norm_sub_add_norm_sub ..
                _ = ‖m i (adv h) - s₀‖ + ‖s - s₀‖ := by rw [norm_sub_rev s₀ s]
                _ ≤ R + R := add_le_add (hR i (adv h)) hss₀
                _ = 2 * R := by ring
            exact pow_le_pow_left₀ (norm_nonneg _) htri 2
          have h1 : ∀ i : I,
              ‖sumPayoff m adv (i :: h) -
                ((k + 1 : ℕ) : ℝ) • metricProjection S
                  (((k + 1 : ℕ) : ℝ)⁻¹ • sumPayoff m adv (i :: h))‖ ^ 2 ≤
              ‖X - (k : ℝ) • s‖ ^ 2 + 2 * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫ +
                ‖m i (adv h) - s‖ ^ 2 := by
            intro i
            have hm := sum_sub_smul_metricProjection_le hc hS hs_mem
              (sumPayoff m adv (i :: h)) hk1pos
            have hmsq := pow_le_pow_left₀ (norm_nonneg _) hm 2
            have hre : sumPayoff m adv (i :: h) - ((k + 1 : ℕ) : ℝ) • s =
                (X - (k : ℝ) • s) + (m i (adv h) - s) := by
              rw [sumPayoff_cons, Nat.cast_succ, add_smul, one_smul]
              abel
            rwa [hre, norm_add_sq_real] at hmsq
          have hsum_le :
              ∑ i : I, strat.prob h i *
                ‖sumPayoff m adv (i :: h) -
                  ((k + 1 : ℕ) : ℝ) • metricProjection S
                    (((k + 1 : ℕ) : ℝ)⁻¹ • sumPayoff m adv (i :: h))‖ ^ 2 ≤
              ∑ i : I, strat.prob h i *
                (‖X - (k : ℝ) • s‖ ^ 2 + 2 * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫ +
                  ‖m i (adv h) - s‖ ^ 2) :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) (strat.nonneg h i)
          have hsplit :
              ∑ i : I, strat.prob h i *
                (‖X - (k : ℝ) • s‖ ^ 2 + 2 * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫ +
                  ‖m i (adv h) - s‖ ^ 2) =
                ‖X - (k : ℝ) • s‖ ^ 2 +
                  2 * ⟪X - (k : ℝ) • s, expectedPayoff m (strat.prob h) (adv h) - s⟫ +
                  ∑ i : I, strat.prob h i * ‖m i (adv h) - s‖ ^ 2 := by
            have hlin : ∑ i : I, strat.prob h i * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫ =
                ⟪X - (k : ℝ) • s, expectedPayoff m (strat.prob h) (adv h) - s⟫ := by
              simp only [expectedPayoff, inner_sub_right, inner_sum, real_inner_smul_right,
                mul_sub, sum_sub_distrib, ← sum_mul, strat.sum_eq_one, one_mul]
            simp only [mul_add, sum_add_distrib, ← sum_mul, strat.sum_eq_one, one_mul]
            have htwo : ∑ i : I, strat.prob h i * (2 * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫) =
                2 * ∑ i : I, strat.prob h i * ⟪X - (k : ℝ) • s, m i (adv h) - s⟫ := by
              rw [mul_sum]
              exact sum_congr rfl fun i _ => by ring
            rw [htwo, hlin]
          have hcross : ⟪X - (k : ℝ) • s, expectedPayoff m (strat.prob h) (adv h) - s⟫ ≤ 0 := by
            have hre : X - (k : ℝ) • s = (k : ℝ) • (y - s) := by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ hkr.ne', one_smul]
            rw [hre, real_inner_smul_left]
            have hhh := hstep h (by omega)
            simp only [hh] at hhh
            exact mul_nonpos_of_nonneg_of_nonpos hkr.le hhh
          have hquad : ∑ i : I, strat.prob h i * ‖m i (adv h) - s‖ ^ 2 ≤ (2 * R) ^ 2 := by
            calc ∑ i : I, strat.prob h i * ‖m i (adv h) - s‖ ^ 2
                ≤ ∑ i : I, strat.prob h i * (2 * R) ^ 2 :=
                  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hms i) (strat.nonneg h i)
              _ = (2 * R) ^ 2 := by rw [← sum_mul, strat.sum_eq_one, one_mul]
          linarith
        have hstep_exp := expectHistory_mono strat (t := k) (h := [])
          (fun h hh => hpt h (by simpa using hh))
        rw [expectHistory_add, expectHistory_const] at hstep_exp
        calc expectHistory strat k []
              (fun h => ∑ i : I, strat.prob h i *
                ‖sumPayoff m adv (i :: h) -
                  ((k + 1 : ℕ) : ℝ) • metricProjection S
                    (((k + 1 : ℕ) : ℝ)⁻¹ • sumPayoff m adv (i :: h))‖ ^ 2)
            ≤ expectHistory strat k []
                (fun h => ‖sumPayoff m adv h -
                  (k : ℝ) • metricProjection S ((k : ℝ)⁻¹ • sumPayoff m adv h)‖ ^ 2) +
                (2 * R) ^ 2 := hstep_exp
          _ ≤ (k : ℝ) * (2 * R) ^ 2 + (2 * R) ^ 2 := by linarith
          _ = ((k + 1 : ℕ) : ℝ) * (2 * R) ^ 2 := by push_cast; ring
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hscale :
      expectHistory strat T []
        (fun h => ‖sumPayoff m adv h -
          (T : ℝ) • metricProjection S ((T : ℝ)⁻¹ • sumPayoff m adv h)‖ ^ 2) =
      (T : ℝ) ^ 2 * expectHistory strat T []
        (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2) := by
    rw [← expectHistory_smul]
    congr 1
    funext h
    have hre : sumPayoff m adv h -
        (T : ℝ) • metricProjection S ((T : ℝ)⁻¹ • sumPayoff m adv h) =
        (T : ℝ) • ((T : ℝ)⁻¹ • sumPayoff m adv h -
          metricProjection S ((T : ℝ)⁻¹ • sumPayoff m adv h)) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul]
    rw [hre, norm_smul, Real.norm_eq_abs, abs_of_pos hTpos, mul_pow, distToSet]
  have hmul : (T : ℝ) ^ 2 * expectHistory strat T []
      (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2) ≤ (T : ℝ) * (2 * R) ^ 2 :=
    hscale ▸ hcore T
  rw [le_div_iff₀ hTpos]
  exact le_of_mul_le_mul_left (by linarith) hTpos

/-- `L¹` expected distance bound `𝔼[dist(x̄_T, S)] ≤ 2 * R / √T` via Cauchy–Schwarz/Jensen. -/
theorem blackwell_expect_dist_le {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s₀ : E} (hs₀ : s₀ ∈ S) (m : I → J → E) {R : ℝ} (hRnn : 0 ≤ R)
    (hR : ∀ i j, ‖m i j - s₀‖ ≤ R)
    (strat : ApproachStrategy I) (adv : List I → J)
    (hstep : ∀ (h : List I), 0 < h.length →
      let y := (h.length : ℝ)⁻¹ • sumPayoff m adv h
      let s := metricProjection S y
      ⟪y - s, expectedPayoff m (strat.prob h) (adv h) - s⟫ ≤ 0)
    (T : ℕ) (hT : 0 < T) :
    expectHistory strat T []
      (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h)) ≤
      2 * R / Real.sqrt T := by
  have hTpos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have h1 := sq_expectHistory_le strat T []
    (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h))
  have h2 := blackwell_expect_dist_sq_le hc hS hs₀ m hRnn hR strat adv hstep T hT
  have hnn : 0 ≤ expectHistory strat T []
      (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h)) :=
    expectHistory_nonneg strat fun _ => distToSet_nonneg S _
  have hsq : expectHistory strat T []
      (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h)) ^ 2 ≤
      (2 * R / Real.sqrt T) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hTpos.le]
    exact h1.trans h2
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn,
    Real.sqrt_sq (div_nonneg (by linarith) (Real.sqrt_nonneg _))] at hs

/-- Markov / Chebyshev tail probability bound `Pr[dist(x̄_T, S) ≥ ε] ≤ (2 * R) ^ 2 / (T * ε ^ 2)`
for adaptive randomized Blackwell play. -/
theorem blackwell_prob_dist_ge_le {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S)
    {s₀ : E} (hs₀ : s₀ ∈ S) (m : I → J → E) {R : ℝ} (hRnn : 0 ≤ R)
    (hR : ∀ i j, ‖m i j - s₀‖ ≤ R)
    (strat : ApproachStrategy I) (adv : List I → J)
    (hstep : ∀ (h : List I), 0 < h.length →
      let y := (h.length : ℝ)⁻¹ • sumPayoff m adv h
      let s := metricProjection S y
      ⟪y - s, expectedPayoff m (strat.prob h) (adv h) - s⟫ ≤ 0)
    (T : ℕ) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    expectHistory strat T []
      (fun h => if ε ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) then (1 : ℝ) else 0) ≤
      (2 * R) ^ 2 / ((T : ℝ) * ε ^ 2) := by
  have hind : expectHistory strat T []
      (fun h => if ε ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) then (1 : ℝ) else 0) =
      expectHistory strat T []
        (fun h => if ε ^ 2 ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2 then 1 else 0) := by
    congr 1
    funext h
    have hnn := distToSet_nonneg S ((T : ℝ)⁻¹ • sumPayoff m adv h)
    have hiff : ε ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ↔
        ε ^ 2 ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2 := by
      constructor
      · intro hle; exact pow_le_pow_left₀ hε.le hle 2
      · intro hle
        have := Real.sqrt_le_sqrt hle
        rwa [Real.sqrt_sq hε.le, Real.sqrt_sq hnn] at this
    simp only [hiff]
  rw [hind]
  have hmk := expectHistory_indicator_le strat T []
    (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2)
    (fun _ => sq_nonneg _) (sq_pos_of_pos hε)
  have hsq := blackwell_expect_dist_sq_le hc hS hs₀ m hRnn hR strat adv hstep T hT
  calc expectHistory strat T []
        (fun h => if ε ^ 2 ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2 then 1 else 0)
      ≤ expectHistory strat T []
          (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2) / ε ^ 2 := hmk
    _ ≤ ((2 * R) ^ 2 / (T : ℝ)) / ε ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg ε)
    _ = (2 * R) ^ 2 / ((T : ℝ) * ε ^ 2) := by rw [div_div]

/-- A stationary feedback rule choosing mixed weights `prob y : I → ℝ` from the current running
average vector payoff `y : E`, independently of the adversary strategy. -/
structure FeedbackRule (I E : Type*) [Fintype I] where
  /-- Mixed action weights chosen given current running average vector payoff `y : E`. -/
  prob : E → I → ℝ
  /-- Every probability weight is nonnegative. -/
  nonneg : ∀ y i, 0 ≤ prob y i
  /-- Weights sum to `1` at every vector `y : E`. -/
  sum_eq_one : ∀ y, ∑ i, prob y i = 1

/-- Instantiate a feedback rule against a payoff matrix `m` and an adaptive adversary `adv`. -/
@[expose] noncomputable def FeedbackRule.toStrategy (rule : FeedbackRule I E)
    (m : I → J → E) (adv : List I → J) : ApproachStrategy I where
  prob h := rule.prob ((h.length : ℝ)⁻¹ • sumPayoff m adv h)
  nonneg _ i := rule.nonneg _ i
  sum_eq_one _ := rule.sum_eq_one _

/-- **Blackwell's approachability theorem (existence / sufficiency)** [Blackwell1956]:
for any nonempty complete convex set `S`, finite action game `m : I → J → E`, and `s₀ ∈ S` with
`‖m i j - s₀‖ ≤ R`, if `SatisfiesResponseCondition m S` holds, then there exists a single
adversary-independent feedback rule `rule : FeedbackRule I E` such that against *every* adaptive
adversary `adv : List I → J`, *every* horizon `T ≥ 1`, and *every* `ε > 0`:
* `⟪y - s, m(rule.prob y, j) - s⟫ ≤ 0` for all `y : E`, `j : J` (`s = metricProjection S y`),
* `𝔼[dist(x̄_T, S) ^ 2] ≤ (2 * R) ^ 2 / T`,
* `𝔼[dist(x̄_T, S)] ≤ 2 * R / √T`, and
* `Pr[dist(x̄_T, S) ≥ ε] ≤ (2 * R) ^ 2 / (T * ε ^ 2)`. -/
theorem exists_approachStrategy_of_response [Fintype J] [Nonempty I]
    {S : Set E} (hc : IsComplete S) (hS : Convex ℝ S) {s₀ : E} (hs₀ : s₀ ∈ S)
    (m : I → J → E) {R : ℝ} (hRnn : 0 ≤ R) (hR : ∀ i j, ‖m i j - s₀‖ ≤ R)
    (hresp : SatisfiesResponseCondition m S) :
    ∃ rule : FeedbackRule I E,
      (∀ y j,
        let s := metricProjection S y
        ⟪y - s, expectedPayoff m (rule.prob y) j - s⟫ ≤ 0) ∧
      ∀ (adv : List I → J) (T : ℕ), 0 < T →
        expectHistory (rule.toStrategy m adv) T []
            (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) ^ 2) ≤
          (2 * R) ^ 2 / (T : ℝ) ∧
        expectHistory (rule.toStrategy m adv) T []
            (fun h => distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h)) ≤
          2 * R / Real.sqrt T ∧
        ∀ ε : ℝ, 0 < ε →
          expectHistory (rule.toStrategy m adv) T []
              (fun h => if ε ≤ distToSet S ((T : ℝ)⁻¹ • sumPayoff m adv h) then (1 : ℝ) else 0) ≤
            (2 * R) ^ 2 / ((T : ℝ) * ε ^ 2) := by
  have hhalf := halfspace_of_response hresp
  have hchoice : ∀ y : E, ∃ p : I → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      ∀ j, ⟪y - metricProjection S y, expectedPayoff m p j - metricProjection S y⟫ ≤ 0 := by
    intro y
    set s := metricProjection S y
    have hsep : ∀ z ∈ S, ⟪y - s, z⟫ ≤ ⟪y - s, s⟫ := fun z hz => by
      have hvar := inner_sub_metricProjection_le_zero hc hS y hz
      rw [inner_sub_right] at hvar
      linarith
    obtain ⟨p, hp0, hp1, hp_le⟩ := hhalf (y - s) ⟪y - s, s⟫ hsep
    refine ⟨p, hp0, hp1, fun j => ?_⟩
    rw [inner_sub_right]
    linarith [hp_le j]
  classical
  let rule : FeedbackRule I E :=
    { prob := fun y => (hchoice y).choose
      nonneg := fun y => (hchoice y).choose_spec.1
      sum_eq_one := fun y => (hchoice y).choose_spec.2.1 }
  have hrule_step : ∀ y j,
      ⟪y - metricProjection S y, expectedPayoff m (rule.prob y) j - metricProjection S y⟫ ≤ 0 :=
    fun y j => (hchoice y).choose_spec.2.2 j
  refine ⟨rule, hrule_step, fun adv T hT => ?_⟩
  have hcond : ∀ (h : List I), 0 < h.length →
      let y := (h.length : ℝ)⁻¹ • sumPayoff m adv h
      let s := metricProjection S y
      ⟪y - s, expectedPayoff m ((rule.toStrategy m adv).prob h) (adv h) - s⟫ ≤ 0 :=
    fun h _ => hrule_step _ (adv h)
  exact ⟨blackwell_expect_dist_sq_le hc hS hs₀ m hRnn hR (rule.toStrategy m adv) adv hcond T hT,
    blackwell_expect_dist_le hc hS hs₀ m hRnn hR (rule.toStrategy m adv) adv hcond T hT,
    fun ε hε =>
      blackwell_prob_dist_ge_le hc hS hs₀ m hRnn hR (rule.toStrategy m adv) adv hcond T hT hε⟩

end AdaptiveRandomized

end Cslib.MachineLearning.OnlineLearning.Blackwell
