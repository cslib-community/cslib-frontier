/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Stochastic
public import CslibFrontier.MachineLearning.OnlineLearning.Blackwell
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regret matching via Blackwell approachability

Instantiates `CslibFrontier.MachineLearning.OnlineLearning.Blackwell` on the nonpositive orthant
`nonposOrthant ι = {x : EuclideanSpace ℝ ι | ∀ i, x i ≤ 0}` to derive the parameter-free,
horizon-independent **regret matching** algorithms of Hart and Mas-Colell [HartMasColell2000]:

1. **Nonpositive orthant geometry**: exact closed-form metric projection
   `metricProjection (nonposOrthant ι) x = min (x i) 0`, residual `(x i)⁺ = max (x i) 0`.
2. **External regret matching** (`extRegretMatchingProb`, `extRegretMatching_regret_le`):
   at round `t`, selects each action `i` proportional to its positive cumulative regret
   `max (R_t i) 0`. The Blackwell cone condition `⟪R_t⁺, v_t⟫ = 0 ≤ 0` holds identically, yielding
   external regret at most `B * √(|ι| * T)` for arbitrary losses with pairwise spread
   `|ℓ t i - ℓ t j| ≤ B` (with zero learning-rate parameter or horizon tuning).
3. **Internal / swap regret matching** (`swapRegretMatchingProb`,
   `swapRegretMatching_internal_regret_le`, `swapRegretMatching_swap_regret_le`): runs the Markov
   chain `regretMarkov` driven by the positive pairwise regret matrix `max (R_t a b) 0` and plays
   a stationary distribution via `Matrix.stationaryVec`. The resulting pairwise balance equation
   forces the Blackwell cone condition on `EuclideanSpace ℝ (ι × ι)` to vanish identically, giving:
   * **Internal regret**: `∑ t < T, p t a * (ℓ t a - ℓ t b) ≤ B * √(|ι| * T)` for all `a, b : ι`.
   * **Swap regret**: `∑ t < T, ∑ a, p t a * (ℓ t a - ℓ t (φ a)) ≤ B * |ι| * √T` for every swap
     map `φ : ι → ι`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Blackwell.nonposOrthant`: nonpositive orthant cone in
  `EuclideanSpace ℝ ι`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.extRegretWeights`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.extRegretMatchingState`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.extRegretMatchingProb`: external regret
  matching algorithm.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.regretMarkov`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.swapRegretMatchingState`,
  `Cslib.MachineLearning.OnlineLearning.Blackwell.swapRegretMatchingProb`: Hart–Mas-Colell
  internal/swap regret matching via stationary distributions of `regretMarkov`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Blackwell.metricProjection_nonposOrthant`: closed-form
  Euclidean projection `i ↦ min (x i) 0`.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.extRegretMatching_regret_le`: `B * √(|ι| * T)`
  external regret bound.
* `Cslib.MachineLearning.OnlineLearning.Blackwell.swapRegretMatching_internal_regret_le`:
  `B * √(|ι| * T)` pairwise internal regret bound [HartMasColell2000].
* `Cslib.MachineLearning.OnlineLearning.Blackwell.swapRegretMatching_swap_regret_le`:
  `B * |ι| * √T` swap regret bound against every modification map `φ : ι → ι` [HartMasColell2000].

## References

* [D. Blackwell, *An analog of the minimax theorem for vector payoffs*][Blackwell1956]
* [S. Hart and A. Mas-Colell, *A Simple Adaptive Procedure Leading to Correlated
  Equilibrium*][HartMasColell2000]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.Blackwell

section NonposOrthant

variable {ι : Type*} [Fintype ι]

/-- Nonpositive orthant `{x : EuclideanSpace ℝ ι | ∀ i, x i ≤ 0}`. -/
@[expose] def nonposOrthant (ι : Type*) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ≤ 0}

omit [Fintype ι] in
theorem zero_mem_nonposOrthant : (0 : EuclideanSpace ℝ ι) ∈ nonposOrthant ι :=
  fun _ => le_rfl

omit [Fintype ι] in
theorem nonposOrthant_convex : Convex ℝ (nonposOrthant ι) := by
  intro x hx y hy a b ha hb _ i
  simpa using add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx i))
    (mul_nonpos_of_nonneg_of_nonpos hb (hy i))

omit [Fintype ι] in
theorem nonposOrthant_isClosed : IsClosed (nonposOrthant ι) := by
  have h : nonposOrthant ι = ⋂ i : ι, {x : EuclideanSpace ℝ ι | x i ≤ 0} := by
    ext x; simp [nonposOrthant]
  rw [h]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact EuclideanSpace.proj i |>.continuous

omit [Fintype ι] in
theorem nonposOrthant_isComplete : IsComplete (nonposOrthant ι) :=
  nonposOrthant_isClosed.isComplete

/-- Closed-form Euclidean projection onto `nonposOrthant ι`: `(Π_S x) i = min (x i) 0`. -/
theorem metricProjection_nonposOrthant (x : EuclideanSpace ℝ ι) :
    metricProjection (nonposOrthant ι) x = WithLp.toLp 2 (fun i => min (x i) 0) := by
  rw [metricProjection_eq_iff nonposOrthant_isComplete nonposOrthant_convex
    (fun i => min_le_right _ _)]
  intro z hz
  rw [PiLp.inner_apply]
  refine sum_nonpos fun i _ => ?_
  have hz' : z i ≤ 0 := hz i
  simp only [PiLp.sub_apply, conj_trivial, mul_comm, RCLike.inner_apply]
  rcases le_total (x i) 0 with hxi | hxi
  · simp [min_eq_left hxi]
  · simp only [min_eq_right hxi, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hxi hz'

/-- Coordinate of the residual `x - metricProjection (nonposOrthant ι) x` equals `max (x i) 0`. -/
theorem sub_metricProjection_nonposOrthant_apply (x : EuclideanSpace ℝ ι) (i : ι) :
    (x - metricProjection (nonposOrthant ι) x) i = max (x i) 0 := by
  rw [metricProjection_nonposOrthant, PiLp.sub_apply]
  rcases le_total (x i) 0 with hxi | hxi
  · simp [min_eq_left hxi, max_eq_right hxi]
  · simp [min_eq_right hxi, max_eq_left hxi]

/-- Squared Euclidean distance to `nonposOrthant ι` equals `∑ i, max (x i) 0 ^ 2`. -/
theorem distToSet_nonposOrthant_sq (x : EuclideanSpace ℝ ι) :
    distToSet (nonposOrthant ι) x ^ 2 = ∑ i : ι, max (x i) 0 ^ 2 := by
  rw [distToSet, ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [sub_metricProjection_nonposOrthant_apply, RCLike.inner_apply, conj_trivial, sq]

/-- Each positive part `max (x i) 0` is bounded by `distToSet (nonposOrthant ι) x`. -/
theorem max_le_distToSet_nonposOrthant (x : EuclideanSpace ℝ ι) (i : ι) :
    max (x i) 0 ≤ distToSet (nonposOrthant ι) x := by
  have hsq : max (x i) 0 ^ 2 ≤ distToSet (nonposOrthant ι) x ^ 2 := by
    rw [distToSet_nonposOrthant_sq]
    exact Finset.single_le_sum (f := fun j => max (x j) 0 ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (le_max_right _ _), Real.sqrt_sq (distToSet_nonposOrthant_nonneg x)] at hs
where
  distToSet_nonposOrthant_nonneg (y : EuclideanSpace ℝ ι) :
      0 ≤ distToSet (nonposOrthant ι) y := distToSet_nonneg _ _

end NonposOrthant

section ExternalRegretMatching

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Normalize the positive parts `max (r i) 0` of a regret vector `r : ι → ℝ` into a probability
distribution on `ι` (falling back to the uniform distribution when all coordinates are `≤ 0`). -/
@[expose] noncomputable def extRegretWeights (r : ι → ℝ) (i : ι) : ℝ :=
  let s := ∑ k : ι, max (r k) 0
  if s = 0 then (Fintype.card ι : ℝ)⁻¹ else max (r i) 0 / s

theorem extRegretWeights_nonneg (r : ι → ℝ) (i : ι) : 0 ≤ extRegretWeights r i := by
  dsimp only [extRegretWeights]
  split_ifs
  · positivity
  · exact div_nonneg (le_max_right _ _) (sum_nonneg fun _ _ => le_max_right _ _)

theorem sum_extRegretWeights (r : ι → ℝ) : ∑ i : ι, extRegretWeights r i = 1 := by
  dsimp only [extRegretWeights]
  split_ifs with h
  · have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]
  · rw [← sum_div, div_self h]

omit [Nonempty ι] in
/-- Fundamental orthogonality of external regret matching: for *every* loss vector `ℓ : ι → ℝ` and
*every* cumulative regret vector `r : ι → ℝ`,
`∑ k, max (r k) 0 * (∑ i, extRegretWeights r i * ℓ i - ℓ k) = 0`. -/
theorem extRegretWeights_inner_eq_zero (r ℓ : ι → ℝ) :
    ∑ k : ι, max (r k) 0 * (∑ i : ι, extRegretWeights r i * ℓ i - ℓ k) = 0 := by
  by_cases hs : ∑ k : ι, max (r k) 0 = 0
  · have hzero : ∀ k : ι, max (r k) 0 = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => le_max_right (r j) 0).mp hs k (mem_univ k)
    simp [hzero]
  · have hmul : ∑ i : ι, extRegretWeights r i * ℓ i =
        (∑ i : ι, max (r i) 0 * ℓ i) / ∑ k : ι, max (r k) 0 := by
      simp only [extRegretWeights, hs, ↓reduceIte]
      rw [sum_div]
      refine sum_congr rfl fun i _ => by ring
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hmul]
    rw [mul_div_cancel₀ _ hs, sub_self]

/-- Cumulative external regret vector maintained by **external regret matching** after `t` rounds
of loss vectors `ℓ : ℕ → ι → ℝ`. -/
@[expose] noncomputable def extRegretMatchingState (ℓ : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 0
  | t + 1 =>
    let r := extRegretMatchingState ℓ t
    let p := extRegretWeights r
    fun k => r k + (∑ i : ι, p i * ℓ t i - ℓ t k)

/-- Round-`t` mixed action distribution played by **external regret matching** (depends strictly on
losses `ℓ s` for `s < t`). -/
@[expose] noncomputable def extRegretMatchingProb (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  extRegretWeights (extRegretMatchingState ℓ t)

theorem extRegretMatchingProb_nonneg (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ extRegretMatchingProb ℓ t i :=
  extRegretWeights_nonneg _ i

theorem sum_extRegretMatchingProb (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i : ι, extRegretMatchingProb ℓ t i = 1 :=
  sum_extRegretWeights _

omit [Nonempty ι] in
theorem extRegretMatchingState_eq_sum (ℓ : ℕ → ι → ℝ) (t : ℕ) (k : ι) :
    extRegretMatchingState ℓ t k =
      ∑ s ∈ range t, (∑ i : ι, extRegretMatchingProb ℓ s i * ℓ s i - ℓ s k) := by
  induction t with
  | zero => simp [extRegretMatchingState]
  | succ t ih =>
    rw [sum_range_succ, ← ih]
    rfl

omit [Nonempty ι] in
/-- Causality of external regret matching: `extRegretMatchingProb ℓ t` depends only on `ℓ s` for
`s < t`. -/
theorem extRegretMatchingProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    extRegretMatchingProb ℓ t = extRegretMatchingProb ℓ' t := by
  suffices hs : extRegretMatchingState ℓ t = extRegretMatchingState ℓ' t by
    simp [extRegretMatchingProb, hs]
  induction t with
  | zero => rfl
  | succ t ih =>
    have iht := ih fun s hs => h s (lt_trans hs (Nat.lt_succ_self t))
    have ht : ℓ t = ℓ' t := h t (Nat.lt_succ_self t)
    funext k
    simp only [extRegretMatchingState, iht, ht]

/-- **External regret bound for regret matching** [HartMasColell2000]: against any bounded loss
sequence `|ℓ t i - ℓ t j| ≤ B` (`0 ≤ B`), parameter-free, horizon-independent regret matching
incurs external regret at most `B * √(|ι| * T)` after *every* horizon `T : ℕ`. -/
theorem extRegretMatching_regret_le (ℓ : ℕ → ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hspread : ∀ t i j, |ℓ t i - ℓ t j| ≤ B) (k : ι) (T : ℕ) :
    ∑ t ∈ range T, (∑ i : ι, extRegretMatchingProb ℓ t i * ℓ t i - ℓ t k) ≤
      B * Real.sqrt ((Fintype.card ι : ℝ) * (T : ℝ)) := by
  let v : ℕ → EuclideanSpace ℝ ι := fun t =>
    WithLp.toLp 2 fun j => ∑ i : ι, extRegretMatchingProb ℓ t i * ℓ t i - ℓ t j
  have hsum_apply : ∀ (n : ℕ) (j : ι),
      (∑ s ∈ range n, v s) j = extRegretMatchingState ℓ n j := by
    intro n j
    rw [extRegretMatchingState_eq_sum]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ, PiLp.add_apply, ih]
  have hcone := blackwell_cone_dist_le nonposOrthant_isComplete nonposOrthant_convex
    zero_mem_nonposOrthant (v := v) (R := B * Real.sqrt (Fintype.card ι)) (by positivity) T
    (fun t _ => ?_) (fun t _ => ?_)
  · have hcoord : extRegretMatchingState ℓ T k ≤ max ((∑ s ∈ range T, v s) k) 0 := by
      rw [hsum_apply T k]
      exact le_max_left _ _
    have hle := hcoord.trans ((max_le_distToSet_nonposOrthant _ k).trans hcone)
    rw [extRegretMatchingState_eq_sum] at hle
    refine hle.trans_eq ?_
    rw [mul_assoc, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  · have hsq : ‖v t‖ ^ 2 ≤ (B * Real.sqrt (Fintype.card ι)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      have hcoord_bd : ∀ j : ι,
          |∑ i : ι, extRegretMatchingProb ℓ t i * ℓ t i - ℓ t j| ≤ B := fun j => by
        have hdiff : ∑ i : ι, extRegretMatchingProb ℓ t i * ℓ t i - ℓ t j =
            ∑ i : ι, extRegretMatchingProb ℓ t i * (ℓ t i - ℓ t j) := by
          simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_extRegretMatchingProb, one_mul]
        rw [hdiff]
        calc |∑ i : ι, extRegretMatchingProb ℓ t i * (ℓ t i - ℓ t j)|
            ≤ ∑ i : ι, |extRegretMatchingProb ℓ t i * (ℓ t i - ℓ t j)| := abs_sum_le_sum_abs ..
          _ = ∑ i : ι, extRegretMatchingProb ℓ t i * |ℓ t i - ℓ t j| := by
              refine sum_congr rfl fun i _ => ?_
              rw [abs_mul, abs_of_nonneg (extRegretMatchingProb_nonneg ℓ t i)]
          _ ≤ ∑ i : ι, extRegretMatchingProb ℓ t i * B :=
              sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hspread t i j)
                (extRegretMatchingProb_nonneg ℓ t i)
          _ = B := by rw [← sum_mul, sum_extRegretMatchingProb, one_mul]
      calc ∑ j : ι, ⟪(v t) j, (v t) j⟫
          = ∑ j : ι, ((v t) j) ^ 2 := by
            refine sum_congr rfl fun j _ => by rw [RCLike.inner_apply, conj_trivial, sq]
        _ ≤ ∑ _j : ι, B ^ 2 := sum_le_sum fun j _ => by
            have := hcoord_bd j
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = B ^ 2 * (Fintype.card ι : ℝ) := by simp [nsmul_eq_mul, mul_comm]
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hs
  · dsimp only
    rw [PiLp.inner_apply]
    have hinner := extRegretWeights_inner_eq_zero (extRegretMatchingState ℓ t) (ℓ t)
    have hcomm : ∑ j : ι, ⟪(∑ s ∈ range t, v s -
          metricProjection (nonposOrthant ι) (∑ s ∈ range t, v s)) j, (v t) j⟫ =
        ∑ j : ι, max (extRegretMatchingState ℓ t j) 0 *
          (∑ i : ι, extRegretMatchingProb ℓ t i * ℓ t i - ℓ t j) := by
      refine sum_congr rfl fun j _ => ?_
      rw [sub_metricProjection_nonposOrthant_apply, hsum_apply t j, RCLike.inner_apply,
        conj_trivial, mul_comm]
    rw [hcomm]
    exact le_of_eq hinner

end ExternalRegretMatching

section SwapRegretMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Row-stochastic Markov matrix associated with a pairwise regret table `R : ι → ι → ℝ`:
setting `w a b = max (R a b) 0` and normalizer `s = 1 + ∑ a, ∑ b, w a b > 0`, off-diagonal
entries are `w a b / s` and diagonal entries absorb `1 - ∑_{c ≠ a} w a c / s`. -/
@[expose] noncomputable def regretMarkov (R : ι → ι → ℝ) : Matrix ι ι ℝ :=
  let s : ℝ := 1 + ∑ a : ι, ∑ b : ι, max (R a b) 0
  Matrix.of fun a b =>
    if b = a then 1 - (∑ c ∈ univ.erase a, max (R a c) 0) / s else max (R a b) 0 / s

omit [DecidableEq ι] [Nonempty ι] in
private theorem regretMarkov_scale_pos (R : ι → ι → ℝ) :
    0 < 1 + ∑ a : ι, ∑ b : ι, max (R a b) 0 := by
  have hnn : 0 ≤ ∑ a : ι, ∑ b : ι, max (R a b) 0 :=
    sum_nonneg fun a _ => sum_nonneg fun b _ => le_max_right _ _
  linarith

omit [Nonempty ι] in
theorem regretMarkov_mem_rowStochastic (R : ι → ι → ℝ) :
    regretMarkov R ∈ Matrix.rowStochastic ℝ ι := by
  set s : ℝ := 1 + ∑ a : ι, ∑ b : ι, max (R a b) 0
  have hs : 0 < s := regretMarkov_scale_pos R
  refine ⟨fun a b => ?_, funext fun a => ?_⟩
  · dsimp only [regretMarkov, Matrix.of_apply]
    split_ifs with hba
    · have hrow : ∑ c ∈ univ.erase a, max (R a c) 0 ≤ s := by
        have h1 : ∑ c ∈ univ.erase a, max (R a c) 0 ≤ ∑ c : ι, max (R a c) 0 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => le_max_right _ _
        have h2 : ∑ c : ι, max (R a c) 0 ≤ ∑ x : ι, ∑ c : ι, max (R x c) 0 :=
          Finset.single_le_sum (f := fun x => ∑ c : ι, max (R x c) 0)
            (fun x _ => sum_nonneg fun c _ => le_max_right _ _) (mem_univ a)
        linarith
      rw [sub_nonneg, div_le_one hs]
      exact hrow
    · exact div_nonneg (le_max_right _ _) hs.le
  · simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
    rw [← Finset.add_sum_erase _ _ (mem_univ a)]
    have hdiag : regretMarkov R a a = 1 - (∑ c ∈ univ.erase a, max (R a c) 0) / s := by
      simp [regretMarkov, s]
    have hoff : ∑ b ∈ univ.erase a, regretMarkov R a b =
        (∑ c ∈ univ.erase a, max (R a c) 0) / s := by
      rw [sum_div]
      refine sum_congr rfl fun b hb => ?_
      simp [regretMarkov, s, ne_of_mem_erase hb]
    rw [hdiag, hoff]
    ring

/-- Stationary probability vector of `regretMarkov R`, satisfying the exact pairwise balance
identity `∑ a, p a * max (R a k) 0 = p k * ∑ b, max (R k b) 0` [HartMasColell2000]. -/
@[expose] noncomputable def regretMarkovStationary (R : ι → ι → ℝ) : ι → ℝ :=
  Matrix.stationaryVec (regretMarkov R)

theorem regretMarkovStationary_nonneg (R : ι → ι → ℝ) (i : ι) :
    0 ≤ regretMarkovStationary R i :=
  Matrix.stationaryVec_nonneg (regretMarkov_mem_rowStochastic R) i

theorem sum_regretMarkovStationary (R : ι → ι → ℝ) :
    ∑ i : ι, regretMarkovStationary R i = 1 :=
  Matrix.sum_stationaryVec (regretMarkov_mem_rowStochastic R)

/-- Exact flow-balance identity of Hart–Mas-Colell regret matching: for every `k : ι`,
`∑ a, p a * max (R a k) 0 = p k * ∑ b, max (R k b) 0`. -/
theorem regretMarkovStationary_balance (R : ι → ι → ℝ) (k : ι) :
    ∑ a : ι, regretMarkovStationary R a * max (R a k) 0 =
      regretMarkovStationary R k * ∑ b : ι, max (R k b) 0 := by
  set p := regretMarkovStationary R
  set s : ℝ := 1 + ∑ a : ι, ∑ b : ι, max (R a b) 0
  have hs : 0 < s := regretMarkov_scale_pos R
  have hstat : ∑ a : ι, p a * regretMarkov R a k = p k := by
    have h := congrFun (Matrix.stationaryVec_vecMul (regretMarkov_mem_rowStochastic R)) k
    simpa [Matrix.vecMul, dotProduct, p, regretMarkovStationary] using h
  rw [← Finset.add_sum_erase _ _ (mem_univ k)] at hstat
  have hdiag : regretMarkov R k k = 1 - (∑ c ∈ univ.erase k, max (R k c) 0) / s := by
    simp [regretMarkov, s]
  have hoff : ∑ a ∈ univ.erase k, p a * regretMarkov R a k =
      (∑ a ∈ univ.erase k, p a * max (R a k) 0) / s := by
    rw [sum_div]
    refine sum_congr rfl fun a ha => ?_
    have hka : k ≠ a := (ne_of_mem_erase ha).symm
    simp only [regretMarkov, Matrix.of_apply, hka, ↓reduceIte]
    ring
  rw [hdiag, hoff] at hstat
  have herase : ∑ a ∈ univ.erase k, p a * max (R a k) 0 =
      p k * ∑ c ∈ univ.erase k, max (R k c) 0 := by
    have hdiv : (∑ a ∈ univ.erase k, p a * max (R a k) 0) / s =
        p k * (∑ c ∈ univ.erase k, max (R k c) 0) / s := by
      rw [mul_sub, mul_one, ← mul_div_assoc] at hstat
      linarith
    have hm := congrArg (· * s) hdiv
    rwa [div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne'] at hm
  rw [← Finset.add_sum_erase _ _ (mem_univ k),
    ← Finset.add_sum_erase _ (fun b => max (R k b) 0) (mem_univ k), mul_add, herase]

/-- Pairwise Blackwell orthogonality for Hart–Mas-Colell swap regret matching:
`∑ a, ∑ b, max (R a b) 0 * (p a * (ℓ a - ℓ b)) = 0`. -/
theorem regretMarkovStationary_inner_eq_zero (R : ι → ι → ℝ) (ℓ : ι → ℝ) :
    ∑ a : ι, ∑ b : ι, max (R a b) 0 * (regretMarkovStationary R a * (ℓ a - ℓ b)) = 0 := by
  set p := regretMarkovStationary R
  have hsplit : ∑ a : ι, ∑ b : ι, max (R a b) 0 * (p a * (ℓ a - ℓ b)) =
      (∑ a : ι, p a * (∑ b : ι, max (R a b) 0) * ℓ a) -
        (∑ b : ι, (∑ a : ι, p a * max (R a b) 0) * ℓ b) := by
    have h1 : ∀ a : ι, ∑ b : ι, max (R a b) 0 * (p a * (ℓ a - ℓ b)) =
        (∑ b : ι, max (R a b) 0 * p a * ℓ a) - ∑ b : ι, max (R a b) 0 * p a * ℓ b := fun a => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun b _ => by ring
    simp_rw [h1, sum_sub_distrib]
    congr 1
    · refine sum_congr rfl fun a _ => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun b _ => by ring
    · rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun a _ => by ring
  rw [hsplit]
  have hbal : ∑ b : ι, (∑ a : ι, p a * max (R a b) 0) * ℓ b =
      ∑ k : ι, p k * (∑ b : ι, max (R k b) 0) * ℓ k :=
    sum_congr rfl fun k _ => by rw [regretMarkovStationary_balance]
  rw [hbal, sub_self]

/-- Cumulative pairwise internal regret table maintained by **Hart–Mas-Colell regret matching**. -/
@[expose] noncomputable def swapRegretMatchingState (ℓ : ℕ → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => fun _ _ => 0
  | t + 1 =>
    let R := swapRegretMatchingState ℓ t
    let p := regretMarkovStationary R
    fun a b => R a b + p a * (ℓ t a - ℓ t b)

/-- Round-`t` mixed action distribution played by **Hart–Mas-Colell swap regret matching** (depends
only on losses `ℓ s` for `s < t`). -/
@[expose] noncomputable def swapRegretMatchingProb (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  regretMarkovStationary (swapRegretMatchingState ℓ t)

theorem swapRegretMatchingProb_nonneg (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ swapRegretMatchingProb ℓ t i :=
  regretMarkovStationary_nonneg _ i

theorem sum_swapRegretMatchingProb (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i : ι, swapRegretMatchingProb ℓ t i = 1 :=
  sum_regretMarkovStationary _

omit [Nonempty ι] in
theorem swapRegretMatchingState_eq_sum (ℓ : ℕ → ι → ℝ) (t : ℕ) (a b : ι) :
    swapRegretMatchingState ℓ t a b =
      ∑ s ∈ range t, swapRegretMatchingProb ℓ s a * (ℓ s a - ℓ s b) := by
  induction t with
  | zero => simp [swapRegretMatchingState]
  | succ t ih =>
    rw [sum_range_succ, ← ih]
    rfl

omit [Nonempty ι] in
/-- Causality: `swapRegretMatchingProb ℓ t` depends strictly on `ℓ s` for `s < t`. -/
theorem swapRegretMatchingProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    swapRegretMatchingProb ℓ t = swapRegretMatchingProb ℓ' t := by
  suffices hs : swapRegretMatchingState ℓ t = swapRegretMatchingState ℓ' t by
    simp [swapRegretMatchingProb, hs]
  induction t with
  | zero => rfl
  | succ t ih =>
    have iht := ih fun s hs => h s (lt_trans hs (Nat.lt_succ_self t))
    have ht : ℓ t = ℓ' t := h t (Nat.lt_succ_self t)
    funext a b
    simp only [swapRegretMatchingState, iht, ht]

/-- Core Euclidean `L²` positive pairwise regret norm bound
`∑ a, ∑ b, max (R_T a b) 0 ^ 2 ≤ B ^ 2 * |ι| * T`. -/
private theorem sum_swapRegretMatching_pos_sq_le (ℓ : ℕ → ι → ℝ) {B : ℝ}
    (hspread : ∀ t i j, |ℓ t i - ℓ t j| ≤ B) (T : ℕ) :
    ∑ a : ι, ∑ b : ι, max (swapRegretMatchingState ℓ T a b) 0 ^ 2 ≤
      B ^ 2 * (Fintype.card ι : ℝ) * (T : ℝ) := by
  let v : ℕ → EuclideanSpace ℝ (ι × ι) := fun t =>
    WithLp.toLp 2 fun ab => swapRegretMatchingProb ℓ t ab.1 * (ℓ t ab.1 - ℓ t ab.2)
  have hsum_apply : ∀ (n : ℕ) (ab : ι × ι),
      (∑ s ∈ range n, v s) ab = swapRegretMatchingState ℓ n ab.1 ab.2 := by
    intro n ab
    rw [swapRegretMatchingState_eq_sum]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ, PiLp.add_apply, ih]
  have hcone := blackwell_cone_dist_sq_le_sum nonposOrthant_isComplete nonposOrthant_convex
    zero_mem_nonposOrthant v T (fun t _ => ?_)
  · have hL : distToSet (nonposOrthant (ι × ι)) (∑ s ∈ range T, v s) ^ 2 =
        ∑ a : ι, ∑ b : ι, max (swapRegretMatchingState ℓ T a b) 0 ^ 2 := by
      rw [distToSet_nonposOrthant_sq, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hsum_apply T (a, b)]
    have hR : ∑ t ∈ range T, ‖v t‖ ^ 2 ≤ B ^ 2 * (Fintype.card ι : ℝ) * (T : ℝ) := by
      calc ∑ t ∈ range T, ‖v t‖ ^ 2
          ≤ ∑ _t ∈ range T, B ^ 2 * (Fintype.card ι : ℝ) := by
            refine sum_le_sum fun t _ => ?_
            rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fintype.sum_prod_type]
            have hterm : ∀ a : ι,
                ∑ b : ι, ⟪(v t) (a, b), (v t) (a, b)⟫ ≤
                  swapRegretMatchingProb ℓ t a ^ 2 * (B ^ 2 * (Fintype.card ι : ℝ)) := by
              intro a
              calc ∑ b : ι, ⟪(v t) (a, b), (v t) (a, b)⟫
                  = ∑ b : ι, swapRegretMatchingProb ℓ t a ^ 2 * (ℓ t a - ℓ t b) ^ 2 := by
                    refine sum_congr rfl fun b _ => ?_
                    rw [RCLike.inner_apply, conj_trivial]
                    dsimp only [v]
                    ring
                _ ≤ ∑ _b : ι, swapRegretMatchingProb ℓ t a ^ 2 * B ^ 2 :=
                    sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
                      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hspread t a b) 2)
                      (sq_nonneg _)
                _ = swapRegretMatchingProb ℓ t a ^ 2 * (B ^ 2 * (Fintype.card ι : ℝ)) := by
                    simp [nsmul_eq_mul]; ring
            have hpsq : ∑ a : ι, swapRegretMatchingProb ℓ t a ^ 2 ≤ 1 := by
              calc ∑ a : ι, swapRegretMatchingProb ℓ t a ^ 2
                  ≤ ∑ a : ι, swapRegretMatchingProb ℓ t a := sum_le_sum fun a _ => by
                    have h0 := swapRegretMatchingProb_nonneg ℓ t a
                    have h1 : swapRegretMatchingProb ℓ t a ≤ 1 := by
                      have := Finset.single_le_sum
                        (fun x _ => swapRegretMatchingProb_nonneg ℓ t x) (mem_univ a)
                      linarith [sum_swapRegretMatchingProb ℓ t]
                    nlinarith
                _ = 1 := sum_swapRegretMatchingProb ℓ t
            calc ∑ a : ι, ∑ b : ι, ⟪(v t) (a, b), (v t) (a, b)⟫
                ≤ ∑ a : ι, swapRegretMatchingProb ℓ t a ^ 2 * (B ^ 2 * (Fintype.card ι : ℝ)) :=
                  sum_le_sum fun a _ => hterm a
              _ = (∑ a : ι, swapRegretMatchingProb ℓ t a ^ 2) * (B ^ 2 * (Fintype.card ι : ℝ)) :=
                  (sum_mul ..).symm
              _ ≤ 1 * (B ^ 2 * (Fintype.card ι : ℝ)) :=
                  mul_le_mul_of_nonneg_right hpsq (by positivity)
              _ = B ^ 2 * (Fintype.card ι : ℝ) := one_mul _
        _ = B ^ 2 * (Fintype.card ι : ℝ) * (T : ℝ) := by simp [nsmul_eq_mul, mul_comm]
    exact hL ▸ hcone.trans hR
  · dsimp only
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    have hcomm : ∑ a : ι, ∑ b : ι,
        ⟪(∑ s ∈ range t, v s - metricProjection (nonposOrthant (ι × ι)) (∑ s ∈ range t, v s))
          (a, b), (v t) (a, b)⟫ =
        ∑ a : ι, ∑ b : ι, max (swapRegretMatchingState ℓ t a b) 0 *
          (swapRegretMatchingProb ℓ t a * (ℓ t a - ℓ t b)) := by
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [sub_metricProjection_nonposOrthant_apply, hsum_apply t (a, b), RCLike.inner_apply,
        conj_trivial, mul_comm]
    rw [hcomm]
    exact le_of_eq (regretMarkovStationary_inner_eq_zero (swapRegretMatchingState ℓ t) (ℓ t))

/-- **Pairwise internal regret bound for Hart–Mas-Colell regret matching** [HartMasColell2000]:
for every pair of actions `a, b : ι` and every horizon `T : ℕ`,
`∑ t < T, p t a * (ℓ t a - ℓ t b) ≤ B * √(|ι| * T)`. -/
theorem swapRegretMatching_internal_regret_le (ℓ : ℕ → ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hspread : ∀ t i j, |ℓ t i - ℓ t j| ≤ B) (a b : ι) (T : ℕ) :
    ∑ t ∈ range T, swapRegretMatchingProb ℓ t a * (ℓ t a - ℓ t b) ≤
      B * Real.sqrt ((Fintype.card ι : ℝ) * (T : ℝ)) := by
  have h1 := sum_swapRegretMatching_pos_sq_le ℓ hspread T
  have hsingle : max (swapRegretMatchingState ℓ T a b) 0 ^ 2 ≤
      ∑ x : ι, ∑ y : ι, max (swapRegretMatchingState ℓ T x y) 0 ^ 2 := by
    have hrow : max (swapRegretMatchingState ℓ T a b) 0 ^ 2 ≤
        ∑ y : ι, max (swapRegretMatchingState ℓ T a y) 0 ^ 2 :=
      Finset.single_le_sum (f := fun y => max (swapRegretMatchingState ℓ T a y) 0 ^ 2)
        (fun _ _ => sq_nonneg _) (mem_univ b)
    exact hrow.trans (Finset.single_le_sum
      (f := fun x => ∑ y : ι, max (swapRegretMatchingState ℓ T x y) 0 ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ a))
  have hsq : max (swapRegretMatchingState ℓ T a b) 0 ^ 2 ≤
      (B * Real.sqrt ((Fintype.card ι : ℝ) * (T : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    linarith [hsingle, h1]
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (le_max_right _ _), Real.sqrt_sq (by positivity)] at hs
  rw [← swapRegretMatchingState_eq_sum]
  exact (le_max_left _ _).trans hs

/-- **Swap regret bound for Hart–Mas-Colell regret matching** [HartMasColell2000]: against *every*
modification rule `φ : ι → ι` and *every* horizon `T : ℕ`,
`∑ t < T, ∑ a, p t a * (ℓ t a - ℓ t (φ a)) ≤ B * |ι| * √T`. -/
theorem swapRegretMatching_swap_regret_le (ℓ : ℕ → ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hspread : ∀ t i j, |ℓ t i - ℓ t j| ≤ B) (φ : ι → ι) (T : ℕ) :
    ∑ t ∈ range T, ∑ a : ι, swapRegretMatchingProb ℓ t a * (ℓ t a - ℓ t (φ a)) ≤
      B * (Fintype.card ι : ℝ) * Real.sqrt T := by
  rw [sum_comm]
  have hle : ∑ a : ι, ∑ t ∈ range T, swapRegretMatchingProb ℓ t a * (ℓ t a - ℓ t (φ a)) ≤
      ∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0 := by
    refine sum_le_sum fun a _ => ?_
    rw [← swapRegretMatchingState_eq_sum]
    exact le_max_left _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun a => max (swapRegretMatchingState ℓ T a (φ a)) 0)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  have hsum_sq : ∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0 ^ 2 ≤
      ∑ a : ι, ∑ b : ι, max (swapRegretMatchingState ℓ T a b) 0 ^ 2 :=
    sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => max (swapRegretMatchingState ℓ T a b) 0 ^ 2)
        (fun _ _ => sq_nonneg _) (mem_univ (φ a))
  have hbd := sum_swapRegretMatching_pos_sq_le ℓ hspread T
  have hcomb : (∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0) ^ 2 ≤
      (B * (Fintype.card ι : ℝ) * Real.sqrt T) ^ 2 := by
    calc (∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0) ^ 2
        ≤ (Fintype.card ι : ℝ) * ∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0 ^ 2 := hcs
      _ ≤ (Fintype.card ι : ℝ) * ∑ a : ι, ∑ b : ι, max (swapRegretMatchingState ℓ T a b) 0 ^ 2 :=
          mul_le_mul_of_nonneg_left hsum_sq (Nat.cast_nonneg _)
      _ ≤ (Fintype.card ι : ℝ) * (B ^ 2 * (Fintype.card ι : ℝ) * (T : ℝ)) :=
          mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg _)
      _ = (B * (Fintype.card ι : ℝ) * Real.sqrt T) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
          ring
  have hnn : 0 ≤ ∑ a : ι, max (swapRegretMatchingState ℓ T a (φ a)) 0 :=
    sum_nonneg fun _ _ => le_max_right _ _
  have hs := Real.sqrt_le_sqrt hcomb
  rw [Real.sqrt_sq hnn, Real.sqrt_sq (by positivity)] at hs
  exact hle.trans hs

end SwapRegretMatching

end Cslib.MachineLearning.OnlineLearning.Blackwell
