/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
public import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Internal regret, nonpositive-orthant projection, and Blackwell–Hart–Mas-Colell regret-matching

This module formalizes **internal regret**, its quantitative relationship with external and swap
regret ([BlumMansour2007AGT] §§4.2, 4.4 and Exercise 4.1), the **Euclidean metric projection** onto
the nonpositive orthant with **Blackwell's quadratic potential bound** ([Blackwell1956];
[HartMasColell2000] §3, Figure 2, pp. 1135–1138 and Appendix Step M1, p. 1146), and the resulting
horizon-free, parameter-free **`O(√T)` external and internal/swap regret-matching algorithms**
([HartMasColell2000] Theorem A, eqs. `(3.1)`–`(3.5)`, pp. 1133–1138, and Theorem B, eqs.
`(4.2a)`–`(4.2b)`, p. 1139):

1. **External, internal, and swap regret functionals**: for an action sequence `p : ℕ → ι → ℝ` and
   loss sequence `ℓ : ℕ → ι → ℝ` over `T` rounds, `pairInternalRegret p ℓ T j k` measures the cost
   saved by replacing action `j` with `k` (`switchAction j k`), `swapRegretOf p ℓ T δ` measures the
   cost saved by an arbitrary modification rule `δ : ι → ι`, and `externalRegretOf p ℓ T k`
   compares against the constant action `k`. Swap regret decomposes as
   `∑ j, pairInternalRegret p ℓ T j (δ j)`, bounding both internal regret (`δ = switchAction j k`)
   and external regret (`δ = fun _ => k`), while internal regret at most `R` bounds swap regret by
   `|ι| * R` ([BlumMansour2007AGT] Exercise 4.1).
2. **Euclidean projection onto `ℝ_{\le 0}^L` and Blackwell's potential**: reusing
   `Cslib.metricProjection` from
   `CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection`,
   the nearest point of `nonposOrthant L = {z : EuclideanSpace ℝ L | ∀ l, z l ≤ 0}` to `y` is
   `l ↦ min 0 (y l)` (`metricProjection_nonposOrthant`, Figure 2 of [HartMasColell2000], p. 1137),
   with squared residual norm `∑ l, max 0 (y l) ^ 2`. Whenever an instantaneous vector sequence
   `r : ℕ → L → ℝ` satisfies the **Blackwell halfspace condition**
   `∑ l, max 0 (∑ s < t, r s l) * r t l ≤ 0` for all `t < T`, the squared Euclidean distance of
   `∑ t < T, r t` to `nonposOrthant L` is at most `∑ t < T, ∑ l, r t l ^ 2`
   (`blackwell_orthant_potential_le`).
3. **Blackwell external regret-matching (`regretMatchingProb`)**: playing `p_t(a) ∝ [R_t(a)]_+`
   (and uniformly when no positive regrets exist; [HartMasColell2000] eq. `(4.2b)`, p. 1139)
   satisfies the Blackwell condition with equality in every round without any learning-rate or
   horizon parameter, yielding `externalRegretOf (regretMatchingProb ℓ) ℓ T k ≤ B √(|ι| T)`
   whenever pairwise loss differences are bounded by `B` (`regretMatching_externalRegret_le`).
4. **Hart–Mas-Colell stationary internal regret-matching (`internalRegretMatchingProb`)**: playing
   a stationary distribution (`Matrix.stationaryVec`) of the positive-diagonal inertial transition
   matrix built from positive pairwise regrets ([HartMasColell2000] eqs. `(2.2)` and `(3.1)`,
   Theorem A, pp. 1130–1138) satisfies balance equation `(3.1)` and the Blackwell condition on
   `ι × ι` with equality, guaranteeing anytime internal regret at most `B √((|ι| - 1) T)`
   (`internalRegretMatching_pairInternalRegret_le`) and swap regret at most
   `B √(|ι| (|ι| - 1) T)` (`internalRegretMatching_swapRegret_le`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.switchAction`: the single-pair modification rule
  mapping `j` to `k` and fixing all other actions ([BlumMansour2007AGT] §4.4).
* `Cslib.MachineLearning.OnlineLearning.Experts.pairInternalRegret`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegretOf`,
  `Cslib.MachineLearning.OnlineLearning.Experts.externalRegretOf`: cumulative internal, swap, and
  external regret over `T` rounds.
* `Cslib.MachineLearning.OnlineLearning.Experts.nonposOrthant`: the closed convex cone
  `{z : EuclideanSpace ℝ L | ∀ l, z l ≤ 0}`.
* `Cslib.MachineLearning.OnlineLearning.Experts.regretMatchingStep`,
  `Cslib.MachineLearning.OnlineLearning.Experts.regretMatchingProb`: Blackwell's parameter-free
  external regret-matching learner (`p_t(a) ∝ [R_t(a)]_+`).
* `Cslib.MachineLearning.OnlineLearning.Experts.internalRegretTransition`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRegretMatchingProb`: Hart and Mas-Colell's
  inertial regret-transition matrix and its stationary internal regret-matching learner.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.swapRegretOf_eq_sum_pairInternalRegret`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegretOf_switchAction`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegretOf_const`,
  `Cslib.MachineLearning.OnlineLearning.Experts.swapRegretOf_le_card_mul_of_pairInternalRegret_le`:
  exact relationships among external, internal, and swap regret ([BlumMansour2007AGT] §4.2 and
  Exercise 4.1).
* `Cslib.MachineLearning.OnlineLearning.Experts.metricProjection_nonposOrthant`,
  `Cslib.MachineLearning.OnlineLearning.Experts.blackwell_orthant_potential_le`: Euclidean
  projection onto `ℝ_{\le 0}^L` and Blackwell's quadratic potential bound ([HartMasColell2000] §3,
  Figure 2, and Step M1).
* `Cslib.MachineLearning.OnlineLearning.Experts.regretMatching_externalRegret_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.regretMatching_externalRegret_le_of_mem_Icc`,
  `Cslib.MachineLearning.OnlineLearning.Experts.regretMatching_externalRegret_le_of_abs_le`:
  anytime `O(√T)` external-regret bounds for `regretMatchingProb` ([HartMasColell2000] Theorem B).
* `Cslib.MachineLearning.OnlineLearning.Experts.sum_mul_internalRegretTransition_balance`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRegretMatching_pairInternalRegret_le`,
  `Cslib.MachineLearning.OnlineLearning.Experts.internalRegretMatching_swapRegret_le`:
  Hart–Mas-Colell balance equation `(3.1)` and anytime `O(√T)` internal- and swap-regret bounds
  ([HartMasColell2000] Theorem A).

## References

* [D. Blackwell, *An analog of the minimax theorem for vector payoffs*][Blackwell1956]
* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [S. Hart and A. Mas-Colell, *A Simple Adaptive Procedure Leading to Correlated
  Equilibrium*][HartMasColell2000]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Matrix Real Cslib
open scoped RealInnerProductSpace

/-! ### Internal, swap, and external regret functionals -/

section RegretDefs

variable {ι : Type*}

/-- The single-pair modification rule `switch_i(·, j, k)` of [BlumMansour2007AGT] (§4.4): replaces
action `j` by `k` and leaves every other action unchanged. -/
@[expose] def switchAction [DecidableEq ι] (j k x : ι) : ι :=
  if x = j then k else x

@[simp] theorem switchAction_self [DecidableEq ι] (j k : ι) : switchAction j k j = k :=
  ite_eq_left rfl

theorem switchAction_of_ne [DecidableEq ι] {j k x : ι} (hx : x ≠ j) : switchAction j k x = x :=
  ite_eq_right hx

@[simp] theorem switchAction_same [DecidableEq ι] (j x : ι) : switchAction j j x = x := by
  unfold switchAction
  split_ifs with h <;> simp [h]

/-- Cumulative **pairwise internal regret** for replacing action `j` with `k` over the first `T`
rounds ([BlumMansour2007AGT] §4.2; `T` times `D_T^i(j, k)` in [HartMasColell2000] eq. `(2.1b)`,
p. 1130). -/
@[expose] def pairInternalRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) (j k : ι) : ℝ :=
  ∑ t ∈ range T, p t j * (ℓ t j - ℓ t k)

@[simp] theorem pairInternalRegret_zero (p ℓ : ℕ → ι → ℝ) (j k : ι) :
    pairInternalRegret p ℓ 0 j k = 0 := by
  simp [pairInternalRegret]

@[simp] theorem pairInternalRegret_same (p ℓ : ℕ → ι → ℝ) (T : ℕ) (j : ι) :
    pairInternalRegret p ℓ T j j = 0 := by
  simp [pairInternalRegret]

theorem pairInternalRegret_succ (p ℓ : ℕ → ι → ℝ) (T : ℕ) (j k : ι) :
    pairInternalRegret p ℓ (T + 1) j k =
      pairInternalRegret p ℓ T j k + p T j * (ℓ T j - ℓ T k) :=
  sum_range_succ _ T

variable [Fintype ι]

/-- Cumulative **swap regret** against a modification rule `δ : ι → ι` over the first `T` rounds
([BlumMansour2007AGT] §4.2). -/
@[expose] def swapRegretOf (p ℓ : ℕ → ι → ℝ) (T : ℕ) (δ : ι → ι) : ℝ :=
  ∑ t ∈ range T, ∑ j, p t j * (ℓ t j - ℓ t (δ j))

/-- Cumulative **external regret** against a fixed action `k : ι` over the first `T` rounds
([BlumMansour2007AGT] §4.2). -/
@[expose] def externalRegretOf (p ℓ : ℕ → ι → ℝ) (T : ℕ) (k : ι) : ℝ :=
  ∑ t ∈ range T, (∑ j, p t j * ℓ t j - ℓ t k)

@[simp] theorem externalRegretOf_zero (p ℓ : ℕ → ι → ℝ) (k : ι) :
    externalRegretOf p ℓ 0 k = 0 := by
  simp [externalRegretOf]

theorem externalRegretOf_succ (p ℓ : ℕ → ι → ℝ) (T : ℕ) (k : ι) :
    externalRegretOf p ℓ (T + 1) k =
      externalRegretOf p ℓ T k + (∑ j, p T j * ℓ T j - ℓ T k) :=
  sum_range_succ _ T

/-- Swap regret against `δ` is the sum of the pairwise internal regrets `(j, δ j)` over all actions
`j` ([BlumMansour2007AGT] §4.2). -/
theorem swapRegretOf_eq_sum_pairInternalRegret (p ℓ : ℕ → ι → ℝ) (T : ℕ) (δ : ι → ι) :
    swapRegretOf p ℓ T δ = ∑ j, pairInternalRegret p ℓ T j (δ j) := by
  rw [swapRegretOf, sum_comm]
  rfl

@[simp] theorem swapRegretOf_id (p ℓ : ℕ → ι → ℝ) (T : ℕ) :
    swapRegretOf p ℓ T id = 0 := by
  simp [swapRegretOf]

/-- Swap regret against `switchAction j k` equals the pairwise internal regret `pairInternalRegret`
for `(j, k)` ([BlumMansour2007AGT] §§4.2, 4.4). -/
theorem swapRegretOf_switchAction [DecidableEq ι] (p ℓ : ℕ → ι → ℝ) (T : ℕ) (j k : ι) :
    swapRegretOf p ℓ T (switchAction j k) = pairInternalRegret p ℓ T j k := by
  rw [swapRegretOf_eq_sum_pairInternalRegret]
  rw [← add_sum_erase _ _ (mem_univ j), switchAction_self]
  have hzero : ∑ x ∈ univ.erase j, pairInternalRegret p ℓ T x (switchAction j k x) = 0 :=
    sum_eq_zero fun x hx => by
      rw [switchAction_of_ne (ne_of_mem_erase hx), pairInternalRegret_same]
  rw [hzero, add_zero]

/-- When `p t` sums to `1` in each round `t < T`, swap regret against the constant map `fun _ => k`
equals external regret against `k` ([BlumMansour2007AGT] §4.2). -/
theorem swapRegretOf_const {p ℓ : ℕ → ι → ℝ} {T : ℕ} (hp : ∀ t < T, ∑ j, p t j = 1) (k : ι) :
    swapRegretOf p ℓ T (fun _ => k) = externalRegretOf p ℓ T k := by
  rw [swapRegretOf, externalRegretOf]
  refine sum_congr rfl fun t ht => ?_
  have hpt := hp t (mem_range.mp ht)
  have hsub : ∑ j, p t j * (ℓ t j - ℓ t k) = ∑ j, p t j * ℓ t j - (∑ j, p t j) * ℓ t k := by
    simp only [mul_sub, sum_sub_distrib, sum_mul]
  rw [hsub, hpt, one_mul]

/-- **Exercise 4.1** of [BlumMansour2007AGT]: if every pairwise internal regret is at most `R`,
then swap regret against every modification rule `δ : ι → ι` is at most `|ι| * R`. -/
theorem swapRegretOf_le_card_mul_of_pairInternalRegret_le {p ℓ : ℕ → ι → ℝ} {T : ℕ} {R : ℝ}
    (hR : ∀ j k, pairInternalRegret p ℓ T j k ≤ R) (δ : ι → ι) :
    swapRegretOf p ℓ T δ ≤ Fintype.card ι * R := by
  rw [swapRegretOf_eq_sum_pairInternalRegret]
  calc ∑ j, pairInternalRegret p ℓ T j (δ j)
      ≤ ∑ _j : ι, R := sum_le_sum fun j _ => hR j (δ j)
    _ = Fintype.card ι * R := by simp [sum_const, nsmul_eq_mul]

end RegretDefs

/-! ### Euclidean projection onto `ℝ_{\le 0}^L` and Blackwell's quadratic potential -/

section BlackwellPotential

/-- The closed convex **nonpositive orthant** `{z ∈ ℝ^L | ∀ l, z l ≤ 0}` in `EuclideanSpace ℝ L`
([HartMasColell2000] §3, p. 1136, `ℝ_-^L`). -/
@[expose] def nonposOrthant (L : Type*) : Set (EuclideanSpace ℝ L) :=
  {z | ∀ l, z l ≤ 0}

variable {L : Type*}

theorem zero_mem_nonposOrthant : (0 : EuclideanSpace ℝ L) ∈ nonposOrthant L :=
  fun _ => le_rfl

theorem convex_nonposOrthant : Convex ℝ (nonposOrthant L) := by
  intro x hx y hy a b ha hb _ l
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [hx l, hy l]

theorem isClosed_nonposOrthant : IsClosed (nonposOrthant L) := by
  have heq : nonposOrthant L = ⋂ l : L, {z : EuclideanSpace ℝ L | z l ≤ 0} := by
    ext z
    simp [nonposOrthant]
  rw [heq]
  exact isClosed_iInter fun l => isClosed_le (PiLp.continuous_apply 2 _ l) continuous_const

theorem isComplete_nonposOrthant : IsComplete (nonposOrthant L) :=
  isClosed_nonposOrthant.isComplete

variable [Fintype L]

/-- **Figure 2** of [HartMasColell2000] (§3, p. 1137): the Euclidean `metricProjection` of `y` onto
`nonposOrthant L` is the coordinatewise negative part `l ↦ min 0 (y l)`. -/
theorem metricProjection_nonposOrthant (y : EuclideanSpace ℝ L) :
    metricProjection (nonposOrthant L) y = WithLp.toLp 2 (fun l => min 0 (y l)) := by
  have hmem : (WithLp.toLp 2 fun l => min 0 (y l)) ∈ nonposOrthant L :=
    fun l => min_le_left 0 (y l)
  rw [metricProjection_eq_iff isComplete_nonposOrthant convex_nonposOrthant hmem]
  intro z hz
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  refine sum_nonpos fun l _ => ?_
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  rcases le_total (y l) 0 with hyl | hyl
  · rw [min_eq_right hyl, sub_self, mul_zero]
  · rw [min_eq_left hyl, sub_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (hz l) hyl

/-- Coordinatewise, subtracting the projection onto `nonposOrthant L` yields the positive part
`l ↦ max 0 (y l)` ([HartMasColell2000] §3, p. 1137, `λ(D_t) = D_t - [D_t]_- = [D_t]_+`). -/
theorem sub_metricProjection_nonposOrthant (y : EuclideanSpace ℝ L) :
    y - metricProjection (nonposOrthant L) y = WithLp.toLp 2 (fun l => max 0 (y l)) := by
  rw [metricProjection_nonposOrthant]
  ext l
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  rcases le_total 0 (y l) with h | h
  · rw [min_eq_left h, max_eq_right h, sub_zero]
  · rw [min_eq_right h, max_eq_left h, sub_self]

/-- The squared distance of `y` to `nonposOrthant L` equals `∑ l, max 0 (y l) ^ 2`. -/
theorem norm_sub_metricProjection_nonposOrthant_sq (y : EuclideanSpace ℝ L) :
    ‖y - metricProjection (nonposOrthant L) y‖ ^ 2 = ∑ l, max 0 (y l) ^ 2 := by
  rw [sub_metricProjection_nonposOrthant, EuclideanSpace.real_norm_sq_eq]

/-- **Blackwell's quadratic potential bound for the nonpositive orthant** ([Blackwell1956];
[HartMasColell2000] §3, pp. 1135–1138, and Appendix Step M1, p. 1146): if a sequence of vectors
`r : ℕ → L → ℝ` satisfies the halfspace condition
`∑ l, max 0 (∑ s ∈ range t, r s l) * r t l ≤ 0` at every round `t < T`, then
`∑ l, max 0 (∑ t ∈ range T, r t l) ^ 2 ≤ ∑ t ∈ range T, ∑ l, r t l ^ 2`.

The one-step telescope uses the nearest-point property `metricProjection_eq_iff_forall_norm_le` of
`metricProjection (nonposOrthant L)` and the Hilbert-space expansion `norm_add_sq_real`. -/
theorem blackwell_orthant_potential_le {r : ℕ → L → ℝ} {T : ℕ}
    (hB : ∀ t < T, ∑ l, max 0 (∑ s ∈ range t, r s l) * r t l ≤ 0) :
    ∑ l, max 0 (∑ t ∈ range T, r t l) ^ 2 ≤ ∑ t ∈ range T, ∑ l, r t l ^ 2 := by
  induction T with
  | zero => simp
  | succ t ih =>
    have iht := ih fun s hs => hB s (Nat.lt_succ_of_lt hs)
    have hBt := hB t (Nat.lt_succ_self t)
    let Rt : EuclideanSpace ℝ L := WithLp.toLp 2 (fun l => ∑ s ∈ range t, r s l)
    let rt : EuclideanSpace ℝ L := WithLp.toLp 2 (r t)
    let Rt1 : EuclideanSpace ℝ L := Rt + rt
    have hproj_mem : metricProjection (nonposOrthant L) Rt ∈ nonposOrthant L :=
      metricProjection_mem ⟨0, zero_mem_nonposOrthant⟩ isComplete_nonposOrthant
        convex_nonposOrthant Rt
    have hnear : ‖Rt1 - metricProjection (nonposOrthant L) Rt1‖ ≤
        ‖Rt1 - metricProjection (nonposOrthant L) Rt‖ :=
      (metricProjection_eq_iff_forall_norm_le isComplete_nonposOrthant convex_nonposOrthant
        (metricProjection_mem ⟨0, zero_mem_nonposOrthant⟩ isComplete_nonposOrthant
          convex_nonposOrthant Rt1)).mp rfl _ hproj_mem
    have hnear_sq : ‖Rt1 - metricProjection (nonposOrthant L) Rt1‖ ^ 2 ≤
        ‖(Rt - metricProjection (nonposOrthant L) Rt) + rt‖ ^ 2 := by
      rw [show (Rt - metricProjection (nonposOrthant L) Rt) + rt =
        Rt1 - metricProjection (nonposOrthant L) Rt by dsimp [Rt1]; abel]
      exact pow_le_pow_left₀ (norm_nonneg _) hnear 2
    rw [norm_add_sq_real] at hnear_sq
    have hinner : ⟪Rt - metricProjection (nonposOrthant L) Rt, rt⟫ =
        ∑ l, max 0 (∑ s ∈ range t, r s l) * r t l := by
      rw [sub_metricProjection_nonposOrthant, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, dotProduct]
      exact sum_congr rfl fun l _ => mul_comm _ _
    have hRt1_sq : ‖Rt1 - metricProjection (nonposOrthant L) Rt1‖ ^ 2 =
        ∑ l, max 0 (∑ s ∈ range (t + 1), r s l) ^ 2 := by
      rw [norm_sub_metricProjection_nonposOrthant_sq]
      refine sum_congr rfl fun l _ => ?_
      simp only [Rt1, Rt, rt, WithLp.ofLp_add, Pi.add_apply, sum_range_succ]
    have hRt_sq : ‖Rt - metricProjection (nonposOrthant L) Rt‖ ^ 2 =
        ∑ l, max 0 (∑ s ∈ range t, r s l) ^ 2 :=
      norm_sub_metricProjection_nonposOrthant_sq Rt
    have hrt_sq : ‖rt‖ ^ 2 = ∑ l, r t l ^ 2 := EuclideanSpace.real_norm_sq_eq rt
    rw [hRt1_sq, hRt_sq, hinner, hrt_sq] at hnear_sq
    rw [sum_range_succ]
    linarith

/-- Coordinatewise consequence of `blackwell_orthant_potential_le`: every coordinate cumulative sum
is bounded by `√(∑ t < T, ∑ l, r t l ^ 2)`. -/
theorem blackwell_orthant_coord_le {r : ℕ → L → ℝ} {T : ℕ}
    (hB : ∀ t < T, ∑ l, max 0 (∑ s ∈ range t, r s l) * r t l ≤ 0) (l₀ : L) :
    ∑ t ∈ range T, r t l₀ ≤ √(∑ t ∈ range T, ∑ l, r t l ^ 2) := by
  have hpot := blackwell_orthant_potential_le hB
  have hsingle : max 0 (∑ t ∈ range T, r t l₀) ^ 2 ≤ ∑ l, max 0 (∑ t ∈ range T, r t l) ^ 2 :=
    single_le_sum (f := fun l => max 0 (∑ t ∈ range T, r t l) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ l₀)
  calc ∑ t ∈ range T, r t l₀
      ≤ max 0 (∑ t ∈ range T, r t l₀) := le_max_right _ _
    _ = √(max 0 (∑ t ∈ range T, r t l₀) ^ 2) := (sqrt_sq (le_max_left _ _)).symm
    _ ≤ √(∑ t ∈ range T, ∑ l, r t l ^ 2) := sqrt_le_sqrt (hsingle.trans hpot)

/-- Finite Cauchy–Schwarz inequality `(∑ l, f l) ^ 2 ≤ |L| * ∑ l, f l ^ 2`, proved via
`real_inner_le_norm` in `EuclideanSpace ℝ L`. -/
private theorem sq_sum_le_card_mul_sum_sq (f : L → ℝ) :
    (∑ l, f l) ^ 2 ≤ Fintype.card L * ∑ l, f l ^ 2 := by
  let ones : EuclideanSpace ℝ L := WithLp.toLp 2 (fun _ => 1)
  let vf : EuclideanSpace ℝ L := WithLp.toLp 2 f
  have hcs := real_inner_le_norm ones vf
  have hinner : ⟪ones, vf⟫ = ∑ l, f l := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    simp [ones, vf]
  have hones_sq : ‖ones‖ ^ 2 = Fintype.card L := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [ones]
  have hvf_sq : ‖vf‖ ^ 2 = ∑ l, f l ^ 2 := EuclideanSpace.real_norm_sq_eq vf
  rw [hinner] at hcs
  rcases le_or_gt 0 (∑ l, f l) with hnn | hneg
  · calc (∑ l, f l) ^ 2 ≤ (‖ones‖ * ‖vf‖) ^ 2 := pow_le_pow_left₀ hnn hcs 2
      _ = ‖ones‖ ^ 2 * ‖vf‖ ^ 2 := mul_pow _ _ 2
      _ = Fintype.card L * ∑ l, f l ^ 2 := by rw [hones_sq, hvf_sq]
  · have hneg_abs := real_inner_le_norm (-ones) vf
    have hinner_neg : ⟪-ones, vf⟫ = -∑ l, f l := by rw [inner_neg_left, hinner]
    rw [hinner_neg, norm_neg] at hneg_abs
    calc (∑ l, f l) ^ 2 = (-∑ l, f l) ^ 2 := (neg_sq _).symm
      _ ≤ (‖ones‖ * ‖vf‖) ^ 2 := pow_le_pow_left₀ (by linarith) hneg_abs 2
      _ = ‖ones‖ ^ 2 * ‖vf‖ ^ 2 := mul_pow _ _ 2
      _ = Fintype.card L * ∑ l, f l ^ 2 := by rw [hones_sq, hvf_sq]

end BlackwellPotential

/-! ### Blackwell's external regret-matching (`p_t(a) ∝ [R_t(a)]_+`) -/

section ExternalRegretMatching

variable {ι : Type*} [Fintype ι]

/-- One step of **Blackwell's external regret-matching** ([HartMasColell2000] eq. `(4.2b)`,
p. 1139): normalizes a nonnegative regret vector `rPos` when its sum is positive, and plays the
uniform distribution `1 / |ι|` otherwise. -/
@[expose] noncomputable def regretMatchingStep (rPos : ι → ℝ) (a : ι) : ℝ :=
  if ∑ b, rPos b = 0 then 1 / Fintype.card ι else rPos a / ∑ b, rPos b

theorem regretMatchingStep_nonneg {rPos : ι → ℝ} (hr : ∀ b, 0 ≤ rPos b) (a : ι) :
    0 ≤ regretMatchingStep rPos a := by
  unfold regretMatchingStep
  split_ifs with h0
  · positivity
  · exact div_nonneg (hr a) (sum_nonneg fun b _ => hr b)

theorem sum_regretMatchingStep [Nonempty ι] {rPos : ι → ℝ} :
    ∑ a, regretMatchingStep rPos a = 1 := by
  unfold regretMatchingStep
  split_ifs with h0
  · simp only [sum_const, card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · rw [← sum_div, div_self h0]

/-- Key proportionality identity of `regretMatchingStep`: for any nonnegative `rPos`,
`rPos a = (∑ b, rPos b) * regretMatchingStep rPos a` holds unconditionally (without splitting on
whether `∑ b, rPos b = 0`). -/
theorem mul_regretMatchingStep_eq {rPos : ι → ℝ} (hr : ∀ b, 0 ≤ rPos b) (a : ι) :
    (∑ b, rPos b) * regretMatchingStep rPos a = rPos a := by
  unfold regretMatchingStep
  split_ifs with h0
  · rw [h0, zero_mul]
    exact ((sum_eq_zero_iff_of_nonneg fun b _ => hr b).mp h0 a (mem_univ a)).symm
  · exact mul_div_cancel₀ (rPos a) h0

/-- **Blackwell's external regret-matching learner** ([Blackwell1956]; [HartMasColell2000] §4(c),
eqs. `(4.2a)`–`(4.2b)`, p. 1139): in round `t`, plays proportional to the positive cumulative
external regrets `max 0 (externalRegretOf p ℓ t a)`, defaulting to the uniform distribution when no
action has positive regret. -/
noncomputable def regretMatchingProb (ℓ : ℕ → ι → ℝ) : ℕ → ι → ℝ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t p =>
    regretMatchingStep fun a =>
      max 0 (∑ s : Fin t, (∑ b, p s.1 s.2 b * ℓ s.1 b - ℓ s.1 a))

/-- Unfolding equation for `regretMatchingProb`: round `t` applies `regretMatchingStep` to the
positive cumulative external regrets from rounds `< t`. -/
theorem regretMatchingProb_eq (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    regretMatchingProb ℓ t =
      regretMatchingStep fun a => max 0 (externalRegretOf (regretMatchingProb ℓ) ℓ t a) := by
  conv_lhs => rw [regretMatchingProb, WellFounded.fix_eq]
  congr 1
  funext a
  rw [externalRegretOf, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- In round `0`, `regretMatchingProb` plays the uniform distribution `1 / |ι|`. -/
@[simp] theorem regretMatchingProb_zero (ℓ : ℕ → ι → ℝ) (a : ι) :
    regretMatchingProb ℓ 0 a = 1 / Fintype.card ι := by
  rw [regretMatchingProb_eq]
  simp [regretMatchingStep]

/-- `regretMatchingProb` is causal (an online algorithm): round `t` depends only on losses before
round `t`. -/
theorem regretMatchingProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    regretMatchingProb ℓ t = regretMatchingProb ℓ' t := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [regretMatchingProb_eq, regretMatchingProb_eq]
    congr 1
    funext a
    congr 1
    refine sum_congr rfl fun s hs => ?_
    have hst := mem_range.mp hs
    rw [ih s hst (fun u hu => h u (hu.trans hst)), h s hst]

theorem regretMatchingProb_nonneg (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : ι) :
    0 ≤ regretMatchingProb ℓ t a := by
  rw [regretMatchingProb_eq]
  exact regretMatchingStep_nonneg (fun _ => le_max_left _ _) a

theorem sum_regretMatchingProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ a, regretMatchingProb ℓ t a = 1 := by
  rw [regretMatchingProb_eq]
  exact sum_regretMatchingStep

/-- `regretMatchingProb` satisfies the **Blackwell halfspace condition with equality** in every
round `t`, for arbitrary real-valued losses. -/
theorem sum_max_externalRegret_mul_sub_eq_zero [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ a, max 0 (externalRegretOf (regretMatchingProb ℓ) ℓ t a) *
        (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) = 0 := by
  set rPos : ι → ℝ := fun a => max 0 (externalRegretOf (regretMatchingProb ℓ) ℓ t a)
  have hstep : ∀ a, rPos a = (∑ b, rPos b) * regretMatchingProb ℓ t a := fun a => by
    rw [regretMatchingProb_eq]
    exact (mul_regretMatchingStep_eq (fun _ => le_max_left _ _) a).symm
  calc ∑ a, rPos a * (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a)
      = ∑ a, (∑ b, rPos b) * (regretMatchingProb ℓ t a *
          (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a)) :=
        sum_congr rfl fun a _ => by rw [hstep a, mul_assoc]
    _ = (∑ b, rPos b) * ∑ a, regretMatchingProb ℓ t a *
          (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) := (mul_sum _ _ _).symm
    _ = (∑ b, rPos b) * ((∑ a, regretMatchingProb ℓ t a) *
          (∑ b, regretMatchingProb ℓ t b * ℓ t b) -
          ∑ a, regretMatchingProb ℓ t a * ℓ t a) := by
        simp only [mul_sub, sum_sub_distrib, sum_mul]
    _ = 0 := by rw [sum_regretMatchingProb, one_mul, sub_self, mul_zero]

/-- Quadratic potential bound for `regretMatchingProb`: the sum of squared positive external regrets
after `T` rounds is at most `∑ t < T, ∑ a, (⟨p_t, ℓ_t⟩ - ℓ_t(a)) ^ 2`. -/
theorem sum_max_externalRegret_regretMatchingProb_sq_le [Nonempty ι] (ℓ : ℕ → ι → ℝ) (T : ℕ) :
    ∑ a, max 0 (externalRegretOf (regretMatchingProb ℓ) ℓ T a) ^ 2 ≤
      ∑ t ∈ range T, ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2 :=
  blackwell_orthant_potential_le (r := fun t a => ∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a)
    fun t _ => (sum_max_externalRegret_mul_sub_eq_zero ℓ t).le

/-- **Anytime `O(√T)` external regret of Blackwell's regret-matching** ([Blackwell1956];
[HartMasColell2000] §4(c), Theorem B, p. 1139, quantitative finite-horizon form): if pairwise loss
differences in rounds `< T` are bounded by `B ≥ 0`, then against every expert `k : ι`,
`externalRegretOf (regretMatchingProb ℓ) ℓ T k ≤ B * √(|ι| * T)`. -/
theorem regretMatching_externalRegret_le {ℓ : ℕ → ι → ℝ} {T : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hℓ : ∀ s < T, ∀ a b, |ℓ s a - ℓ s b| ≤ B) (k : ι) :
    externalRegretOf (regretMatchingProb ℓ) ℓ T k ≤ B * √(Fintype.card ι * T) := by
  have : Nonempty ι := ⟨k⟩
  have hcoord := blackwell_orthant_coord_le
    (r := fun t a => ∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a)
    (T := T) (fun t _ => (sum_max_externalRegret_mul_sub_eq_zero ℓ t).le) k
  have hround : ∀ t ∈ range T,
      ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2 ≤ Fintype.card ι * B ^ 2 := by
    intro t ht
    have ht' := mem_range.mp ht
    calc ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2
        ≤ ∑ _a : ι, B ^ 2 := sum_le_sum fun a _ => by
          have hrew : ∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a =
              ∑ b, regretMatchingProb ℓ t b * (ℓ t b - ℓ t a) := by
            simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_regretMatchingProb, one_mul]
          have habs : |∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a| ≤ B := by
            rw [hrew]
            calc |∑ b, regretMatchingProb ℓ t b * (ℓ t b - ℓ t a)|
                ≤ ∑ b, |regretMatchingProb ℓ t b * (ℓ t b - ℓ t a)| := abs_sum_le_sum_abs _ _
              _ ≤ ∑ b, regretMatchingProb ℓ t b * B := sum_le_sum fun b _ => by
                  rw [abs_mul, abs_of_nonneg (regretMatchingProb_nonneg ℓ t b)]
                  exact mul_le_mul_of_nonneg_left (hℓ t ht' b a)
                    (regretMatchingProb_nonneg ℓ t b)
              _ = B := by rw [← sum_mul, sum_regretMatchingProb, one_mul]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = Fintype.card ι * B ^ 2 := by simp [sum_const, nsmul_eq_mul]
  have htot : ∑ t ∈ range T, ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2 ≤
      B ^ 2 * (Fintype.card ι * T) := by
    calc ∑ t ∈ range T, ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2
        ≤ ∑ _t ∈ range T, (Fintype.card ι : ℝ) * B ^ 2 := sum_le_sum hround
      _ = B ^ 2 * (Fintype.card ι * T) := by
          simp only [sum_const, card_range, nsmul_eq_mul]
          ring
  calc externalRegretOf (regretMatchingProb ℓ) ℓ T k
      ≤ √(∑ t ∈ range T, ∑ a, (∑ b, regretMatchingProb ℓ t b * ℓ t b - ℓ t a) ^ 2) := hcoord
    _ ≤ √(B ^ 2 * (Fintype.card ι * T)) := sqrt_le_sqrt htot
    _ = B * √(Fintype.card ι * T) := by rw [sqrt_mul (sq_nonneg B), sqrt_sq hB0]

/-- Specialization of `regretMatching_externalRegret_le` to `[0, 1]`-valued losses
([BlumMansour2007AGT] §4.2 convention): external regret at most `√(|ι| * T)` for all `T`. -/
theorem regretMatching_externalRegret_le_of_mem_Icc {ℓ : ℕ → ι → ℝ} {T : ℕ}
    (hℓ : ∀ s < T, ∀ a, ℓ s a ∈ Set.Icc (0 : ℝ) 1) (k : ι) :
    externalRegretOf (regretMatchingProb ℓ) ℓ T k ≤ √(Fintype.card ι * T) := by
  simpa only [one_mul] using regretMatching_externalRegret_le zero_le_one (fun s hs a b => by
    rw [abs_le]
    constructor <;> linarith [(hℓ s hs a).1, (hℓ s hs a).2, (hℓ s hs b).1, (hℓ s hs b).2]) k

/-- Specialization of `regretMatching_externalRegret_le` to `[-M, M]`-valued losses: external regret
at most `2 * M * √(|ι| * T)` for all `T`. -/
theorem regretMatching_externalRegret_le_of_abs_le {ℓ : ℕ → ι → ℝ} {T : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hℓ : ∀ s < T, ∀ a, |ℓ s a| ≤ M) (k : ι) :
    externalRegretOf (regretMatchingProb ℓ) ℓ T k ≤ 2 * M * √(Fintype.card ι * T) :=
  regretMatching_externalRegret_le (by positivity) (fun s hs a b =>
    calc |ℓ s a - ℓ s b| = |ℓ s a + -ℓ s b| := rfl
      _ ≤ |ℓ s a| + |-ℓ s b| := abs_add_le _ _
      _ = |ℓ s a| + |ℓ s b| := by rw [abs_neg]
      _ ≤ M + M := add_le_add (hℓ s hs a) (hℓ s hs b)
      _ = 2 * M := by ring) k

end ExternalRegretMatching

/-! ### Hart–Mas-Colell stationary internal regret-matching (`Theorem A`) -/

section InternalRegretMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Inertial regret-transition matrix** of [HartMasColell2000] (§2, eq. `(2.2)`, p. 1130, and
Appendix p. 1144) with positive normalization `μ = 1 + ∑ j', ∑ k', rPos j' k'`: off-diagonal entry
`(j, k)` is `rPos j k / μ`, and diagonal entry `(j, j)` carries the remaining positive inertia mass
`1 - (∑ k' ≠ j, rPos j k') / μ`. -/
noncomputable def internalRegretTransition (rPos : ι → ι → ℝ) : Matrix ι ι ℝ :=
  let μ := 1 + ∑ j', ∑ k', rPos j' k'
  Matrix.of fun j k =>
    if k = j then 1 - (∑ k' ∈ univ.erase j, rPos j k') / μ
    else rPos j k / μ

theorem internalRegretTransition_mem_rowStochastic {rPos : ι → ι → ℝ}
    (hr : ∀ j k, 0 ≤ rPos j k) :
    internalRegretTransition rPos ∈ rowStochastic ℝ ι := by
  set μ : ℝ := 1 + ∑ j', ∑ k', rPos j' k'
  have hμ_pos : 0 < μ :=
    add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun j' _ => sum_nonneg fun k' _ => hr j' k')
  refine mem_rowStochastic_iff_sum.mpr ⟨fun j k => ?_, fun j => ?_⟩
  · dsimp only [internalRegretTransition, of_apply]
    split_ifs with hkj
    · have hsub_le : ∑ k' ∈ univ.erase j, rPos j k' ≤ ∑ j', ∑ k', rPos j' k' := by
        calc ∑ k' ∈ univ.erase j, rPos j k'
            ≤ ∑ k', rPos j k' := sum_le_univ_sum_of_nonneg (hr j)
          _ ≤ ∑ j', ∑ k', rPos j' k' :=
              single_le_sum (fun j' _ => sum_nonneg fun k' _ => hr j' k') (mem_univ j)
      have hdiv : (∑ k' ∈ univ.erase j, rPos j k') / μ ≤ 1 := by
        rw [div_le_one hμ_pos]
        dsimp [μ]
        linarith
      linarith
    · exact div_nonneg (hr j k) hμ_pos.le
  · dsimp only [internalRegretTransition, of_apply]
    rw [← add_sum_erase _ _ (mem_univ j), ite_eq_left rfl]
    have hoff : ∑ x ∈ univ.erase j,
        (if x = j then 1 - (∑ k' ∈ univ.erase j, rPos j k') / μ else rPos j x / μ) =
        (∑ k' ∈ univ.erase j, rPos j k') / μ := by
      rw [sum_div]
      refine sum_congr rfl fun x hx => ?_
      rw [ite_eq_right (ne_of_mem_erase hx)]
    rw [hoff]
    ring

/-- **Balance equation `(3.1)`** of [HartMasColell2000] (§3, p. 1133, and `(3.5)` on p. 1137):
any stationary vector `q` of `internalRegretTransition rPos` (where `rPos ≥ 0` and `rPos j j = 0`)
satisfies `∑ k, q k * rPos k j = q j * ∑ k, rPos j k` for every action `j`. -/
theorem sum_mul_internalRegretTransition_balance {rPos : ι → ι → ℝ} {q : ι → ℝ}
    (hr : ∀ j k, 0 ≤ rPos j k) (hdiag : ∀ j, rPos j j = 0)
    (hstat : q ᵥ* internalRegretTransition rPos = q) (j : ι) :
    ∑ k, q k * rPos k j = q j * ∑ k, rPos j k := by
  set μ : ℝ := 1 + ∑ j', ∑ k', rPos j' k'
  have hμ_pos : 0 < μ :=
    add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun j' _ => sum_nonneg fun k' _ => hr j' k')
  have hj := congrFun hstat j
  rw [vecMul_apply_eq_sum, ← add_sum_erase _ _ (mem_univ j)] at hj
  dsimp only [internalRegretTransition, of_apply] at hj
  rw [ite_eq_left rfl] at hj
  have hoff : ∑ k ∈ univ.erase j,
      q k * (if j = k then 1 - (∑ k' ∈ univ.erase k, rPos k k') / μ else rPos k j / μ) =
      (∑ k ∈ univ.erase j, q k * rPos k j) / μ := by
    rw [sum_div]
    refine sum_congr rfl fun k hk => ?_
    rw [ite_eq_right (ne_of_mem_erase hk).symm, mul_div_assoc]
  rw [hoff] at hj
  have herase_eq : ∑ k ∈ univ.erase j, q k * rPos k j =
      q j * ∑ k' ∈ univ.erase j, rPos j k' := by
    have hmul : μ * (q j * (1 - (∑ k' ∈ univ.erase j, rPos j k') / μ) +
        (∑ k ∈ univ.erase j, q k * rPos k j) / μ) = μ * q j := congrArg (μ * ·) hj
    field_simp [hμ_pos.ne'] at hmul
    linarith
  calc ∑ k, q k * rPos k j
      = q j * rPos j j + ∑ k ∈ univ.erase j, q k * rPos k j :=
        (add_sum_erase _ _ (mem_univ j)).symm
    _ = q j * (rPos j j + ∑ k' ∈ univ.erase j, rPos j k') := by
        rw [hdiag j, mul_zero, zero_add, zero_add, herase_eq]
    _ = q j * ∑ k, rPos j k := by rw [add_sum_erase _ _ (mem_univ j)]

omit [DecidableEq ι] in
/-- **Equations `(3.3)`–`(3.4)`** of [HartMasColell2000] (§3, pp. 1136–1137): whenever `q` satisfies
the balance equation `(3.1)` for `rPos`, the inner product of `rPos` with the instantaneous
pairwise regret vector `(j, k) ↦ q j * (v j - v k)` vanishes identically for every loss/payoff
vector `v : ι → ℝ`. -/
theorem sum_balance_mul_sub_eq_zero {rPos : ι → ι → ℝ} {q : ι → ℝ}
    (hbal : ∀ j, ∑ k, q k * rPos k j = q j * ∑ k, rPos j k) (v : ι → ℝ) :
    ∑ p : ι × ι, rPos p.1 p.2 * (q p.1 * (v p.1 - v p.2)) = 0 := by
  rw [Fintype.sum_prod_type]
  have hexp : ∀ j, ∑ k, rPos j k * (q j * (v j - v k)) =
      v j * (q j * ∑ k, rPos j k) - ∑ k, v k * (q j * rPos j k) := fun j => by
    have h1 : ∀ k, rPos j k * (q j * (v j - v k)) =
        v j * (q j * rPos j k) - v k * (q j * rPos j k) := fun k => by ring
    simp only [h1, sum_sub_distrib, ← mul_sum]
  simp only [hexp, sum_sub_distrib]
  rw [sum_comm (f := fun j k => v k * (q j * rPos j k))]
  have h2 : ∑ k, ∑ j, v k * (q j * rPos j k) = ∑ j, v j * (q j * ∑ k, rPos j k) := by
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sum, hbal j]
  rw [h2, sub_self]

/-- **Hart–Mas-Colell stationary internal regret-matching learner** ([HartMasColell2000] §3,
eq. `(3.1)`, Theorem A, p. 1133): in round `t`, chooses `Matrix.stationaryVec` of the inertial
regret-transition matrix formed from the positive cumulative internal regrets of rounds `< t`. -/
noncomputable def internalRegretMatchingProb (ℓ : ℕ → ι → ℝ) : ℕ → ι → ℝ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t p =>
    Matrix.stationaryVec (internalRegretTransition fun j k =>
      max 0 (∑ s : Fin t, p s.1 s.2 j * (ℓ s.1 j - ℓ s.1 k)))

/-- Unfolding equation for `internalRegretMatchingProb`. -/
theorem internalRegretMatchingProb_eq (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    internalRegretMatchingProb ℓ t =
      Matrix.stationaryVec (internalRegretTransition fun j k =>
        max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ t j k)) := by
  conv_lhs => rw [internalRegretMatchingProb, WellFounded.fix_eq]
  congr 2
  funext j k
  rw [pairInternalRegret, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- `internalRegretMatchingProb` is causal (an online algorithm): round `t` depends only on losses
before round `t`. -/
theorem internalRegretMatchingProb_congr {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ}
    (h : ∀ s < t, ℓ s = ℓ' s) :
    internalRegretMatchingProb ℓ t = internalRegretMatchingProb ℓ' t := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [internalRegretMatchingProb_eq, internalRegretMatchingProb_eq]
    congr 2
    funext j k
    congr 1
    refine sum_congr rfl fun s hs => ?_
    have hst := mem_range.mp hs
    rw [ih s hst (fun u hu => h u (hu.trans hst)), h s hst]

theorem internalRegretMatchingProb_nonneg [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : ι) :
    0 ≤ internalRegretMatchingProb ℓ t a := by
  rw [internalRegretMatchingProb_eq]
  exact stationaryVec_nonneg (internalRegretTransition_mem_rowStochastic fun _ _ => le_max_left _ _)
    a

theorem sum_internalRegretMatchingProb [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ a, internalRegretMatchingProb ℓ t a = 1 := by
  rw [internalRegretMatchingProb_eq]
  exact sum_stationaryVec (internalRegretTransition_mem_rowStochastic fun _ _ => le_max_left _ _)

theorem internalRegretMatchingProb_le_one [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (a : ι) :
    internalRegretMatchingProb ℓ t a ≤ 1 :=
  (single_le_sum (fun b _ => internalRegretMatchingProb_nonneg ℓ t b) (mem_univ a)).trans_eq
    (sum_internalRegretMatchingProb ℓ t)

/-- `internalRegretMatchingProb` satisfies Hart and Mas-Colell's balance equation `(3.1)` in every
round `t`. -/
theorem sum_mul_posPairInternalRegret_eq [Nonempty ι] (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    ∑ k, internalRegretMatchingProb ℓ t k *
        max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ t k j) =
      internalRegretMatchingProb ℓ t j *
        ∑ k, max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ t j k) := by
  have hstat : internalRegretMatchingProb ℓ t ᵥ*
      internalRegretTransition
        (fun j' k' => max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ t j' k')) =
      internalRegretMatchingProb ℓ t := by
    rw [internalRegretMatchingProb_eq]
    exact stationaryVec_vecMul
      (internalRegretTransition_mem_rowStochastic fun _ _ => le_max_left _ _)
  exact sum_mul_internalRegretTransition_balance
    (fun _ _ => le_max_left _ _)
    (fun j' => by rw [pairInternalRegret_same, max_self]) hstat j

/-- Quadratic potential bound for `internalRegretMatchingProb`: when pairwise loss differences in
rounds `< T` are bounded by `B`,
`∑ p : ι × ι, max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T p.1 p.2) ^ 2 ≤
B ^ 2 * ((|ι| - 1 : ℕ) * T)`. -/
theorem sum_max_pairInternalRegret_sq_le [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ} {B : ℝ}
    (hℓ : ∀ s < T, ∀ a b, |ℓ s a - ℓ s b| ≤ B) :
    ∑ p : ι × ι,
        max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T p.1 p.2) ^ 2 ≤
      B ^ 2 * ((Fintype.card ι - 1 : ℕ) * T) := by
  set q := internalRegretMatchingProb ℓ
  have hpot := blackwell_orthant_potential_le
    (L := ι × ι) (r := fun t p => q t p.1 * (ℓ t p.1 - ℓ t p.2)) (T := T) fun t _ =>
      (sum_balance_mul_sub_eq_zero (sum_mul_posPairInternalRegret_eq ℓ t) (ℓ t)).le
  refine hpot.trans ?_
  have hround : ∀ t ∈ range T,
      ∑ p : ι × ι, (q t p.1 * (ℓ t p.1 - ℓ t p.2)) ^ 2 ≤
        B ^ 2 * (Fintype.card ι - 1 : ℕ) := by
    intro t ht
    have ht' := mem_range.mp ht
    rw [Fintype.sum_prod_type]
    have hj_bound : ∀ j : ι,
        ∑ k, (q t j * (ℓ t j - ℓ t k)) ^ 2 ≤
          q t j * (B ^ 2 * (Fintype.card ι - 1 : ℕ)) := fun j => by
      rw [← add_sum_erase _ _ (mem_univ j), sub_self, mul_zero, zero_pow two_ne_zero, zero_add]
      have hqj0 := internalRegretMatchingProb_nonneg ℓ t j
      have hqj1 := internalRegretMatchingProb_le_one ℓ t j
      have hqj_sq : q t j ^ 2 ≤ q t j := by nlinarith
      calc ∑ k ∈ univ.erase j, (q t j * (ℓ t j - ℓ t k)) ^ 2
          ≤ ∑ _k ∈ univ.erase j, q t j ^ 2 * B ^ 2 := sum_le_sum fun k _ => by
            rw [mul_pow]
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hℓ t ht' j k) 2
        _ = ((univ.erase j).card : ℝ) * (q t j ^ 2 * B ^ 2) := by
            simp [sum_const, nsmul_eq_mul]
        _ = (Fintype.card ι - 1 : ℕ) * (q t j ^ 2 * B ^ 2) := by
            rw [card_erase_of_mem (mem_univ j), card_univ]
        _ ≤ (Fintype.card ι - 1 : ℕ) * (q t j * B ^ 2) := by gcongr
        _ = q t j * (B ^ 2 * (Fintype.card ι - 1 : ℕ)) := by ring
    calc ∑ j, ∑ k, (q t j * (ℓ t j - ℓ t k)) ^ 2
        ≤ ∑ j, q t j * (B ^ 2 * (Fintype.card ι - 1 : ℕ)) := sum_le_sum fun j _ => hj_bound j
      _ = (∑ j, q t j) * (B ^ 2 * (Fintype.card ι - 1 : ℕ)) := (sum_mul _ _ _).symm
      _ = B ^ 2 * (Fintype.card ι - 1 : ℕ) := by rw [sum_internalRegretMatchingProb, one_mul]
  calc ∑ t ∈ range T, ∑ p : ι × ι, (q t p.1 * (ℓ t p.1 - ℓ t p.2)) ^ 2
      ≤ ∑ _t ∈ range T, B ^ 2 * (Fintype.card ι - 1 : ℕ) := sum_le_sum hround
    _ = B ^ 2 * ((Fintype.card ι - 1 : ℕ) * T) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring

/-- **Quantitative Theorem A** of [HartMasColell2000] (§3, pp. 1133, 1138): if pairwise loss
differences in rounds `< T` are bounded by `B ≥ 0`, then `internalRegretMatchingProb` achieves
pairwise internal regret at most `B * √((|ι| - 1) * T)` for every pair of actions `(j, k)` and
every horizon `T`. -/
theorem internalRegretMatching_pairInternalRegret_le {ℓ : ℕ → ι → ℝ} {T : ℕ} {B : ℝ}
    (hB0 : 0 ≤ B) (hℓ : ∀ s < T, ∀ a b, |ℓ s a - ℓ s b| ≤ B) (j k : ι) :
    pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j k ≤
      B * √((Fintype.card ι - 1 : ℕ) * T) := by
  have : Nonempty ι := ⟨j⟩
  have hpot := sum_max_pairInternalRegret_sq_le hℓ
  have hsingle : max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j k) ^ 2 ≤
      ∑ p : ι × ι, max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T p.1 p.2) ^ 2 :=
    single_le_sum
      (f := fun p : ι × ι =>
        max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T p.1 p.2) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ (j, k))
  calc pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j k
      ≤ max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j k) := le_max_right _ _
    _ = √(max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j k) ^ 2) :=
        (sqrt_sq (le_max_left _ _)).symm
    _ ≤ √(B ^ 2 * ((Fintype.card ι - 1 : ℕ) * T)) := sqrt_le_sqrt (hsingle.trans hpot)
    _ = B * √((Fintype.card ι - 1 : ℕ) * T) := by rw [sqrt_mul (sq_nonneg B), sqrt_sq hB0]

/-- **Anytime `O(√T)` swap regret of Hart–Mas-Colell stationary regret-matching**: by Cauchy–Schwarz
over the `|ι|` pairs `(j, δ j)`, if pairwise loss differences in rounds `< T` are bounded by
`B ≥ 0`, then against every modification rule `δ : ι → ι`,
`swapRegretOf (internalRegretMatchingProb ℓ) ℓ T δ ≤ B * √(|ι| * (|ι| - 1) * T)`. -/
theorem internalRegretMatching_swapRegret_le [Nonempty ι] {ℓ : ℕ → ι → ℝ} {T : ℕ} {B : ℝ}
    (hB0 : 0 ≤ B) (hℓ : ∀ s < T, ∀ a b, |ℓ s a - ℓ s b| ≤ B) (δ : ι → ι) :
    swapRegretOf (internalRegretMatchingProb ℓ) ℓ T δ ≤
      B * √(Fintype.card ι * (Fintype.card ι - 1 : ℕ) * T) := by
  set rPos : ι → ℝ := fun j =>
    max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j (δ j))
  have hpot := sum_max_pairInternalRegret_sq_le hℓ
  let emb : ι ↪ ι × ι := ⟨fun j => (j, δ j), fun j₁ j₂ h => (Prod.mk.inj h).1⟩
  have hsub_sq : ∑ j, rPos j ^ 2 ≤ B ^ 2 * ((Fintype.card ι - 1 : ℕ) * T) := by
    have hmap : ∑ j, rPos j ^ 2 =
        ∑ p ∈ univ.map emb,
          max 0 (pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T p.1 p.2) ^ 2 := by
      rw [sum_map]
      rfl
    rw [hmap]
    exact (sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _).trans hpot
  have hcs := sq_sum_le_card_mul_sum_sq rPos
  have hsum_nn : 0 ≤ ∑ j, rPos j := sum_nonneg fun j _ => le_max_left _ _
  have hsq_bd : (∑ j, rPos j) ^ 2 ≤
      B ^ 2 * (Fintype.card ι * (Fintype.card ι - 1 : ℕ) * T) := by
    calc (∑ j, rPos j) ^ 2
        ≤ Fintype.card ι * ∑ j, rPos j ^ 2 := hcs
      _ ≤ Fintype.card ι * (B ^ 2 * ((Fintype.card ι - 1 : ℕ) * T)) :=
          mul_le_mul_of_nonneg_left hsub_sq (Nat.cast_nonneg _)
      _ = B ^ 2 * (Fintype.card ι * (Fintype.card ι - 1 : ℕ) * T) := by ring
  calc swapRegretOf (internalRegretMatchingProb ℓ) ℓ T δ
      = ∑ j, pairInternalRegret (internalRegretMatchingProb ℓ) ℓ T j (δ j) :=
        swapRegretOf_eq_sum_pairInternalRegret _ _ _ _
    _ ≤ ∑ j, rPos j := sum_le_sum fun j _ => le_max_right _ _
    _ = √((∑ j, rPos j) ^ 2) := (sqrt_sq hsum_nn).symm
    _ ≤ √(B ^ 2 * (Fintype.card ι * (Fintype.card ι - 1 : ℕ) * T)) := sqrt_le_sqrt hsq_bd
    _ = B * √(Fintype.card ι * (Fintype.card ι - 1 : ℕ) * T) := by
        rw [sqrt_mul (sq_nonneg B), sqrt_sq hB0]

end InternalRegretMatching

end Cslib.MachineLearning.OnlineLearning.Experts
