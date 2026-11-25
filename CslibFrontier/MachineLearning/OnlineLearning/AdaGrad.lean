/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.DynamicRegret
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adaptive online gradient descent (AdaGrad)

Self-tuning, data-dependent online gradient descent [Hazan2022, Orabona2019]: instead of tuning a
step size using an a priori gradient norm bound `G` and horizon `T`, *AdaGrad* accumulates the
squared gradient norms seen so far and scales the step size inversely by their square root.

* **Scalar `AdaGrad-Norm`** (`adaGradNorm`) on any real inner product space `E` with a Pythagorean
  projection `proj` onto `K`: tracks `S (t + 1) = ε + ∑ s ≤ t, ‖grad s (x s)‖ ^ 2` and steps with
  `η t = γ / √(S (t + 1))`. With optimal scale `γ = D / √2`, its regret over `T` rounds is at most
  `√2 * D * √(ε + ∑ t < T, ‖grad t (x t)‖ ^ 2) - (D / √2) * √ε` (with `ε = 0` permitted via Lean's
  `0 / 0 = 0` convention when an initial prefix of subgradients vanishes). In the worst case
  `‖g t‖ ≤ G` with `ε = 0`, this gives `√2 * G * D * √T`, tightening `3 / 2 * G * D * √T` without
  knowing `G` or `T`.
* **Coordinate-wise diagonal `AdaGrad`** (`adaGradBox`) on an axis-aligned box
  `∏ i, [l i, r i] ⊆ (ι → ℝ)`: runs per-coordinate clamping `clampProj (l i) (r i)` with an
  independent adaptive step size `γ / √(ε + ∑ s ≤ t, (grad s (x s) i) ^ 2)` on each coordinate
  `i : ι`. Because diagonal Mahalanobis projection onto a box separates across coordinates, the
  regret decomposes into the `d` scalar sums
  `∑ i, ((r i - l i) ^ 2 / (2 * γ) + γ) * √(ε + ∑ t < T, (grad t (x t) i) ^ 2)`.
  When `r i - l i ≤ D∞` and `γ = D∞ / √2`, this gives
  `√2 * D∞ * ∑ i, √(ε + ∑ t < T, (grad t (x t) i) ^ 2) - (D∞ / √2) * card ι * √ε`, strictly
  improving over the dense bound `√(card ι * ∑ i, S_i)` whenever gradients are sparse.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.AdaGradState`: named state `(point, sqGradSum)` of
  scalar `AdaGrad-Norm`.
* `Cslib.MachineLearning.OnlineLearning.OCO.adaGradNorm`,
  `Cslib.MachineLearning.OnlineLearning.OCO.adaGradNormSqSum`: iterates and accumulated squared
  gradient norm of scalar `AdaGrad-Norm`.
* `Cslib.MachineLearning.OnlineLearning.OCO.clampProj`: 1D projection onto `[a, b]`.
* `Cslib.MachineLearning.OnlineLearning.OCO.adaGradBox`: coordinate-wise diagonal `AdaGrad` on an
  axis-aligned box `∏ i, [l i, r i]`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.sum_div_sqrt_cumsum_le`: elementary telescoping
  bound `∑ t < T, a t / √(ε + ∑ s ≤ t, a s) ≤ 2 * (√(ε + ∑ t < T, a t) - √ε)`.
* `Cslib.MachineLearning.OnlineLearning.OCO.adaGradNorm_dynamic_regret_le`: data-dependent dynamic
  regret bound against any comparator sequence `u : ℕ → E` in `K`.
* `Cslib.MachineLearning.OnlineLearning.OCO.adaGradNorm_regret_le`,
  `Cslib.MachineLearning.OnlineLearning.OCO.adaGradNorm_regret_le_optimal`: static `AdaGrad-Norm`
  regret bounds (`√2 * D * √(ε + ∑ ‖g t‖ ^ 2)`).
* `Cslib.MachineLearning.OnlineLearning.OCO.adaGradBox_regret_le`,
  `Cslib.MachineLearning.OnlineLearning.OCO.adaGradBox_regret_le_optimal`: diagonal `AdaGrad`
  regret bounds on a finite-dimensional box.

## References

Exact section, theorem, and page locators below are unverified against primary PDFs (pending an
outside-fleet source check).

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022] (locator unverified)
* [F. Orabona, *A Modern Introduction to Online Learning*][Orabona2019] (locator unverified)
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

/-- **Telescoping square-root lemma** for adaptive gradient methods: for any nonnegative sequence
`a : ℕ → ℝ` and `ε ≥ 0`,
`∑ t ∈ range T, a t / √(ε + ∑ s ∈ range (t + 1), a s) ≤ 2 * (√(ε + ∑ t ∈ range T, a t) - √ε)`.
Works even at `ε = 0` when an initial prefix of `a` vanishes (using `0 / 0 = 0`). -/
theorem sum_div_sqrt_cumsum_le {a : ℕ → ℝ} (ha : ∀ t, 0 ≤ a t) {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    ∑ t ∈ range T, a t / √(ε + ∑ s ∈ range (t + 1), a s) ≤
      2 * (√(ε + ∑ t ∈ range T, a t) - √ε) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ a T]
    set S₀ := ε + ∑ s ∈ range T, a s
    set S₁ := ε + (∑ s ∈ range T, a s + a T)
    have hS₀ : 0 ≤ S₀ := add_nonneg hε (sum_nonneg fun s _ => ha s)
    have haT : 0 ≤ a T := ha T
    have hS₁ : S₁ = S₀ + a T := by ring
    have hstep : a T / √S₁ ≤ 2 * (√S₁ - √S₀) := by
      rcases (by linarith : 0 ≤ S₁).eq_or_lt with h0 | hpos
      · rw [show a T = 0 by linarith, zero_div, ← h0, show S₀ = 0 by linarith, sqrt_zero,
          sub_self, mul_zero]
      · rw [div_le_iff₀ (sqrt_pos.mpr hpos)]
        nlinarith [sq_sqrt (by linarith : 0 ≤ S₁), sq_sqrt hS₀, sq_nonneg (√S₁ - √S₀),
          sqrt_nonneg S₀, sqrt_nonneg S₁]
    linarith

section AdaGradNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Named state of scalar `AdaGrad-Norm`: current iterate and accumulated squared gradient norm. -/
structure AdaGradState (E : Type*) where
  /-- Current decision point in `E`. -/
  point : E
  /-- Accumulated sum `ε + ∑ s < t, ‖grad s (point s)‖ ^ 2`. -/
  sqGradSum : ℝ

/-- Full causal state sequence of scalar `AdaGrad-Norm` starting at `(x₀, ε)` with scale `γ`. -/
noncomputable def adaGradNormState (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) :
    ℕ → AdaGradState E
  | 0 => ⟨x₀, ε⟩
  | t + 1 =>
    let st := adaGradNormState proj grad γ ε x₀ t
    let g := grad t st.point
    let s' := st.sqGradSum + ‖g‖ ^ 2
    ⟨proj (st.point - (γ / √s') • g), s'⟩

/-- Decision point sequence of scalar `AdaGrad-Norm`. -/
noncomputable def adaGradNorm (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) (t : ℕ) : E :=
  (adaGradNormState proj grad γ ε x₀ t).point

/-- Accumulated squared gradient norm `ε + ∑ s < t, ‖grad s (x s)‖ ^ 2` of scalar
`AdaGrad-Norm`. -/
noncomputable def adaGradNormSqSum (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E)
    (t : ℕ) : ℝ :=
  (adaGradNormState proj grad γ ε x₀ t).sqGradSum

@[simp] theorem adaGradNorm_zero (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) :
    adaGradNorm proj grad γ ε x₀ 0 = x₀ := by rfl

@[simp] theorem adaGradNormSqSum_zero (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) :
    adaGradNormSqSum proj grad γ ε x₀ 0 = ε := by rfl

theorem adaGradNormSqSum_succ (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) (t : ℕ) :
    adaGradNormSqSum proj grad γ ε x₀ (t + 1) =
      adaGradNormSqSum proj grad γ ε x₀ t +
        ‖grad t (adaGradNorm proj grad γ ε x₀ t)‖ ^ 2 := by rfl

theorem adaGradNorm_succ (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) (t : ℕ) :
    adaGradNorm proj grad γ ε x₀ (t + 1) =
      proj (adaGradNorm proj grad γ ε x₀ t -
        (γ / √(adaGradNormSqSum proj grad γ ε x₀ (t + 1))) •
          grad t (adaGradNorm proj grad γ ε x₀ t)) := by rfl

theorem adaGradNormSqSum_eq (proj : E → E) (grad : ℕ → E → E) (γ ε : ℝ) (x₀ : E) (t : ℕ) :
    adaGradNormSqSum proj grad γ ε x₀ t =
      ε + ∑ s ∈ range t, ‖grad s (adaGradNorm proj grad γ ε x₀ s)‖ ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih => rw [adaGradNormSqSum_succ, ih, sum_range_succ]; ring

theorem adaGradNorm_mem {K : Set E} {proj : E → E} (hP : IsPythagoreanProjection K proj)
    {x₀ : E} (hx₀ : x₀ ∈ K) (grad : ℕ → E → E) (γ ε : ℝ) (t : ℕ) :
    adaGradNorm proj grad γ ε x₀ t ∈ K := by
  cases t with
  | zero => exact hx₀
  | succ t => rw [adaGradNorm_succ]; exact hP.mem _

private theorem adaGradNorm_step_le {K : Set E} {proj : E → E}
    (hP : IsPythagoreanProjection K proj) {grad : ℕ → E → E} {γ ε : ℝ} (hγ : 0 < γ)
    (hε : 0 ≤ ε) {x₀ u : E} (hu : u ∈ K) (t : ℕ) :
    let x := adaGradNorm proj grad γ ε x₀
    let S := adaGradNormSqSum proj grad γ ε x₀
    2 * ⟪grad t (x t), x t - u⟫ ≤
      √(S (t + 1)) / γ * (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) +
        γ * (‖grad t (x t)‖ ^ 2 / √(S (t + 1))) := by
  set x := adaGradNorm proj grad γ ε x₀
  set S := adaGradNormSqSum proj grad γ ε x₀
  have hSn : 0 ≤ S t := by
    change 0 ≤ adaGradNormSqSum _ _ _ _ _ t; rw [adaGradNormSqSum_eq]
    exact add_nonneg hε (sum_nonneg fun _ _ => sq_nonneg _)
  have hS1_nn : 0 ≤ S (t + 1) := by
    change 0 ≤ S t + ‖grad t (x t)‖ ^ 2; exact add_nonneg hSn (sq_nonneg _)
  rcases hS1_nn.eq_or_lt with hzero | hpos
  · have hg : grad t (x t) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by
      have : S t + ‖grad t (x t)‖ ^ 2 = 0 := hzero.symm; linarith [sq_nonneg ‖grad t (x t)‖]))
    simp [hg, ← hzero]
  · set r := √(S (t + 1)); have hr : 0 < r := sqrt_pos.mpr hpos
    set η := γ / r; have hη : 0 < η := div_pos hγ hr
    have hproj : ‖x (t + 1) - u‖ ^ 2 ≤ ‖x t - η • grad t (x t) - u‖ ^ 2 := by
      rw [show x (t + 1) = proj (x t - η • grad t (x t)) from adaGradNorm_succ _ _ _ _ _ t]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_sub_le _ u hu) 2
    have hexp : ‖x t - η • grad t (x t) - u‖ ^ 2 =
        ‖x t - u‖ ^ 2 - 2 * η * ⟪grad t (x t), x t - u⟫ + η ^ 2 * ‖grad t (x t)‖ ^ 2 := by
      rw [show x t - η • grad t (x t) - u = (x t - u) - η • grad t (x t) by abel,
        norm_sub_sq_real, norm_smul, real_inner_smul_right, real_inner_comm, Real.norm_eq_abs,
        abs_of_pos hη]; ring
    have hdiv := div_le_div_of_nonneg_right
      (by linarith : 2 * η * ⟪grad t (x t), x t - u⟫ ≤
        ‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2 + η ^ 2 * ‖grad t (x t)‖ ^ 2) hη.le
    rwa [show 2 * η * ⟪grad t (x t), x t - u⟫ / η = 2 * ⟪grad t (x t), x t - u⟫ by field_simp,
      show (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2 + η ^ 2 * ‖grad t (x t)‖ ^ 2) / η =
        r / γ * (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) + γ * (‖grad t (x t)‖ ^ 2 / r) by
        simp only [η]; field_simp] at hdiv

/-- Linearized dynamic regret bound for scalar `AdaGrad-Norm` against any sequence of comparators
`u : ℕ → E` in `K`. -/
theorem adaGradNorm_dynamic_sum_inner_le {K : Set E} {proj : E → E}
    (hP : IsPythagoreanProjection K proj) {x₀ : E} (hx₀ : x₀ ∈ K) {D γ ε : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hγ : 0 < γ) (hε : 0 ≤ ε)
    {grad : ℕ → E → E} {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T, ⟪grad t (adaGradNorm proj grad γ ε x₀ t),
        adaGradNorm proj grad γ ε x₀ t - u t⟫ ≤
      (D ^ 2 / (2 * γ) + D / γ * pathLength u T + γ) *
        √(ε + ∑ t ∈ range T, ‖grad t (adaGradNorm proj grad γ ε x₀ t)‖ ^ 2) - γ * √ε := by
  set x := adaGradNorm proj grad γ ε x₀
  set S := adaGradNormSqSum proj grad γ ε x₀
  have hD0 : 0 ≤ D := (norm_nonneg (x₀ - u 0)).trans (hD _ hx₀ _ (hu 0))
  have hS_mono (t : ℕ) : S t ≤ S (t + 1) := by
    have : S (t + 1) = S t + ‖grad t (x t)‖ ^ 2 := adaGradNormSqSum_succ _ _ _ _ _ t
    linarith [sq_nonneg ‖grad t (x t)‖]
  cases T with
  | zero =>
    simp only [range_zero, sum_empty, pathLength_zero, mul_zero, add_zero]
    linarith [show 0 ≤ D ^ 2 / (2 * γ) * √ε by positivity]
  | succ T =>
    have key (k : ℕ) : 2 * ∑ t ∈ range (k + 1), ⟪grad t (x t), x t - u t⟫ ≤
        √(S (k + 1)) / γ * (D ^ 2 - ‖x (k + 1) - u k‖ ^ 2) +
          (2 * D / γ) * pathLength u (k + 1) * √(S (k + 1)) +
          γ * ∑ t ∈ range (k + 1), ‖grad t (x t)‖ ^ 2 / √(S (t + 1)) := by
      induction k with
      | zero =>
        have hs := adaGradNorm_step_le hP hγ hε (hu 0) 0 (grad := grad) (x₀ := x₀)
        simp only [zero_add, range_one, sum_singleton, pathLength_one, mul_zero, zero_mul, add_zero]
        have hd0 : ‖x 0 - u 0‖ ^ 2 ≤ D ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hD _ hx₀ _ (hu 0)) 2
        have := mul_le_mul_of_nonneg_left (by linarith : ‖x 0 - u 0‖ ^ 2 - ‖x 1 - u 0‖ ^ 2 ≤
          D ^ 2 - ‖x 1 - u 0‖ ^ 2) (div_nonneg (sqrt_nonneg (S 1)) hγ.le)
        linarith
      | succ k ih =>
        have hstep := adaGradNorm_step_le hP hγ hε (hu (k + 1)) (k + 1) (grad := grad) (x₀ := x₀)
        have hr_le : √(S (k + 1)) ≤ √(S (k + 2)) := sqrt_le_sqrt (hS_mono (k + 1))
        have hmem := adaGradNorm_mem hP hx₀ grad γ ε (k + 1)
        have hd_le := pow_le_pow_left₀ (norm_nonneg _) (hD _ hmem _ (hu (k + 1))) 2
        have h1 := mul_le_mul_of_nonneg_left
          (norm_sub_sq_sub_le (hD _ hmem _ (hu k)) (hD _ hmem _ (hu (k + 1))))
          (div_nonneg (sqrt_nonneg (S (k + 1))) hγ.le)
        have h2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hr_le hγ.le)
          (sub_nonneg.mpr hd_le)
        have h3 : (2 * D / γ) * (pathLength u (k + 1) + ‖u (k + 1) - u k‖) * √(S (k + 1)) ≤
            (2 * D / γ) * pathLength u (k + 2) * √(S (k + 2)) := by
          rw [pathLength_succ_succ]
          exact mul_le_mul_of_nonneg_left hr_le
            (mul_nonneg (by positivity) (add_nonneg (pathLength_nonneg _ _) (norm_nonneg _)))
        rw [sum_range_succ, sum_range_succ (fun t => ‖grad t (x t)‖ ^ 2 / √(S (t + 1)))]
        linarith [show √(S (k + 1)) / γ * (2 * D * ‖u (k + 1) - u k‖) =
            (2 * D / γ) * ‖u (k + 1) - u k‖ * √(S (k + 1)) by ring,
          show (2 * D / γ) * pathLength u (k + 1) * √(S (k + 1)) +
            (2 * D / γ) * ‖u (k + 1) - u k‖ * √(S (k + 1)) =
            (2 * D / γ) * (pathLength u (k + 1) + ‖u (k + 1) - u k‖) * √(S (k + 1)) by ring,
          show √(S (k + 2)) / γ * (D ^ 2 - ‖x (k + 1) - u (k + 1)‖ ^ 2) +
            √(S (k + 2)) / γ * (‖x (k + 1) - u (k + 1)‖ ^ 2 - ‖x (k + 2) - u (k + 1)‖ ^ 2) =
            √(S (k + 2)) / γ * (D ^ 2 - ‖x (k + 2) - u (k + 1)‖ ^ 2) by ring]
    have hk := key T
    have hrem : 0 ≤ √(S (T + 1)) / γ * ‖x (T + 1) - u T‖ ^ 2 := by positivity
    have heq (t : ℕ) : ε + ∑ s ∈ range t, ‖grad s (x s)‖ ^ 2 = S t :=
      (adaGradNormSqSum_eq _ _ _ _ _ t).symm
    have hcs := sum_div_sqrt_cumsum_le (fun t => sq_nonneg ‖grad t (x t)‖) hε (T + 1)
    simp only [heq] at hcs
    have hmul := mul_le_mul_of_nonneg_left hcs hγ.le
    rw [← adaGradNormSqSum_eq proj grad γ ε x₀ (T + 1)]
    linarith [show √(S (T + 1)) / γ * (D ^ 2 - ‖x (T + 1) - u T‖ ^ 2) =
        D ^ 2 / γ * √(S (T + 1)) - √(S (T + 1)) / γ * ‖x (T + 1) - u T‖ ^ 2 by ring,
      show 2 * ((D ^ 2 / (2 * γ) + D / γ * pathLength u (T + 1) + γ) * √(S (T + 1)) - γ * √ε) =
        D ^ 2 / γ * √(S (T + 1)) + (2 * D / γ) * pathLength u (T + 1) * √(S (T + 1)) +
        γ * (2 * (√(S (T + 1)) - √ε)) by ring]

/-- **Dynamic regret of `AdaGrad-Norm`**: without knowing a gradient bound `G` or horizon `T`,
scalar `AdaGrad-Norm` incurs data-dependent regret against any sequence `u` in `K`. -/
theorem adaGradNorm_dynamic_regret_le {K : Set E} {proj : E → E} {f : ℕ → E → ℝ}
    {grad : ℕ → E → E} (hP : IsPythagoreanProjection K proj) {x₀ : E} (hx₀ : x₀ ∈ K)
    {D γ ε : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradNorm proj grad γ ε x₀ t) - f t (u t)) ≤
      (D ^ 2 / (2 * γ) + D / γ * pathLength u T + γ) *
        √(ε + ∑ t ∈ range T, ‖grad t (adaGradNorm proj grad γ ε x₀ t)‖ ^ 2) - γ * √ε :=
  (sum_sub_le_sum_inner_dynamic hsub (adaGradNorm_mem hP hx₀ grad γ ε) hu T).trans
    (adaGradNorm_dynamic_sum_inner_le hP hx₀ hD hγ hε hu T)

/-- **Static regret of `AdaGrad-Norm`** [Orabona2019]: for any scale `γ > 0` and offset
`ε ≥ 0`, regret against every comparator `u ∈ K` is at most
`(D ^ 2 / (2 * γ) + γ) * √(ε + ∑ t < T, ‖grad t (x t)‖ ^ 2) - γ * √ε`. -/
theorem adaGradNorm_regret_le {K : Set E} {proj : E → E} {f : ℕ → E → ℝ} {grad : ℕ → E → E}
    (hP : IsPythagoreanProjection K proj) {x₀ : E} (hx₀ : x₀ ∈ K) {D γ ε : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradNorm proj grad γ ε x₀ t) - f t u) ≤
      (D ^ 2 / (2 * γ) + γ) *
        √(ε + ∑ t ∈ range T, ‖grad t (adaGradNorm proj grad γ ε x₀ t)‖ ^ 2) - γ * √ε := by
  have h := adaGradNorm_dynamic_regret_le (f := f) hP hx₀ hD hγ hε hsub (u := fun _ => u)
    (fun _ => hu) T
  simpa only [pathLength_const, mul_zero, add_zero] using h

/-- **Optimally scaled `AdaGrad-Norm`**: choosing `γ = D / √2` minimizes `D ^ 2 / (2 * γ) + γ` to
`√2 * D`, giving data-dependent regret at most
`√2 * D * √(ε + ∑ t < T, ‖grad t (x t)‖ ^ 2) - (D / √2) * √ε` without prior knowledge of `G` or
`T`. -/
theorem adaGradNorm_regret_le_optimal {K : Set E} {proj : E → E} {f : ℕ → E → ℝ}
    {grad : ℕ → E → E} (hP : IsPythagoreanProjection K proj) {x₀ : E} (hx₀ : x₀ ∈ K)
    {D ε : ℝ} (hD0 : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hε : 0 ≤ ε)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradNorm proj grad (D / √2) ε x₀ t) - f t u) ≤
      √2 * D * √(ε + ∑ t ∈ range T, ‖grad t (adaGradNorm proj grad (D / √2) ε x₀ t)‖ ^ 2) -
        D / √2 * √ε := by
  have hsq2 : 0 < √(2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have h := adaGradNorm_regret_le (f := f) (grad := grad) hP hx₀ hD (div_pos hD0 hsq2) hε hsub hu T
  rwa [show D ^ 2 / (2 * (D / √2)) + D / √2 = √2 * D by
    field_simp; nlinarith [mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]] at h

/-- Worst-case `O(G * D * √T)` bound for `AdaGrad-Norm`: when `‖grad t x‖ ≤ G` on `K` and
`ε = 0`, `AdaGrad-Norm` with `γ = D / √2` guarantees regret at most `√2 * G * D * √T`. -/
theorem adaGradNorm_regret_le_sqrt {K : Set E} {proj : E → E} {f : ℕ → E → ℝ} {grad : ℕ → E → E}
    (hP : IsPythagoreanProjection K proj) {x₀ : E} (hx₀ : x₀ ∈ K) {D G : ℝ}
    (hD0 : 0 < D) (hG0 : 0 ≤ G) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradNorm proj grad (D / √2) 0 x₀ t) - f t u) ≤
      √2 * G * D * √(T : ℝ) := by
  have h := adaGradNorm_regret_le_optimal (f := f) (grad := grad) hP hx₀ hD0 hD le_rfl hsub hu T
  simp only [zero_add, sqrt_zero, mul_zero, sub_zero] at h
  have hsum : ∑ t ∈ range T, ‖grad t (adaGradNorm proj grad (D / √2) 0 x₀ t)‖ ^ 2 ≤
      (T : ℝ) * G ^ 2 :=
    (sum_le_sum fun t _ => pow_le_pow_left₀ (norm_nonneg _)
      (hG t _ (adaGradNorm_mem hP hx₀ grad (D / √2) 0 t)) 2).trans_eq
      (by simp [sum_const, card_range, nsmul_eq_mul])
  have hsqrt : √(∑ t ∈ range T, ‖grad t (adaGradNorm proj grad (D / √2) 0 x₀ t)‖ ^ 2) ≤
      G * √(T : ℝ) :=
    (sqrt_le_sqrt hsum).trans_eq (by rw [sqrt_mul (Nat.cast_nonneg T), sqrt_sq hG0]; ring)
  exact h.trans ((mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans_eq (by ring))

end AdaGradNorm

section DiagonalAdaGrad

/-- One-dimensional projection clamping a real number into `[a, b]`. -/
@[expose] def clampProj (a b z : ℝ) : ℝ := min (max z a) b

/-- `clampProj a b` is a Pythagorean projection onto `Set.Icc a b` whenever `a ≤ b`. -/
theorem isPythagoreanProjection_clampProj {a b : ℝ} (hab : a ≤ b) :
    IsPythagoreanProjection (Set.Icc a b) (clampProj a b) where
  mem _ := ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩
  norm_sub_le y z := fun ⟨hza, hzb⟩ => by
    simp only [Real.norm_eq_abs, clampProj, abs_le]
    constructor <;> rcases le_total y a with _ | _ <;> rcases le_total y b with _ | _ <;>
      simp only [min_def, max_def] at * <;>
      split_ifs <;> linarith [le_abs_self (y - z), neg_le_abs (y - z), abs_nonneg (y - z)]

/-- State of coordinate-wise diagonal `AdaGrad` on an axis-aligned box over `ι`. -/
structure AdaGradBoxState (ι : Type*) where
  /-- Current iterate `ι → ℝ`. -/
  point : ι → ℝ
  /-- Per-coordinate accumulated sum `ε + ∑ s < t, (grad s (point s) i) ^ 2`. -/
  sqGradSum : ι → ℝ

/-- Axis-aligned box `∏ i, [l i, r i]`. -/
abbrev Box {ι : Type*} (l r : ι → ℝ) : Set (ι → ℝ) := {x | ∀ i, l i ≤ x i ∧ x i ≤ r i}

/-- Full causal state sequence of diagonal `AdaGrad` on the box `Box l r` with scale `γ` and
offset `ε` [Hazan2022]. -/
noncomputable def adaGradBoxState {ι : Type*} (l r : ι → ℝ)
    (grad : ℕ → (ι → ℝ) → (ι → ℝ)) (γ ε : ℝ) (x₀ : ι → ℝ) : ℕ → AdaGradBoxState ι
  | 0 => ⟨x₀, fun _ => ε⟩
  | t + 1 =>
    let st := adaGradBoxState l r grad γ ε x₀ t
    let g := grad t st.point
    let s' := fun i => st.sqGradSum i + (g i) ^ 2
    ⟨fun i => clampProj (l i) (r i) (st.point i - (γ / √(s' i)) * g i), s'⟩

/-- Iterate sequence of coordinate-wise diagonal `AdaGrad` on `Box l r`. -/
noncomputable def adaGradBox {ι : Type*} (l r : ι → ℝ)
    (grad : ℕ → (ι → ℝ) → (ι → ℝ)) (γ ε : ℝ) (x₀ : ι → ℝ) (t : ℕ) : ι → ℝ :=
  (adaGradBoxState l r grad γ ε x₀ t).point

theorem adaGradBox_mem {ι : Type*} {l r : ι → ℝ} (hlr : ∀ i, l i ≤ r i)
    (grad : ℕ → (ι → ℝ) → (ι → ℝ)) (γ ε : ℝ) {x₀ : ι → ℝ} (hx₀ : x₀ ∈ Box l r) (t : ℕ) :
    adaGradBox l r grad γ ε x₀ t ∈ Box l r := by
  cases t with
  | zero => exact hx₀
  | succ t =>
    intro i
    exact (isPythagoreanProjection_clampProj (hlr i)).mem _

private theorem adaGradBox_coord_eq {ι : Type*} (l r : ι → ℝ)
    (grad : ℕ → (ι → ℝ) → (ι → ℝ)) (γ ε : ℝ) (x₀ : ι → ℝ) (i : ι) (t : ℕ) :
    (adaGradBoxState l r grad γ ε x₀ t).point i =
      adaGradNorm (clampProj (l i) (r i))
        (fun s _ => grad s (adaGradBox l r grad γ ε x₀ s) i) γ ε (x₀ i) t ∧
    (adaGradBoxState l r grad γ ε x₀ t).sqGradSum i =
      adaGradNormSqSum (clampProj (l i) (r i))
        (fun s _ => grad s (adaGradBox l r grad γ ε x₀ s) i) γ ε (x₀ i) t := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    constructor
    · simp only [adaGradBoxState, adaGradNorm_succ, adaGradNormSqSum_succ, ← ih.1, ← ih.2,
        Real.norm_eq_abs, sq_abs, smul_eq_mul]
      rfl
    · simp only [adaGradBoxState, adaGradNormSqSum_succ, ← ih.2, Real.norm_eq_abs, sq_abs]
      rfl

/-- **Diagonal `AdaGrad` regret on an axis-aligned box** [Hazan2022]: each coordinate runs an
independent adaptive step size `γ / √(ε + ∑ s ≤ t, (grad s (x s) i) ^ 2)`. With no prior bound
on the gradient norms, the regret decomposes per coordinate as
`∑ i, ((r i - l i) ^ 2 / (2 * γ) + γ) * √(ε + ∑ t < T, (grad t (x t) i) ^ 2) - γ * card ι * √ε`.
-/
theorem adaGradBox_regret_le {ι : Type*} [Fintype ι] {l r : ι → ℝ} (hlr : ∀ i, l i ≤ r i)
    {f : ℕ → (ι → ℝ) → ℝ} {grad : ℕ → (ι → ℝ) → (ι → ℝ)} {x₀ u : ι → ℝ}
    (hx₀ : x₀ ∈ Box l r) (hu : u ∈ Box l r) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hsub : ∀ t, ∀ x ∈ Box l r, ∀ y ∈ Box l r,
      f t x + ∑ i : ι, grad t x i * (y i - x i) ≤ f t y)
    (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradBox l r grad γ ε x₀ t) - f t u) ≤
      ∑ i : ι, ((r i - l i) ^ 2 / (2 * γ) + γ) *
          √(ε + ∑ t ∈ range T, (grad t (adaGradBox l r grad γ ε x₀ t) i) ^ 2) -
        γ * (Fintype.card ι : ℝ) * √ε := by
  set x := adaGradBox l r grad γ ε x₀
  have hlin : ∑ t ∈ range T, (f t (x t) - f t u) ≤
      ∑ i : ι, ∑ t ∈ range T, grad t (x t) i * (x t i - u i) := by
    rw [← sum_comm]
    refine sum_le_sum fun t _ => ?_
    have h := hsub t (x t) (adaGradBox_mem hlr grad γ ε hx₀ t) u hu
    linarith [show ∑ i : ι, grad t (x t) i * (u i - x t i) =
      - ∑ i : ι, grad t (x t) i * (x t i - u i) by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => by ring]
  have hcoord (i : ι) : ∑ t ∈ range T, grad t (x t) i * (x t i - u i) ≤
      ((r i - l i) ^ 2 / (2 * γ) + γ) * √(ε + ∑ t ∈ range T, (grad t (x t) i) ^ 2) - γ * √ε := by
    have hDi : ∀ a ∈ Set.Icc (l i) (r i), ∀ b ∈ Set.Icc (l i) (r i), ‖a - b‖ ≤ r i - l i :=
      fun a ha b hb => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    have hbase := adaGradNorm_dynamic_sum_inner_le (K := Set.Icc (l i) (r i))
      (grad := fun s _ => grad s (x s) i) (isPythagoreanProjection_clampProj (hlr i)) (hx₀ i)
      hDi hγ hε (u := fun _ => u i) (fun _ => hu i) T
    simp only [pathLength_const, mul_zero, add_zero, Real.norm_eq_abs, sq_abs] at hbase
    refine (sum_congr rfl fun t _ => ?_).trans_le hbase
    change grad t (x t) i * ((adaGradBoxState l r grad γ ε x₀ t).point i - u i) =
      (adaGradNorm (clampProj (l i) (r i))
        (fun s _ => grad s (x s) i) γ ε (x₀ i) t - u i) * grad t (x t) i
    rw [(adaGradBox_coord_eq l r grad γ ε x₀ i t).1, mul_comm]
  exact hlin.trans ((sum_le_sum fun i _ => hcoord i).trans_eq
    (by rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]; ring))

/-- **Optimally scaled diagonal `AdaGrad` on an `ℓ∞`-bounded box**: when `r i - l i ≤ D` for
every coordinate `i : ι` with `D > 0`, choosing `γ = D / √2` gives
`√2 * D * ∑ i, √(ε + ∑ t < T, (grad t (x t) i) ^ 2) - D / √2 * card ι * √ε`. -/
theorem adaGradBox_regret_le_optimal {ι : Type*} [Fintype ι] {l r : ι → ℝ} (hlr : ∀ i, l i ≤ r i)
    {D ε : ℝ} (hD0 : 0 < D) (hwidth : ∀ i, r i - l i ≤ D) (hε : 0 ≤ ε)
    {f : ℕ → (ι → ℝ) → ℝ} {grad : ℕ → (ι → ℝ) → (ι → ℝ)} {x₀ u : ι → ℝ}
    (hx₀ : x₀ ∈ Box l r) (hu : u ∈ Box l r)
    (hsub : ∀ t, ∀ x ∈ Box l r, ∀ y ∈ Box l r,
      f t x + ∑ i : ι, grad t x i * (y i - x i) ≤ f t y)
    (T : ℕ) :
    ∑ t ∈ range T, (f t (adaGradBox l r grad (D / √2) ε x₀ t) - f t u) ≤
      √2 * D * ∑ i : ι, √(ε + ∑ t ∈ range T,
          (grad t (adaGradBox l r grad (D / √2) ε x₀ t) i) ^ 2) -
        D / √2 * (Fintype.card ι : ℝ) * √ε := by
  have hsq2 : 0 < √(2 : ℝ) := sqrt_pos.mpr (by norm_num)
  refine (adaGradBox_regret_le hlr (f := f) (grad := grad) hx₀ hu (div_pos hD0 hsq2) hε hsub
    T).trans ((sub_le_sub_right (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_
      (sqrt_nonneg _)) _).trans_eq (by rw [← mul_sum]))
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr (hlr i)) (hwidth i) 2
  exact (by gcongr : _ ≤ D ^ 2 / (2 * (D / √2)) + D / √2).trans_eq
    (by field_simp; nlinarith [mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)])

end DiagonalAdaGrad

end Cslib.MachineLearning.OnlineLearning.OCO
