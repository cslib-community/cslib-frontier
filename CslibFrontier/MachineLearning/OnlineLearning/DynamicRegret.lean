/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.OnlineGradientDescent
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dynamic regret of online gradient descent

Extends `CslibFrontier.MachineLearning.OnlineLearning.OnlineGradientDescent` from a fixed
comparator `u ∈ K` to an arbitrary sequence of comparators `u : ℕ → E` lying in a bounded convex
set `K` of a real inner product space [Zinkevich2003, Hazan2022]. The *path length* of `u` over
`T` rounds (indexed from `0`) is

  `pathLength u T = ∑ t ∈ Finset.range (T - 1), ‖u (t + 1) - u t‖`.

The dynamic regret over `T` rounds is `∑ t < T, (f t (x t) - f t (u t))`, generalizing static
regret (`pathLength (fun _ => u₀) T = 0`). Because `ogd` runs unchanged, the per-round triangle
estimate `‖x - u'‖ ^ 2 - ‖x - u‖ ^ 2 ≤ 2 * D * ‖u' - u‖` telescopes against `ogd_two_mul_inner_le`
to separate the comparator drift `pathLength u T` from the static diameter term `D`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.pathLength`: comparator path length `P_T`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.norm_sub_sq_sub_le`: squared-distance shift estimate
  `‖x - w‖ ^ 2 - ‖x - v‖ ^ 2 ≤ 2 * D * ‖w - v‖` (shared with `AdaGrad`).
* `Cslib.MachineLearning.OnlineLearning.OCO.sum_sub_le_sum_inner_dynamic`: subgradient
  linearization against a sequence of comparators `u : ℕ → E`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_sum_inner_le`: nonincreasing positive step
  sizes give the drift-weighted dynamic bound against any sequence `u` in `K`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_sum_inner_le_of_const`: constant step
  size `c > 0`, tracking `‖x₀ - u 0‖ ^ 2 / (2 * c) + D / c * pathLength u T`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_regret_le_fixed`: constant step size
  `D / (G * √T)` yields dynamic regret at most `G * (D + pathLength u T) * √T`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_regret_le_tuned`: path-length-tuned
  constant step size `√(D ^ 2 + 2 * D * P_T) / (G * √T)` yields dynamic regret at most
  `G * √(T * (D ^ 2 + 2 * D * pathLength u T))`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_regret_le_three_halves`: horizon-independent
  step sizes `D / (G * √(t + 1))` yield `(3 / 2 * D + pathLength u T) * G * √T`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_dynamic_regret_le_zinkevich`: Zinkevich's
  `1 / √(t + 1)` schedule yields `(D ^ 2 / 2 + D * pathLength u T) * √T + (√T - 1 / 2) * G ^ 2`
  (dynamic extension of [Zinkevich2003]).

## References

Exact section, theorem, and page locators below are unverified against primary PDFs (pending an
outside-fleet source check).

* [M. Zinkevich, *Online Convex Programming and Generalized Infinitesimal Gradient
  Ascent*][Zinkevich2003] (locator unverified)
* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022] (locator unverified)
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

section PathLength

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Path length `P_T = ∑_{t < T - 1} ‖u (t + 1) - u t‖` of a comparator sequence `u : ℕ → E` over
`T` rounds indexed from `0`. When `T ≤ 1` or `u` is constant, `pathLength u T = 0`. -/
@[expose] noncomputable def pathLength (u : ℕ → E) (T : ℕ) : ℝ :=
  ∑ t ∈ range (T - 1), ‖u (t + 1) - u t‖

@[simp] theorem pathLength_zero (u : ℕ → E) : pathLength u 0 = 0 := by
  simp [pathLength]

@[simp] theorem pathLength_one (u : ℕ → E) : pathLength u 1 = 0 := by
  simp [pathLength]

theorem pathLength_succ_succ (u : ℕ → E) (T : ℕ) :
    pathLength u (T + 2) = pathLength u (T + 1) + ‖u (T + 1) - u T‖ := by
  simp only [pathLength, Nat.add_sub_cancel]
  exact sum_range_succ _ T

theorem pathLength_nonneg (u : ℕ → E) (T : ℕ) : 0 ≤ pathLength u T :=
  sum_nonneg fun _ _ => norm_nonneg _

@[simp] theorem pathLength_const (u₀ : E) (T : ℕ) : pathLength (fun _ => u₀) T = 0 := by
  simp [pathLength]

end PathLength

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {K : Set E} {proj : E → E} {η : ℕ → ℝ} {grad : ℕ → E → E} {x₀ : E}

omit [InnerProductSpace ℝ E] in
/-- Difference of squared distances between a point `x` and two comparators `v, w` in a set of
diameter at most `D`: `‖x - w‖ ^ 2 - ‖x - v‖ ^ 2 ≤ 2 * D * ‖w - v‖`. -/
theorem norm_sub_sq_sub_le {D : ℝ} {x v w : E}
    (hv : ‖x - v‖ ≤ D) (hw : ‖x - w‖ ≤ D) :
    ‖x - w‖ ^ 2 - ‖x - v‖ ^ 2 ≤ 2 * D * ‖w - v‖ := by
  have hdiff : ‖x - w‖ - ‖x - v‖ ≤ ‖w - v‖ := sub_le_iff_le_add.mpr (by
    rw [add_comm, norm_sub_rev w v]
    exact norm_sub_le_norm_sub_add_norm_sub x v w)
  rw [sq_sub_sq]
  refine (mul_le_mul_of_nonneg_left hdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans ?_
  exact mul_le_mul_of_nonneg_right ((add_le_add hw hv).trans_eq (two_mul D).symm) (norm_nonneg _)

/-- Subgradient linearization for dynamic regret against any comparator sequence `u : ℕ → E` in
`K`: `∑ t < T, (f t (x t) - f t (u t)) ≤ ∑ t < T, ⟪grad t (x t), x t - u t⟫`. -/
theorem sum_sub_le_sum_inner_dynamic {f : ℕ → E → ℝ}
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {x u : ℕ → E}
    (hx : ∀ t, x t ∈ K) (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (x t) - f t (u t)) ≤ ∑ t ∈ range T, ⟪grad t (x t), x t - u t⟫ :=
  sum_le_sum fun t _ => by
    have h := hsub t (x t) (hx t) (u t) (hu t)
    rw [← neg_sub (x t) (u t), inner_neg_right] at h
    linarith

/-- Generic dynamic linearized-regret bound for `ogd` with positive nonincreasing step sizes on a
set of diameter at most `D`, keeping the per-step drift weight `1 / η t`. -/
theorem ogd_dynamic_sum_inner_le (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) {D : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hη : ∀ t, 0 < η t) (hanti : Antitone η)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u t⟫ ≤
      D ^ 2 / (2 * η T) + D * (∑ t ∈ range T, ‖u (t + 1) - u t‖ / η t) +
        (∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2) / 2 := by
  set x := ogd proj η grad x₀
  let a (t : ℕ) := ‖x t - u t‖ ^ 2
  let b (t : ℕ) := ‖x (t + 1) - u t‖ ^ 2
  let w (t : ℕ) := 1 / η t
  have hd (t s : ℕ) : ‖x t - u s‖ ≤ D := hD _ (ogd_mem hP hx₀ t) _ (hu s)
  have hcap (t : ℕ) : a t ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd t t) 2
  have htel := Fin.sum_range_mul_sub_le_of_adjacent w a b
    (fun t => 2 * D * (‖u (t + 1) - u t‖ / η t)) (D ^ 2) T
    (fun t _ => mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (hη (t + 1)) (hanti (Nat.le_succ t))) (sub_nonneg.mpr (hcap _)))
    (fun t _ => by
      dsimp only [w, a, b]
      rw [one_div_mul_eq_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (norm_sub_sq_sub_le (hd (t + 1) t) (hd (t + 1) (t + 1)))
        (hη t).le)
  have hsum := sum_le_sum (s := range (T + 1)) fun t _ =>
    ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP (hu t) t (hη t)
  rw [← mul_sum, sum_add_distrib] at hsum
  have hinitial := div_nonneg (sub_nonneg.mpr (hcap 0)) (hη 0).le
  have hfinal := div_nonneg (sq_nonneg ‖x (T + 1) - u T‖) (hη T).le
  simp only [a, b, w, one_div_mul_eq_div, sub_div, ← mul_sum] at htel hinitial hsum
  rw [mul_comm 2 (η T), ← div_div]
  linarith only [hsum, htel, hinitial, hfinal]

/-- Bounding the weighted drift in `ogd_dynamic_sum_inner_le` by the terminal step size `η T`
exposes the comparator path length `pathLength u (T + 1)`. -/
theorem ogd_dynamic_sum_inner_le_pathLength (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hη : ∀ t, 0 < η t) (hanti : Antitone η)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u t⟫ ≤
      (D ^ 2 / 2 + D * pathLength u (T + 1)) / η T +
        (∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2) / 2 := by
  have hbase := ogd_dynamic_sum_inner_le (grad := grad) hP hx₀ hD hη hanti hu T
  have hD0 : 0 ≤ D := (norm_nonneg (x₀ - u 0)).trans (hD _ hx₀ _ (hu 0))
  have hdrift : ∑ t ∈ range T, ‖u (t + 1) - u t‖ / η t ≤ pathLength u (T + 1) / η T := by
    simp only [pathLength, Nat.add_sub_cancel, sum_div]
    exact sum_le_sum fun t ht =>
      div_le_div_of_nonneg_left (norm_nonneg _) (hη T) (hanti (mem_range.mp ht).le)
  rw [add_div, div_div, mul_div_assoc]
  linarith [mul_le_mul_of_nonneg_left hdrift hD0]

/-- Dynamic linearized regret for `ogd` with a constant step size `c > 0`, keeping the exact
initial distance `‖x₀ - u 0‖ ^ 2 / (2 * c)` plus the comparator drift term
`D / c * pathLength u T`. -/
theorem ogd_dynamic_sum_inner_le_of_const (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {D c : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hc : 0 < c) {u : ℕ → E} (hu : ∀ t, u t ∈ K)
    (T : ℕ) :
    ∑ t ∈ range T, ⟪grad t (ogd proj (fun _ => c) grad x₀ t),
        ogd proj (fun _ => c) grad x₀ t - u t⟫ ≤
      ‖x₀ - u 0‖ ^ 2 / (2 * c) + D / c * pathLength u T +
        c * (∑ t ∈ range T, ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2) / 2 := by
  set x := ogd proj (fun _ => c) grad x₀
  cases T with
  | zero =>
    simpa using div_nonneg (sq_nonneg ‖x₀ - u 0‖) (mul_nonneg zero_le_two hc.le)
  | succ T =>
    let a (t : ℕ) := ‖x t - u t‖ ^ 2
    let b (t : ℕ) := ‖x (t + 1) - u t‖ ^ 2
    have hd (t s : ℕ) : ‖x t - u s‖ ≤ D := hD _ (ogd_mem hP hx₀ t) _ (hu s)
    have htel := Fin.sum_range_mul_sub_le_of_adjacent (fun _ => 1 / c) a b
      (fun t => 2 * D / c * ‖u (t + 1) - u t‖) 0 T (fun _ _ => le_rfl) (fun t _ => by
        dsimp only [a, b]
        rw [one_div_mul_eq_div, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (norm_sub_sq_sub_le (hd (t + 1) t) (hd (t + 1) (t + 1))) hc.le)
    have hsum := sum_le_sum (s := range (T + 1)) fun t _ =>
      ogd_two_mul_inner_le (η := fun _ => c) (x₀ := x₀) (grad := grad) hP (hu t) t hc
    rw [← mul_sum, sum_add_distrib, ← mul_sum] at hsum
    have hfinal := div_nonneg (sq_nonneg ‖x (T + 1) - u T‖) hc.le
    change _ ≤ ‖x₀ - u 0‖ ^ 2 / (2 * c) + D / c * pathLength u (T + 1) + _
    rw [mul_comm 2 c, ← div_div]
    have hpath : (∑ t ∈ range T, ‖u (t + 1) - u t‖) = pathLength u (T + 1) := by
      simp only [pathLength, Nat.add_sub_cancel]
    simp only [a, b, one_div_mul_eq_div, zero_sub, neg_div, neg_sub_neg,
      ← mul_sum, hpath, show x 0 = x₀ from ogd_zero] at htel
    rw [mul_div_assoc (2 : ℝ) D c, mul_assoc] at htel
    linarith only [hsum, htel, hfinal]

private theorem sum_ogd_grad_norm_sq_le (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {G : ℝ} (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G) (η : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤ (T : ℝ) * G ^ 2 := by
  calc ∑ t ∈ range T, ‖grad t (ogd proj η grad x₀ t)‖ ^ 2
      ≤ ∑ _ ∈ range T, G ^ 2 := sum_le_sum fun t _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2
    _ = (T : ℝ) * G ^ 2 := by simp [sum_const, card_range, nsmul_eq_mul]

private theorem ogd_dynamic_regret_le_of_const {f : ℕ → E → ℝ}
    (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) {D G c : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    (hc : 0 < c) {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun _ => c) grad x₀ t) - f t (u t)) ≤
      D ^ 2 / (2 * c) + D / c * pathLength u T + c * ((T : ℝ) * G ^ 2) / 2 := by
  refine (sum_sub_le_sum_inner_dynamic hsub (ogd_mem hP hx₀) hu T).trans ?_
  have h := ogd_dynamic_sum_inner_le_of_const (grad := grad) hP hx₀ hD hc hu T
  have hx0 : ‖x₀ - u 0‖ ^ 2 / (2 * c) ≤ D ^ 2 / (2 * c) :=
    div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hD _ hx₀ _ (hu 0)) 2) (by positivity)
  have hgrad := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (sum_ogd_grad_norm_sq_le (grad := grad) hP hx₀ hG (fun _ => c) T) hc.le) zero_le_two
  linarith

/-- **Dynamic regret of OGD with standard fixed step size** `η = D / (G * √T)`:
for a diameter-`D` set and `G`-bounded subgradients, dynamic regret over `T ≥ 1` rounds against
any comparator sequence `u` in `K` is at most `G * (D + pathLength u T) * √T`. When `u` is
constant (`pathLength u T = 0`), this matches `ogd_regret_le_fixed`. -/
theorem ogd_dynamic_regret_le_fixed {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun _ => D / (G * √(T : ℝ))) grad x₀ t) - f t (u t)) ≤
      G * (D + pathLength u T) * √(T : ℝ) := by
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hc : 0 < D / (G * √(T : ℝ)) := div_pos hD0 (mul_pos hG0 (sqrt_pos.mpr hTpos))
  refine (ogd_dynamic_regret_le_of_const hP hx₀ hD hG hsub hc hu T).trans_eq ?_
  field_simp
  nlinarith [sq_sqrt hTpos.le]

/-- **Optimal path-length-tuned dynamic regret of OGD** [Zinkevich2003] (locator unverified): when
an upper bound `P ≥ pathLength u T` is used to tune the constant step size
`η = √(D ^ 2 + 2 * D * P) / (G * √T)`, the dynamic regret over `T ≥ 1` rounds is at most
`G * √(T * (D ^ 2 + 2 * D * P))`. -/
theorem ogd_dynamic_regret_le_tuned {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G P : ℝ} (hD0 : 0 < D) (hG0 : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) {T : ℕ} (hT : 0 < T) (hpath : pathLength u T ≤ P) :
    ∑ t ∈ range T,
        (f t (ogd proj (fun _ => √(D ^ 2 + 2 * D * P) / (G * √(T : ℝ))) grad x₀ t) -
          f t (u t)) ≤
      G * √((T : ℝ) * (D ^ 2 + 2 * D * P)) := by
  have hP0 : 0 ≤ P := (pathLength_nonneg u T).trans hpath
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  set A := D ^ 2 + 2 * D * P
  have hApos : 0 < A := by positivity
  set c := √A / (G * √(T : ℝ)) with hcdef
  have hc : 0 < c := div_pos (sqrt_pos.mpr hApos) (mul_pos hG0 (sqrt_pos.mpr hTpos))
  refine (ogd_dynamic_regret_le_of_const hP hx₀ hD hG hsub hc hu T).trans ?_
  have halg : D ^ 2 / (2 * c) + D / c * P + c * ((T : ℝ) * G ^ 2) / 2 =
      G * (√(T : ℝ) * √A) := by
    have hsA : √A * √A = A := mul_self_sqrt hApos.le
    have hsT : √(T : ℝ) * √(T : ℝ) = (T : ℝ) := mul_self_sqrt hTpos.le
    rw [hcdef]
    calc D ^ 2 / (2 * (√A / (G * √(T : ℝ)))) + D / (√A / (G * √(T : ℝ))) * P +
            √A / (G * √(T : ℝ)) * ((T : ℝ) * G ^ 2) / 2
        = A * (G * √(T : ℝ)) / (2 * √A) + (√A * (T : ℝ) * G) / (2 * √(T : ℝ)) := by
            simp only [A]; field_simp
      _ = (√A * √A) * (G * √(T : ℝ)) / (2 * √A) +
            (√A * (√(T : ℝ) * √(T : ℝ)) * G) / (2 * √(T : ℝ)) := by rw [hsA, hsT]
      _ = G * (√(T : ℝ) * √A) / 2 + G * (√(T : ℝ) * √A) / 2 := by field_simp
      _ = G * (√(T : ℝ) * √A) := by ring
  rw [sqrt_mul hTpos.le A]
  linarith [mul_le_mul_of_nonneg_left hpath (div_nonneg hD0.le hc.le)]

/-- Linearized dynamic regret with step sizes `c / √(t + 1)` over `T + 1` rounds. -/
theorem ogd_dynamic_sum_inner_le_sqrt (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {D G c : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hc : 0 < c) {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t),
        ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t - u t⟫ ≤
      (D ^ 2 / 2 + D * pathLength u (T + 1)) / c * √((T : ℝ) + 1) +
        c * G ^ 2 * (√((T : ℝ) + 1) - 1 / 2) := by
  set η : ℕ → ℝ := fun t => c / √((t : ℝ) + 1) with hηdef
  have hη : ∀ t, 0 < η t := fun t => div_pos hc (sqrt_pos.mpr (by positivity))
  have h := ogd_dynamic_sum_inner_le_pathLength (grad := grad) hP hx₀ hD hη
    (fun _ _ hab => by
      simp only [hηdef]
      gcongr) hu T
  rw [hηdef, div_div_eq_mul_div, mul_div_right_comm] at h
  have h2 : ∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤
      c * G ^ 2 * ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) := by
    refine (sum_le_sum fun t _ => ?_).trans_eq (mul_sum _ _ _).symm
    calc η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤ η t * G ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2) (hη t).le
      _ = c * G ^ 2 * (1 / √((t : ℝ) + 1)) := by simp only [hηdef]; ring
  linarith [mul_le_mul_of_nonneg_left (sum_range_one_div_sqrt_succ_le T)
    (mul_nonneg hc.le (sq_nonneg G))]

/-- **Horizon-independent dynamic regret of OGD**: with step sizes `D / (G * √(t + 1))`, the
dynamic regret after `T` rounds is at most `(3 / 2 * D + pathLength u T) * G * √T`, extending
`ogd_regret_le_three_halves` to any moving comparator sequence `u` in `K`. -/
theorem ogd_dynamic_regret_le_three_halves {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => D / (G * √((t : ℝ) + 1))) grad x₀ t) - f t (u t)) ≤
      (3 / 2 * D + pathLength u T) * G * √(T : ℝ) := by
  simp_rw [← div_div D G]
  refine (sum_sub_le_sum_inner_dynamic hsub (ogd_mem hP hx₀) hu T).trans ?_
  rcases T with _ | T
  · simp
  · refine (ogd_dynamic_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG
      (div_pos hD0 hG0) hu T).trans ?_
    push_cast
    field_simp
    linarith [mul_nonneg hG0.le hD0.le]

/-- **Dynamic regret under Zinkevich's `1 / √(t + 1)` schedule** [Zinkevich2003] (locator
unverified): for `T ≥ 1`, dynamic regret after `T` rounds is at most
`(D ^ 2 / 2 + D * pathLength u T) * √T + (√T - 1 / 2) * G ^ 2`. -/
theorem ogd_dynamic_regret_le_zinkevich {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y)
    {u : ℕ → E} (hu : ∀ t, u t ∈ K) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => 1 / √((t : ℝ) + 1)) grad x₀ t) - f t (u t)) ≤
      (D ^ 2 / 2 + D * pathLength u T) * √(T : ℝ) + (√(T : ℝ) - 1 / 2) * G ^ 2 := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
  refine (sum_sub_le_sum_inner_dynamic hsub (ogd_mem hP hx₀) hu (T + 1)).trans ?_
  have h := ogd_dynamic_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG zero_lt_one hu T
  push_cast; linarith

end Cslib.MachineLearning.OnlineLearning.OCO
