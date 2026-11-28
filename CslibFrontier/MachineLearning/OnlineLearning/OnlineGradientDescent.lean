/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Online gradient descent

In *online convex optimization* [Zinkevich2003, Hazan2022] a learner repeatedly plays a point
`x t` of a convex set `K` in a real inner product space, after which an adversary reveals a convex
loss `f t : E → ℝ`. The regret against a comparator `u ∈ K` after `T` rounds is
`∑ t < T, (f t (x t) - f t u)`. *Online gradient descent* (`ogd`) [Hazan2022, Algorithm 8] (the
*greedy projection* algorithm of [Zinkevich2003, Algorithm 1]) steps against a subgradient and
projects back onto `K`:

  `x 0 = x₀`, `x (t + 1) = Π_K (x t - η t • grad t (x t))`.

Rounds are indexed from `0`, so the step size `η t` here is the source's `η_{t+1}`. The
subgradient oracle `grad : ℕ → E → E` is an arbitrary function of the round and the query point,
and the losses `f t` are arbitrary. Since OGD is deterministic, an adversary that adapts to the
learner's past points selects nothing it could not have fixed in advance, so these bounds cover
adaptive adversaries. Every bound holds for each comparator `u ∈ K`; taking the maximum over
`u` gives the regret `Regret_T` of [Hazan2022, §3.1].

The projection is any map `proj` satisfying the Pythagorean inequality
`‖proj y - z‖ ≤ ‖y - z‖` for `z ∈ K` and landing in `K` (`IsPythagoreanProjection`). The metric
projection onto a nonempty complete convex set is one
(`isPythagoreanProjection_metricProjection`, [Hazan2022, Theorem 2.1]). The losses enter through
the subgradient inequality `f t x + ⟪grad t x, y - x⟫ ≤ f t y` for `x y ∈ K`, the definition of
convexity with subgradients in [Hazan2022, §2.1]. For differentiable convex losses with
gradients it follows from `ConvexOn.add_inner_le_of_hasGradientAt`. The strongly convex form
`f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y` follows likewise from
`StrongConvexOn.add_inner_add_le_of_hasGradientAt` (or the `HasGradientWithinAt` variants,
which allow boundary points). `D` bounds the diameter of `K` and `G` the subgradient norms on
`K`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.IsPythagoreanProjection`: maps into `K` satisfying
  the Pythagorean inequality.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd`: the iterates of online gradient descent.

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_sum_inner_le`: for nonincreasing positive step
  sizes, `∑ t ≤ T, ⟪grad t (x t), x t - u⟫ ≤ D ^ 2 / (2 η T) + ∑ t ≤ T, η t ‖grad t (x t)‖ ^ 2 / 2`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_sum_inner_le_of_const`: for a constant step size
  `c`, the same with `‖x₀ - u‖ ^ 2 / (2 c)` in place of `D ^ 2 / (2 η T)`.
* `Cslib.MachineLearning.OnlineLearning.OCO.norm_ogd_sub_le`: `‖x t - x₀‖ ≤ G * ∑ s < t, η s`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_three_halves`: with step sizes
  `D / (G √(t + 1))`, regret at most `3 / 2 * G * D * √T` [Hazan2022, Theorem 3.1].
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_zinkevich`: with step sizes
  `1 / √(t + 1)`, regret at most `D ^ 2 √T / 2 + (√T - 1 / 2) G ^ 2` [Zinkevich2003, Theorem 1].
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_fixed`: with the constant step size
  `D / (G √T)` for a known horizon `T`, regret at most `G * D * √T`.
  `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_fixed_of_norm_sub_le` needs only
  `‖x₀ - u‖ ≤ B` instead of a diameter bound, and gives `G * B * √T` with step size `B / (G √T)`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_log`: for `α`-strongly convex losses
  and step sizes `1 / (α (t + 1))`, regret at most `G ^ 2 / (2 α) * (1 + log T)`
  [Hazan2022, Theorem 3.3].
* `Cslib.MachineLearning.OnlineLearning.OCO.norm_sub_le_of_strongConvex`: the strongly convex
  hypotheses force `diam K ≤ 2 G / α`.

## References

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022]
* [M. Zinkevich, *Online Convex Programming and Generalized Infinitesimal Gradient
  Ascent*][Zinkevich2003]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `proj` maps into `K` and satisfies the Pythagorean inequality `‖proj y - z‖ ≤ ‖y - z‖` for
every `z ∈ K`, the only properties of the projection used by online gradient descent. -/
structure IsPythagoreanProjection (K : Set E) (proj : E → E) : Prop where
  mem : ∀ y, proj y ∈ K
  norm_sub_le : ∀ y, ∀ z ∈ K, ‖proj y - z‖ ≤ ‖y - z‖

/-- The metric projection onto a nonempty complete convex set satisfies the Pythagorean inequality
[Hazan2022, Theorem 2.1]. -/
theorem isPythagoreanProjection_metricProjection {K : Set E} (hne : K.Nonempty)
    (hc : IsComplete K) (hK : Convex ℝ K) : IsPythagoreanProjection K (metricProjection K) :=
  ⟨metricProjection_mem hne hc hK, fun y _ hz => norm_metricProjection_sub_le hc hK y hz⟩

omit [InnerProductSpace ℝ E] in
/-- Unconstrained gradient descent: the identity is a Pythagorean projection onto the whole
space. Since `Set.univ` has no finite diameter (unless `E` is trivial), and the strongly convex
hypotheses force a finite diameter (`norm_sub_le_of_strongConvex`), the bounds that apply to it
nontrivially are those that use only `‖x₀ - u‖`: `ogd_two_mul_inner_le`,
`ogd_sum_inner_le_of_const` and `ogd_regret_le_fixed_of_norm_sub_le`. -/
theorem isPythagoreanProjection_id : IsPythagoreanProjection (Set.univ : Set E) id :=
  ⟨fun _ => Set.mem_univ _, fun _ _ _ => le_rfl⟩

/-- The iterates of online gradient descent [Hazan2022, Algorithm 8] with projection `proj`, step
sizes `η`, subgradient oracle `grad` and starting point `x₀`:
`x (t + 1) = proj (x t - η t • grad t (x t))`. -/
noncomputable def ogd (proj : E → E) (η : ℕ → ℝ) (grad : ℕ → E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => proj (ogd proj η grad x₀ t - η t • grad t (ogd proj η grad x₀ t))

variable {K : Set E} {proj : E → E} {η : ℕ → ℝ} {grad : ℕ → E → E} {x₀ : E}

@[simp] theorem ogd_zero : ogd proj η grad x₀ 0 = x₀ := by rfl

theorem ogd_succ (t : ℕ) :
    ogd proj η grad x₀ (t + 1) =
      proj (ogd proj η grad x₀ t - η t • grad t (ogd proj η grad x₀ t)) := by rfl

theorem ogd_mem (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) (t : ℕ) :
    ogd proj η grad x₀ t ∈ K :=
  match t with
  | 0 => hx₀
  | _ + 1 => hP.mem _

/-- Each step of online gradient descent moves at most `η t * G` when the subgradients on `K` have
norm at most `G`, so `‖x t - x₀‖ ≤ G * ∑ s < t, η s`. -/
theorem norm_ogd_sub_le (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) {G : ℝ}
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G) (hη : ∀ t, 0 ≤ η t) (t : ℕ) :
    ‖ogd proj η grad x₀ t - x₀‖ ≤ G * ∑ s ∈ range t, η s := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ogd_succ, sum_range_succ, mul_add]
    set x := ogd proj η grad x₀ t
    have hstep := mul_le_mul_of_nonneg_right (hG t x (ogd_mem hP hx₀ t)) (hη t)
    calc ‖proj (x - η t • grad t x) - x₀‖
        ≤ ‖proj (x - η t • grad t x) - x‖ + ‖x - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖x - η t • grad t x - x‖ + ‖x - x₀‖ := by
          gcongr
          exact hP.norm_sub_le _ x (ogd_mem hP hx₀ t)
      _ = η t * ‖grad t x‖ + ‖x - x₀‖ := by
          rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hη t)]
      _ ≤ G * ∑ s ∈ range t, η s + G * η t := by linarith

/-- One projected gradient step decreases the squared distance to a feasible comparator,
up to the inner-product loss and the squared step length. -/
theorem projected_step_two_mul_inner_le (hP : IsPythagoreanProjection K proj)
    {x g u : E} (hu : u ∈ K) {c : ℝ} (hc : 0 < c) :
    2 * ⟪g, x - u⟫ ≤ (‖x - u‖ ^ 2 - ‖proj (x - c • g) - u‖ ^ 2) / c + c * ‖g‖ ^ 2 := by
  have hproj := pow_le_pow_left₀ (norm_nonneg _) (hP.norm_sub_le (x - c • g) u hu) 2
  have hexpand : ‖x - c • g - u‖ ^ 2 =
      ‖x - u‖ ^ 2 - 2 * ⟪g, x - u⟫ * c + c * ‖g‖ ^ 2 * c := by
    rw [sub_right_comm, norm_sub_sq_real, norm_smul, real_inner_smul_right, real_inner_comm,
      Real.norm_of_nonneg hc.le]
    ring
  rw [div_add' _ _ _ hc.ne', le_div_iff₀ hc]
  linarith only [hproj, hexpand]

/-- One step of online gradient descent against a comparator `u ∈ K`:
`2 ⟪g, x t - u⟫ ≤ (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / η t + η t ‖g‖ ^ 2` with
`g = grad t (x t)` [Hazan2022, proof of Theorem 3.1]. -/
theorem ogd_two_mul_inner_le (hP : IsPythagoreanProjection K proj) {u : E} (hu : u ∈ K) (t : ℕ)
    (hη : 0 < η t) :
    2 * ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u⟫ ≤
      (‖ogd proj η grad x₀ t - u‖ ^ 2 - ‖ogd proj η grad x₀ (t + 1) - u‖ ^ 2) / η t +
        η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 := by
  rw [ogd_succ]
  exact projected_step_two_mul_inner_le hP hu hη

/-- The generic bound for online gradient descent with positive nonincreasing step sizes on a set
of diameter at most `D`: against every `u ∈ K`,
`∑ t ≤ T, ⟪grad t (x t), x t - u⟫ ≤ D ^ 2 / (2 η T) + (∑ t ≤ T, η t ‖grad t (x t)‖ ^ 2) / 2`
[Hazan2022, proof of Theorem 3.1]. -/
theorem ogd_sum_inner_le (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) {D : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hη : ∀ t, 0 < η t) (hanti : Antitone η)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u⟫ ≤
      D ^ 2 / (2 * η T) +
        (∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2) / 2 := by
  set x := ogd proj η grad x₀
  let a (t : ℕ) := ‖x t - u‖ ^ 2
  let w (t : ℕ) := 1 / η t
  have hcap (t : ℕ) : a t ≤ D ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hD _ (ogd_mem hP hx₀ t) _ hu) 2
  have htel := Fin.sum_range_mul_sub_le_of_adjacent w a (fun t => a (t + 1)) (fun _ => 0)
    (D ^ 2) T
    (fun t _ => mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (hη (t + 1)) (hanti (Nat.le_succ t))) (sub_nonneg.mpr (hcap _)))
    (fun _ _ => by rw [sub_self, mul_zero])
  have hsum := sum_le_sum (s := range (T + 1)) fun t _ =>
    ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP hu t (hη t)
  rw [← mul_sum, sum_add_distrib] at hsum
  have hinitial := div_nonneg (sub_nonneg.mpr (hcap 0)) (hη 0).le
  have hfinal := div_nonneg (sq_nonneg ‖x (T + 1) - u‖) (hη T).le
  simp only [a, w, one_div_mul_eq_div, sum_const_zero, add_zero, sub_div] at htel hinitial hsum
  rw [mul_comm 2 (η T), ← div_div]
  linarith only [hsum, htel, hinitial, hfinal]

/-- Online gradient descent with a constant step size `c > 0`: against every `u ∈ K`,
`∑ t < T, ⟪grad t (x t), x t - u⟫ ≤ ‖x₀ - u‖ ^ 2 / (2 c) + c (∑ t < T, ‖grad t (x t)‖ ^ 2) / 2`.
Only the distance from the starting point to the comparator enters, not the diameter of `K`. -/
theorem ogd_sum_inner_le_of_const (hP : IsPythagoreanProjection K proj) {c : ℝ} (hc : 0 < c)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, ⟪grad t (ogd proj (fun _ => c) grad x₀ t), ogd proj (fun _ => c) grad x₀ t - u⟫ ≤
      ‖x₀ - u‖ ^ 2 / (2 * c) +
        c * (∑ t ∈ range T, ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2) / 2 := by
  let x := ogd proj (fun _ => c) grad x₀
  have hsum := sum_le_sum (s := range T) fun t _ =>
    ogd_two_mul_inner_le (η := fun _ => c) (x₀ := x₀) (grad := grad) hP hu t hc
  change (∑ t ∈ range T, 2 * ⟪grad t (x t), x t - u⟫) ≤
    ∑ t ∈ range T, ((‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / c +
      c * ‖grad t (x t)‖ ^ 2) at hsum
  rw [← mul_sum, sum_add_distrib, ← sum_div, sum_range_sub', ← mul_sum] at hsum
  rw [mul_comm 2 c, ← div_div]
  simp only [x, ogd_zero, sub_div] at hsum
  linarith only [hsum, div_nonneg (sq_nonneg ‖x T - u‖) hc.le]

/-- `∑ t < T + 1, 1 / √(t + 1) ≤ 2 √(T + 1) - 1`. -/
theorem sum_range_one_div_sqrt_succ_le (T : ℕ) :
    ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) ≤ 2 * √((T : ℝ) + 1) - 1 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [sum_range_succ, Nat.cast_add_one]
    set r := √((T : ℝ) + 1)
    set s := √((T : ℝ) + 1 + 1)
    have hs : 0 < s := sqrt_pos.mpr (by positivity)
    have hid : s ^ 2 - r ^ 2 + (s - r) ^ 2 = 2 * (s - r) * s := by ring
    rw [sq_sqrt (by positivity), sq_sqrt (Nat.cast_add_one_pos T).le] at hid
    have hstep : 1 / s ≤ 2 * (s - r) := (div_le_iff₀ hs).mpr (by linarith [sq_nonneg (s - r)])
    linarith

/-- Regret through subgradients: for any points `x t ∈ K` and any `u ∈ K`, the subgradient
inequality bounds `∑ t < T, (f t (x t) - f t u)` by `∑ t < T, ⟪grad t (x t), x t - u⟫`. -/
theorem sum_sub_le_sum_inner {f : ℕ → E → ℝ}
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {x : ℕ → E}
    (hx : ∀ t, x t ∈ K) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ∑ t ∈ range T, ⟪grad t (x t), x t - u⟫ :=
  sum_le_sum fun t _ => by
    have h := hsub t (x t) (hx t) u hu
    rw [← neg_sub (x t) u, inner_neg_right] at h
    linarith

/-- Online gradient descent with step sizes `c / √(t + 1)`: the linearized regret over `T + 1`
rounds is at most `D ^ 2 / (2 c) √(T + 1) + c G ^ 2 (√(T + 1) - 1 / 2)`. -/
theorem ogd_sum_inner_le_sqrt (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {D G c : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hc : 0 < c) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t),
        ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t - u⟫ ≤
      D ^ 2 / (2 * c) * √((T : ℝ) + 1) + c * G ^ 2 * (√((T : ℝ) + 1) - 1 / 2) := by
  set η : ℕ → ℝ := fun t => c / √((t : ℝ) + 1) with hηdef
  have hη : ∀ t, 0 < η t := fun t => div_pos hc (sqrt_pos.mpr (by positivity))
  have hanti : Antitone η := fun a b hab => by simp only [hηdef]; gcongr
  have h := ogd_sum_inner_le (grad := grad) hP hx₀ hD hη hanti hu T
  have h1 : D ^ 2 / (2 * η T) = D ^ 2 / (2 * c) * √((T : ℝ) + 1) := by
    simp only [hηdef]
    field_simp
  have h2 : ∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤
      c * G ^ 2 * ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) := by
    rw [mul_sum]
    refine sum_le_sum fun t _ => (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2) (hη t).le).trans_eq ?_
    simp only [hηdef]
    ring
  rw [h1] at h
  nlinarith [sum_range_one_div_sqrt_succ_le T, mul_nonneg hc.le (sq_nonneg G)]

/-- **Regret of online gradient descent** [Hazan2022, Theorem 3.1]: for losses satisfying the
subgradient inequality with subgradients of norm at most `G` on a set of diameter at most `D`, the
step sizes `D / (G √(t + 1))` give regret at most `3 / 2 * G * D * √T` against every `u ∈ K`. -/
theorem ogd_regret_le_three_halves {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => D / (G * √((t : ℝ) + 1))) grad x₀ t) - f t u) ≤
      3 / 2 * G * D * √(T : ℝ) := by
  simp_rw [← div_div]
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu T).trans ?_
  rcases T with _ | T
  · simp
  · have h := ogd_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG (div_pos hD0 hG0) hu T
    have e : D ^ 2 / (2 * (D / G)) * √((T : ℝ) + 1) +
        D / G * G ^ 2 * (√((T : ℝ) + 1) - 1 / 2) =
        3 / 2 * G * D * √((T : ℝ) + 1) - G * D / 2 := by
      field_simp
      ring
    rw [e] at h
    push_cast
    linarith [mul_pos hG0 hD0]

/-- **Zinkevich's regret bound** [Zinkevich2003, Theorem 1]: with step sizes `1 / √(t + 1)`, the
regret after `T ≥ 1` rounds is at most `D ^ 2 √T / 2 + (√T - 1 / 2) G ^ 2`. -/
theorem ogd_regret_le_zinkevich {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => 1 / √((t : ℝ) + 1)) grad x₀ t) - f t u) ≤
      D ^ 2 * √(T : ℝ) / 2 + (√(T : ℝ) - 1 / 2) * G ^ 2 := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT.ne'
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu _).trans ?_
  push_cast
  linarith [ogd_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG one_pos hu T]

/-- **Fixed step size, from the distance to the comparator**: for a known horizon `T ≥ 1` and a
comparator `u ∈ K` with `‖x₀ - u‖ ≤ B`, the constant step size `B / (G √T)` gives regret at most
`G * B * √T` against `u`. No bound on the diameter of `K` is needed, so `K` may be the whole space;
this is the regret bound behind [ShalevShwartzBenDavid2014, Theorem 14.8]. -/
theorem ogd_regret_le_fixed_of_norm_sub_le {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {B G : ℝ} (hB0 : 0 < B) (hG0 : 0 < G) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    (hx₀u : ‖x₀ - u‖ ≤ B) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun _ => B / (G * √(T : ℝ))) grad x₀ t) - f t u) ≤
      G * B * √(T : ℝ) := by
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu T).trans ?_
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  set c := B / (G * √(T : ℝ)) with hcdef
  have hc : 0 < c := div_pos hB0 (mul_pos hG0 (sqrt_pos.mpr hTr))
  have h1 : ‖x₀ - u‖ ^ 2 / (2 * c) ≤ G * B * √(T : ℝ) / 2 := by
    calc ‖x₀ - u‖ ^ 2 / (2 * c) ≤ B ^ 2 / (2 * c) := by gcongr
      _ = G * B * √(T : ℝ) / 2 := by rw [hcdef]; field_simp
  have h2 : c * (∑ t ∈ range T, ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2) / 2 ≤
      G * B * √(T : ℝ) / 2 := by
    have hsum : ∑ t ∈ range T, ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2 ≤ T * G ^ 2 :=
      (sum_le_sum fun t _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2).trans_eq
        (by simp only [sum_const, card_range, nsmul_eq_mul])
    have e : c * ((T : ℝ) * G ^ 2) = G * B * √(T : ℝ) := by
      calc c * ((T : ℝ) * G ^ 2) =
            (√(T : ℝ) * √(T : ℝ)) * (B / (G * √(T : ℝ)) * G ^ 2) := by
            rw [mul_self_sqrt hTr.le, hcdef]; ring
        _ = G * B * √(T : ℝ) := by field_simp
    linarith [mul_le_mul_of_nonneg_left hsum hc.le]
  linarith [ogd_sum_inner_le_of_const (grad := grad) (x₀ := x₀) hP hc hu T]

/-- **Fixed step size**: for a known horizon `T ≥ 1`, the constant step size `D / (G √T)` gives
regret at most `G * D * √T`. -/
theorem ogd_regret_le_fixed {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun _ => D / (G * √(T : ℝ))) grad x₀ t) - f t u) ≤
      G * D * √(T : ℝ) :=
  ogd_regret_le_fixed_of_norm_sub_le hP hx₀ hD0 hG0 hG hsub hu (hD x₀ hx₀ u hu) hT

/-- The strongly convex hypotheses bound the diameter: if `f` satisfies
`f x + ⟪g x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f y` on `K` with `α > 0` and `‖g x‖ ≤ G` on `K`,
then `‖x - y‖ ≤ 2 G / α` for `x y ∈ K`. -/
theorem norm_sub_le_of_strongConvex {f : E → ℝ} {g : E → E} {G α : ℝ} (hα : 0 < α)
    (hG : ∀ x ∈ K, ‖g x‖ ≤ G)
    (hsc : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : ‖x - y‖ ≤ 2 * G / α := by
  have h1 := hsc x hx y hy
  have h2 := hsc y hy x hx
  -- `α ‖x - y‖ ^ 2 ≤ -⟪g x, y - x⟫ - ⟪g y, x - y⟫ ≤ 2 G ‖x - y‖`
  have hlow : ∀ z ∈ K, ∀ w : E, -(G * ‖w‖) ≤ ⟪g z, w⟫ := fun z hz w =>
    (neg_le_neg (mul_le_mul_of_nonneg_right (hG z hz) (norm_nonneg w))).trans
      (abs_le.mp (abs_real_inner_le_norm (g z) w)).1
  have hcx := hlow x hx (y - x)
  rw [norm_sub_rev y x] at h1 hcx
  have hsq : α * ‖x - y‖ ^ 2 ≤ 2 * G * ‖x - y‖ := by linarith [hlow y hy (x - y)]
  rw [le_div_iff₀ hα]
  by_contra! hlt
  nlinarith [norm_nonneg (x - y), (norm_nonneg (g x)).trans (hG x hx)]

/-- **Logarithmic regret for strongly convex losses** [Hazan2022, Theorem 3.3]: if every loss
satisfies `f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y` on `K` with `α > 0` and the
subgradients have norm at most `G` on `K`, the step sizes `1 / (α (t + 1))` give regret at most
`G ^ 2 / (2 α) * (1 + log T)` against every `u ∈ K`. No separate diameter hypothesis is assumed
(these hypotheses already force `‖x - y‖ ≤ 2 G / α` on `K`, `norm_sub_le_of_strongConvex`). -/
theorem ogd_regret_le_log {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {G α : ℝ} (hα : 0 < α) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsc : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => 1 / (α * ((t : ℝ) + 1))) grad x₀ t) - f t u) ≤
      G ^ 2 / (2 * α) * (1 + log T) := by
  set η : ℕ → ℝ := fun t => 1 / (α * ((t : ℝ) + 1)) with hηdef
  set x := ogd proj η grad x₀
  have hη : ∀ t, 0 < η t := fun t => by simp only [hηdef]; positivity
  have step : ∀ t : ℕ, 2 * (f t (x t) - f t u) ≤
      α * t * ‖x t - u‖ ^ 2 - α * (t + 1) * ‖x (t + 1) - u‖ ^ 2 +
        G ^ 2 / α * (1 / (t + 1)) := fun t => by
    have h1 := ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP hu t (hη t)
    have h2 := hsc t (x t) (ogd_mem hP hx₀ t) u hu
    rw [← neg_sub (x t) u, inner_neg_right, norm_neg] at h2
    have e1 : (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / η t =
        α * t * ‖x t - u‖ ^ 2 + α * ‖x t - u‖ ^ 2 - α * (t + 1) * ‖x (t + 1) - u‖ ^ 2 := by
      simp only [hηdef, one_div, div_inv_eq_mul]; ring
    have e2 : η t * ‖grad t (x t)‖ ^ 2 ≤ G ^ 2 / α * (1 / (t + 1)) :=
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hG t (x t) (ogd_mem hP hx₀ t)) 2) (hη t).le).trans_eq
        (by simp only [hηdef]; field_simp)
    rw [e1] at h1
    linarith
  have tele : 2 * ∑ t ∈ range T, (f t (x t) - f t u) ≤
      -(α * T * ‖x T - u‖ ^ 2) + G ^ 2 / α * ∑ t ∈ range T, 1 / ((t : ℝ) + 1) := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, sum_range_succ, mul_add, mul_add]
      push_cast
      linarith [step T]
  have hH : ∑ t ∈ range T, 1 / ((t : ℝ) + 1) ≤ 1 + log T := by
    simpa [harmonic] using harmonic_le_one_add_log T
  rw [mul_comm 2 α, ← div_div, div_mul_eq_mul_div]
  linarith [tele, mul_nonneg (mul_nonneg hα.le T.cast_nonneg) (sq_nonneg ‖x T - u‖),
    mul_le_mul_of_nonneg_left hH (div_nonneg (sq_nonneg G) hα.le)]

end Cslib.MachineLearning.OnlineLearning.OCO
