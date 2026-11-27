/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/LinearLyapunov.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.LinearFlow
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stability of linear time-invariant systems and the quadratic Lyapunov criterion

For a bounded linear operator `A : E →L[ℝ] E`, stability of the equilibrium `0` of `ẋ = A x` is
stated about all trajectories on `[0, ∞)` in the sense of `ContinuousLinearMap.IsTrajectoryOn`,
measured in the norm of `E`:

* `IsLyapunovStable`: `∀ ε > 0, ∃ δ > 0`, every trajectory with `‖x 0‖ < δ` has `‖x t‖ < ε`
  for all `t ≥ 0`.
* `IsAsymptoticallyStable`: Lyapunov stable, and `∃ δ > 0` such that every trajectory with
  `‖x 0‖ < δ` tends to `0` as `t → ∞`.
* `IsExponentiallyStable`: `∃ M α, 0 < α` such that every trajectory satisfies
  `‖x t‖ ≤ M * exp (-(α * t)) * ‖x 0‖` for all `t ≥ 0`. The constants are chosen before the
  trajectory, so this is global, uniform exponential stability.

For a finite-dimensional system all norms are equivalent, so these properties do not depend on
the chosen norm, although the constants do. Matrix systems are stated on `EuclideanSpace ℝ n`
through `Matrix.toEuclideanCLM`, so their constants refer to the Euclidean norm.

The energy `V x = ⟪x, P x⟫` of any `P : E →L[ℝ] E` has derivative
`⟪x, (A† P + P A) x⟫` along trajectories (`IsTrajectoryOn.hasDerivWithinAt_inner_apply`; no
symmetry of `P` is needed). A differential inequality `V' ≤ K V` on `[a, ∞)` gives
`V t ≤ exp (K (t - a)) V a` (`le_exp_mul_sub_mul_of_hasDerivWithinAt`), and combining the two
gives decay of the energy along trajectories (`IsTrajectoryOn.inner_apply_le_exp_mul`). With
coercivity constants `m ‖y‖² ≤ ⟪y, P y⟫ ≤ M ‖y‖²` and `c ‖y‖² ≤ -⟪y, (A† P + P A) y⟫` this is the
explicit bound `‖x t‖² ≤ (M / m) exp (-(c / M) t) ‖x 0‖²` (`IsTrajectoryOn.norm_sq_le`). In finite
dimension, positivity of a quadratic form gives such a constant by compactness of the unit sphere
(`exists_pos_mul_norm_sq_le_inner_apply`), which yields the classical quadratic Lyapunov
criterion (`isExponentiallyStable_of_inner_pos`) and its matrix form
(`Matrix.isExponentiallyStable_toEuclideanCLM_of_posDef`). The decay estimate is proved, not
assumed.

The same energy identity gives Lyapunov's instability theorem. If `A† P + P A ≤ 2 ε P` for an
indefinite `P` and `⟪x 0, P (x 0)⟫ < 0`, then `⟪x t, P (x t)⟫ ≤ exp (2 ε t) ⟪x 0, P (x 0)⟫ < 0`,
and `-⟪y, P y⟫ ≤ ‖P‖ ‖y‖²` turns this into `‖x t‖ ≥ √(-⟪x 0, P (x 0)⟫ / ‖P‖) exp (ε t)`
(`IsTrajectoryOn.sqrt_mul_exp_le_norm`). With `ε ≥ 0` the system is not asymptotically stable,
and with `ε > 0` it is not Lyapunov stable and has an unbounded trajectory. For matrices the
hypothesis is `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0`. A nonstrict inequality
`A† P + P A ≤ 0` with `P` positive gives Lyapunov stability
(`isLyapunovStable_of_inner_pos_of_nonpos`).

## Main definitions

* `ContinuousLinearMap.IsLyapunovStable`, `ContinuousLinearMap.IsAsymptoticallyStable`,
  `ContinuousLinearMap.IsExponentiallyStable`.

## Main results

* `ContinuousLinearMap.IsExponentiallyStable.isAsymptoticallyStable`.
* `le_exp_mul_sub_mul_of_hasDerivWithinAt`: `V' ≤ K V` on `[a, ∞)` implies
  `V t ≤ exp (K (t - a)) V a`.
* `ContinuousLinearMap.IsTrajectoryOn.hasDerivWithinAt_inner_apply`: the energy identity
  `d/dt ⟪x, P x⟫ = ⟪x, (A† P + P A) x⟫`.
* `ContinuousLinearMap.IsTrajectoryOn.inner_apply_le_exp_mul`: `A† P + P A ≤ K P` as quadratic
  forms gives `⟪x t, P x t⟫ ≤ exp (K t) ⟪x 0, P x 0⟫`.
* `ContinuousLinearMap.IsTrajectoryOn.norm_sq_le`: the explicit decay bound above.
* `exists_pos_mul_norm_sq_le_inner_apply`: a positive quadratic form on a finite-dimensional
  space is coercive.
* `ContinuousLinearMap.isExponentiallyStable_of_inner_pos`: `⟪x, P x⟫ > 0` and
  `⟪x, (A† P + P A) x⟫ < 0` for `x ≠ 0` imply exponential stability.
* `Matrix.hasDerivWithinAt_dotProduct_mulVec`: the energy identity
  `d/dt (xᵀ P x) = xᵀ (Aᵀ P + P A) x` for coordinate trajectories.
* `Matrix.isExponentiallyStable_toEuclideanCLM_of_posDef`: `P ≻ 0` and `-(Aᵀ P + P A) ≻ 0`
  (`Matrix.PosDef` over `ℝ`) imply exponential stability of `ẋ = A x` in the Euclidean norm.
* `ContinuousLinearMap.IsTrajectoryOn.sqrt_mul_exp_le_norm`,
  `ContinuousLinearMap.sqrt_div_norm_pos_of_inner_neg`: the growth bound from
  `A† P + P A ≤ 2 ε P`, with a positive constant when the initial energy is negative.
* `ContinuousLinearMap.not_isAsymptoticallyStable_of_inner_neg`,
  `ContinuousLinearMap.not_isLyapunovStable_of_inner_neg`,
  `ContinuousLinearMap.tendsto_norm_exp_smul_apply_atTop`: Lyapunov's instability theorem.
* `ContinuousLinearMap.isLyapunovStable_of_inner_pos_of_nonpos`: Lyapunov stability from a
  nonstrict Lyapunov inequality.
* `Matrix.sqrt_mul_exp_le_norm_exp_smul_mulVec`, `Matrix.sqrt_div_norm_pos_of_dotProduct_neg`,
  `Matrix.exp_mul_neg_le_norm_mul_dotProduct_self`,
  `Matrix.not_isAsymptoticallyStable_toEuclideanCLM_of_posSemidef`,
  `Matrix.not_isLyapunovStable_toEuclideanCLM_of_posSemidef`,
  `Matrix.tendsto_norm_exp_smul_mulVec_atTop`,
  `Matrix.isLyapunovStable_toEuclideanCLM_of_posDef_of_posSemidef`: the matrix forms.
-/

public section

open Set Filter Topology NormedSpace
open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The equilibrium `0` of `ẋ = A x` is **Lyapunov stable**: for every `ε > 0` there is `δ > 0`
such that every trajectory on `[0, ∞)` starting in the open `δ`-ball stays in the open `ε`-ball
for all `t ≥ 0`. -/
@[expose] def IsLyapunovStable (A : E →L[ℝ] E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → E, A.IsTrajectoryOn x (Ici 0) → ‖x 0‖ < δ →
    ∀ t ≥ 0, ‖x t‖ < ε

/-- The equilibrium `0` of `ẋ = A x` is **asymptotically stable**: it is Lyapunov stable, and
there is `δ > 0` such that every trajectory on `[0, ∞)` starting in the open `δ`-ball tends to
`0`. -/
@[expose] def IsAsymptoticallyStable (A : E →L[ℝ] E) : Prop :=
  A.IsLyapunovStable ∧ ∃ δ > 0, ∀ x : ℝ → E, A.IsTrajectoryOn x (Ici 0) → ‖x 0‖ < δ →
    Tendsto x atTop (𝓝 0)

/-- The equilibrium `0` of `ẋ = A x` is (globally, uniformly) **exponentially stable**: there are
constants `M` and `α > 0`, chosen before the trajectory, such that every trajectory on `[0, ∞)`
satisfies `‖x t‖ ≤ M * exp (-(α * t)) * ‖x 0‖` for all `t ≥ 0`. -/
@[expose] def IsExponentiallyStable (A : E →L[ℝ] E) : Prop :=
  ∃ M α : ℝ, 0 < α ∧ ∀ x : ℝ → E, A.IsTrajectoryOn x (Ici 0) →
    ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖

/-- Exponential stability implies asymptotic stability. -/
theorem IsExponentiallyStable.isAsymptoticallyStable {A : E →L[ℝ] E}
    (hA : A.IsExponentiallyStable) : A.IsAsymptoticallyStable := by
  obtain ⟨M, α, hα, hM⟩ := hA
  refine ⟨fun ε hε => ⟨ε / (|M| + 1), by positivity, fun x hx h0 t ht => ?_⟩,
    1, one_pos, fun x hx _ => ?_⟩
  · have hexp : Real.exp (-(α * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hα.le ht))
    have hpos : 0 < |M| + 1 := by positivity
    calc ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖ := hM x hx t ht
      _ ≤ |M| * ‖x 0‖ := by
          have h1 : M * Real.exp (-(α * t)) ≤ |M| :=
            calc M * Real.exp (-(α * t)) ≤ |M| * Real.exp (-(α * t)) :=
                  mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
              _ ≤ |M| := mul_le_of_le_one_right (abs_nonneg M) hexp
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < (|M| + 1) * (ε / (|M| + 1)) := by
          nlinarith [(lt_div_iff₀ hpos).1 h0, norm_nonneg (x 0), abs_nonneg M]
      _ = ε := by field_simp
  · have hlim : Tendsto (fun t => M * Real.exp (-(α * t)) * ‖x 0‖) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hα))).const_mul M).mul_const ‖x 0‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht using hM x hx t ht

end ContinuousLinearMap

/-- **Exponential bound from a linear differential inequality.** If `V` has derivative `V' t`
within `[a, ∞)` at every `t ≥ a` and `V' t ≤ K * V t` there, then
`V t ≤ exp (K * (t - a)) * V a` for every `t ≥ a`. The rate `K` may have any sign. -/
theorem le_exp_mul_sub_mul_of_hasDerivWithinAt {V V' : ℝ → ℝ} {K a : ℝ}
    (hV : ∀ t ∈ Ici a, HasDerivWithinAt V (V' t) (Ici a) t)
    (hle : ∀ t ∈ Ici a, V' t ≤ K * V t) {t : ℝ} (ht : a ≤ t) :
    V t ≤ Real.exp (K * (t - a)) * V a := by
  set W : ℝ → ℝ := fun τ => Real.exp (-(K * (τ - a))) * V τ
  have hW : ∀ τ ∈ Ici a, HasDerivWithinAt W
      (Real.exp (-(K * (τ - a))) * (V' τ - K * V τ)) (Ici a) τ := fun τ hτ => by
    have he : HasDerivAt (fun τ : ℝ => Real.exp (-(K * (τ - a))))
        (Real.exp (-(K * (τ - a))) * -K) τ := by
      simpa using ((((hasDerivAt_id τ).sub_const a).const_mul K).neg).exp
    convert he.hasDerivWithinAt.mul (hV τ hτ) using 1
    ring
  have hanti : AntitoneOn W (Ici a) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun τ hτ => (hW τ hτ).continuousWithinAt)
      (f' := fun τ => Real.exp (-(K * (τ - a))) * (V' τ - K * V τ))
      (fun τ hτ => ?_) (fun τ hτ => ?_)
    · rw [interior_Ici] at hτ ⊢
      exact (hW τ hτ.le).mono Ioi_subset_Ici_self
    · rw [interior_Ici] at hτ
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.2 (hle τ hτ.le))
  have h := hanti self_mem_Ici (mem_Ici.2 ht) ht
  simp only [W, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  calc V t = Real.exp (K * (t - a)) * (Real.exp (-(K * (t - a))) * V t) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (K * (t - a)) * V a := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- **Coercivity in finite dimension.** A quadratic form `y ↦ ⟪y, P y⟫` that is positive on
nonzero vectors of a finite-dimensional real inner product space is bounded below by
`m * ‖y‖ ^ 2` for some `m > 0`: take the minimum of the form on the (compact) unit sphere. -/
theorem exists_pos_mul_norm_sq_le_inner_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {P : E →L[ℝ] E}
    (hP : ∀ y ≠ 0, 0 < ⟪y, P y⟫) : ∃ m > 0, ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, P y⟫ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, one_pos, fun y => by simp [Subsingleton.elim y 0]⟩
  have hf : Continuous fun y : E => ⟪y, P y⟫ := by fun_prop
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hf.continuousOn
  refine ⟨⟪u, P u⟫, hP u (fun h => by simp [h] at hu), fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h : ⟪u, P u⟫ ≤ ⟪‖y‖⁻¹ • y, P (‖y‖⁻¹ • y)⟫ := hmin <| by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
  rw [map_smul, real_inner_smul_left, real_inner_smul_right,
    show ‖y‖⁻¹ * (‖y‖⁻¹ * ⟪y, P y⟫) = ⟪y, P y⟫ / ‖y‖ ^ 2 by field_simp,
    le_div_iff₀ (by positivity)] at h
  exact h

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {x : ℝ → E} {s : Set ℝ}

/-- **Energy identity.** Along a trajectory of `ẋ = A x`, the quadratic energy `⟪x, P x⟫` has
derivative `⟪x, (A† P + P A) x⟫` within the time set. The operator `P` need not be symmetric. -/
theorem IsTrajectoryOn.hasDerivWithinAt_inner_apply (hx : A.IsTrajectoryOn x s) {t : ℝ}
    (ht : t ∈ s) :
    HasDerivWithinAt (fun τ => ⟪x τ, P (x τ)⟫) ⟪x t, (adjoint A * P + P * A) (x t)⟫ s t := by
  refine ((hx t ht).inner ℝ (P.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht))).congr_deriv ?_
  change ⟪x t, P (A (x t))⟫ + ⟪A (x t), P (x t)⟫ = ⟪x t, adjoint A (P (x t)) + P (A (x t))⟫
  rw [inner_add_right, adjoint_inner_right, add_comm]

/-- **Energy decay along trajectories.** If `A† P + P A ≤ K P` as quadratic forms, then the
energy `⟪x, P x⟫` of every trajectory on `[0, ∞)` satisfies
`⟪x t, P (x t)⟫ ≤ exp (K * t) * ⟪x 0, P (x 0)⟫` for `t ≥ 0`. -/
theorem IsTrajectoryOn.inner_apply_le_exp_mul (hx : A.IsTrajectoryOn x (Ici 0)) {K : ℝ}
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ K * ⟪y, P y⟫) {t : ℝ} (ht : 0 ≤ t) :
    ⟪x t, P (x t)⟫ ≤ Real.exp (K * t) * ⟪x 0, P (x 0)⟫ := by
  simpa using le_exp_mul_sub_mul_of_hasDerivWithinAt
    (fun τ hτ => hx.hasDerivWithinAt_inner_apply (P := P) hτ) (fun τ _ => hK (x τ)) ht

/-- **Explicit quadratic Lyapunov bound.** Suppose `m ‖y‖² ≤ ⟪y, P y⟫ ≤ M ‖y‖²` with `m > 0`,
and `c ‖y‖² ≤ -⟪y, (A† P + P A) y⟫` with `c ≥ 0`. Then every trajectory of `ẋ = A x` on
`[0, ∞)` satisfies `‖x t‖² ≤ (M / m) exp (-(c / M) t) ‖x 0‖²` for `t ≥ 0`. -/
theorem IsTrajectoryOn.norm_sq_le (hx : A.IsTrajectoryOn x (Ici 0)) {m M c : ℝ} (hm : 0 < m)
    (hc : 0 ≤ c) (hlow : ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, P y⟫) (hup : ∀ y, ⟪y, P y⟫ ≤ M * ‖y‖ ^ 2)
    (hQ : ∀ y, c * ‖y‖ ^ 2 ≤ -⟪y, (adjoint A * P + P * A) y⟫) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t‖ ^ 2 ≤ M / m * Real.exp (-(c / M) * t) * ‖x 0‖ ^ 2 := by
  have hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ -(c / M) * ⟪y, P y⟫ := fun y => by
    rcases le_or_gt M 0 with hM | hM
    · -- Then `y = 0`, since `m ‖y‖² ≤ M ‖y‖² ≤ 0`.
      have hy : ‖y‖ ^ 2 = 0 := by nlinarith [hlow y, hup y, sq_nonneg ‖y‖]
      simp [show y = 0 by simpa using hy]
    · have h1 : c / M * ⟪y, P y⟫ ≤ c * ‖y‖ ^ 2 :=
        calc c / M * ⟪y, P y⟫ ≤ c / M * (M * ‖y‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (hup y) (div_nonneg hc hM.le)
          _ = c * ‖y‖ ^ 2 := by field_simp
      linarith [hQ y]
  rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀' hm]
  calc m * ‖x t‖ ^ 2 ≤ ⟪x t, P (x t)⟫ := hlow _
    _ ≤ Real.exp (-(c / M) * t) * ⟪x 0, P (x 0)⟫ := hx.inner_apply_le_exp_mul hK ht
    _ ≤ Real.exp (-(c / M) * t) * (M * ‖x 0‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hup _) (Real.exp_pos _).le
    _ = M * (Real.exp (-(c / M) * t) * ‖x 0‖ ^ 2) := by ring

omit [CompleteSpace E] in
private theorem abs_inner_apply_le (y : E) : |⟪y, P y⟫| ≤ ‖P‖ * ‖y‖ ^ 2 :=
  calc |⟪y, P y⟫| ≤ ‖y‖ * ‖P y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖P‖ * ‖y‖) := mul_le_mul_of_nonneg_left (P.le_opNorm _) (norm_nonneg _)
    _ = ‖P‖ * ‖y‖ ^ 2 := by ring

/-- **Quadratic Lyapunov criterion.** On a finite-dimensional real inner product space, if
`⟪y, P y⟫ > 0` and `⟪y, (A† P + P A) y⟫ < 0` for every `y ≠ 0`, then `ẋ = A x` is exponentially
stable. The coercivity constants come from `exists_pos_mul_norm_sq_le_inner_apply`, the upper
constant is `‖P‖ + 1`, and the rate is obtained from `IsTrajectoryOn.norm_sq_le`. -/
theorem isExponentiallyStable_of_inner_pos [FiniteDimensional ℝ E]
    (hP : ∀ y ≠ 0, 0 < ⟪y, P y⟫) (hQ : ∀ y ≠ 0, ⟪y, (adjoint A * P + P * A) y⟫ < 0) :
    A.IsExponentiallyStable := by
  obtain ⟨m, hm, hlow⟩ := exists_pos_mul_norm_sq_le_inner_apply hP
  obtain ⟨c, hc, hcQ⟩ := exists_pos_mul_norm_sq_le_inner_apply (P := -(adjoint A * P + P * A))
    fun y hy => by rw [neg_apply, inner_neg_right]; linarith [hQ y hy]
  set M := ‖P‖ + 1
  have hM : 0 < M := by positivity
  have hup : ∀ y, ⟪y, P y⟫ ≤ M * ‖y‖ ^ 2 := fun y =>
    (le_abs_self _).trans <| (abs_inner_apply_le y).trans <|
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
  refine ⟨Real.sqrt (M / m), c / (2 * M), by positivity, fun x hx t ht => ?_⟩
  have h := hx.norm_sq_le hm hc.le hlow hup
    (fun y => by simpa only [neg_apply, inner_neg_right] using hcQ y) ht
  refine pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  convert h using 3
  push_cast
  ring_nf

end ContinuousLinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem adjoint_toEuclideanCLM (A : Matrix n n ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) A) = toEuclideanCLM (𝕜 := ℝ) Aᵀ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

private theorem lyapunov_toEuclideanCLM (A P : Matrix n n ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) A) * toEuclideanCLM (𝕜 := ℝ) P +
        toEuclideanCLM (𝕜 := ℝ) P * toEuclideanCLM (𝕜 := ℝ) A =
      toEuclideanCLM (𝕜 := ℝ) (Aᵀ * P + P * A) := by
  rw [adjoint_toEuclideanCLM, map_add, map_mul, map_mul]

omit [DecidableEq n] in
/-- **Energy identity in coordinates.** If `x : ℝ → n → ℝ` solves `x' = A *ᵥ x` on the time set
`s`, then for every real matrix `P`, `d/dt (x ⬝ᵥ P *ᵥ x) = x ⬝ᵥ (Aᵀ * P + P * A) *ᵥ x` within
`s`. -/
theorem hasDerivWithinAt_dotProduct_mulVec {A P : Matrix n n ℝ} {x : ℝ → n → ℝ} {s : Set ℝ}
    (hx : ∀ t ∈ s, HasDerivWithinAt x (A *ᵥ x t) s t) {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun τ => x τ ⬝ᵥ P *ᵥ x τ) (x t ⬝ᵥ (Aᵀ * P + P * A) *ᵥ x t) s t := by
  classical
  have h := (isTrajectoryOn_toEuclideanCLM_iff.2 hx).hasDerivWithinAt_inner_apply
    (P := toEuclideanCLM (𝕜 := ℝ) P) ht
  simpa only [lyapunov_toEuclideanCLM, inner_toEuclideanCLM] using h

/-- **Quadratic Lyapunov criterion for matrices.** If `P` and `-(Aᵀ * P + P * A)` are positive
definite real matrices, then `ẋ = A x` is exponentially stable on `EuclideanSpace ℝ n`, i.e. in
the Euclidean norm. `P` is symmetric by `Matrix.PosDef`; no assumption on `A` is made. -/
theorem isExponentiallyStable_toEuclideanCLM_of_posDef {A P : Matrix n n ℝ} (hP : P.PosDef)
    (hQ : (-(Aᵀ * P + P * A)).PosDef) :
    (toEuclideanCLM (𝕜 := ℝ) A).IsExponentiallyStable := by
  have key : ∀ {M : Matrix n n ℝ}, M.PosDef → ∀ y : EuclideanSpace ℝ n, y ≠ 0 →
      0 < ⟪y, toEuclideanCLM (𝕜 := ℝ) M y⟫ := fun hM y hy => by
    rw [inner_toEuclideanCLM]
    simpa using hM.dotProduct_mulVec_pos (x := y.ofLp) (by simpa using hy)
  refine ContinuousLinearMap.isExponentiallyStable_of_inner_pos (P := toEuclideanCLM (𝕜 := ℝ) P)
    (key hP) fun y hy => ?_
  have := key hQ y hy
  rw [map_neg, neg_apply, inner_neg_right, ← lyapunov_toEuclideanCLM] at this
  linarith

end Matrix

/-! ### Instability and marginal stability from indefinite quadratic forms -/

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {x : ℝ → E}

omit [CompleteSpace E] in
private theorem norm_pos_of_inner_neg {y : E} (hy : ⟪y, P y⟫ < 0) : 0 < ‖P‖ :=
  norm_pos_iff.2 fun h => by simp [h] at hy

omit [CompleteSpace E] in
/-- **The growth constant is positive.** If `⟪y, P y⟫ < 0`, then `√(-⟪y, P y⟫ / ‖P‖) > 0`: the
constant of `IsTrajectoryOn.sqrt_mul_exp_le_norm` for a trajectory starting at `y`. -/
theorem sqrt_div_norm_pos_of_inner_neg {y : E} (hy : ⟪y, P y⟫ < 0) :
    0 < Real.sqrt (-⟪y, P y⟫ / ‖P‖) :=
  Real.sqrt_pos.2 (div_pos (neg_pos.2 hy) (norm_pos_of_inner_neg hy))

/-- **Energy growth along trajectories.** If `A† P + P A ≤ 2 ε P` as quadratic forms, then every
trajectory of `ẋ = A x` on `[0, ∞)` satisfies
`exp (2 ε t) * (-⟪x 0, P (x 0)⟫) ≤ ‖P‖ * ‖x t‖ ^ 2` for `t ≥ 0`. Neither `P` nor `ε` has a sign
condition; the bound is informative when `⟪x 0, P (x 0)⟫ < 0`. -/
theorem IsTrajectoryOn.exp_mul_neg_inner_le (hx : A.IsTrajectoryOn x (Ici 0)) {ε : ℝ}
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 2 * ε * ⟪y, P y⟫) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (2 * ε * t) * -⟪x 0, P (x 0)⟫ ≤ ‖P‖ * ‖x t‖ ^ 2 := by
  have h := hx.inner_apply_le_exp_mul hK ht
  linarith [neg_le_abs ⟪x t, P (x t)⟫, abs_inner_apply_le (P := P) (x t)]

/-- **Exponential growth of the norm.** If `A† P + P A ≤ 2 ε P` as quadratic forms, then every
trajectory of `ẋ = A x` on `[0, ∞)` satisfies `‖x t‖ ≥ C * exp (ε t)` for `t ≥ 0`, with
`C = √(-⟪x 0, P (x 0)⟫ / ‖P‖)`. There is no sign condition: `C > 0` when the trajectory starts
with negative energy `⟪x 0, P (x 0)⟫ < 0` (`sqrt_div_norm_pos_of_inner_neg`), and `C = 0`
otherwise. -/
theorem IsTrajectoryOn.sqrt_mul_exp_le_norm (hx : A.IsTrajectoryOn x (Ici 0)) {ε : ℝ}
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 2 * ε * ⟪y, P y⟫) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (-⟪x 0, P (x 0)⟫ / ‖P‖) * Real.exp (ε * t) ≤ ‖x t‖ := by
  rcases le_or_gt 0 ⟪x 0, P (x 0)⟫ with h0 | h0
  · rw [Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)),
      zero_mul]
    exact norm_nonneg _
  have hP := norm_pos_of_inner_neg h0
  have h := hx.exp_mul_neg_inner_le hK ht
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (div_nonneg (by linarith) hP.le), ← Real.exp_nat_mul,
    div_mul_eq_mul_div, div_le_iff₀ hP]
  convert h using 1 <;> push_cast <;> ring_nf

omit [CompleteSpace E] in
private theorem exists_inner_neg_norm_lt {y₀ : E} (hy₀ : ⟪y₀, P y₀⟫ < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : E, ‖y‖ < δ ∧ ⟪y, P y⟫ < 0 := by
  have hy : y₀ ≠ 0 := fun h => by simp [h] at hy₀
  have hn : 0 < ‖y₀‖ := norm_pos_iff.2 hy
  refine ⟨(δ / (2 * ‖y₀‖)) • y₀, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
    linarith
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
    exact mul_neg_of_pos_of_neg (by positivity) hy₀

/-- **Not asymptotically stable.** If `A† P + P A ≤ 2 ε P` with `ε ≥ 0` and some `y₀` has
`⟪y₀, P y₀⟫ < 0`, then `ẋ = A x` is not asymptotically stable: trajectories starting at small
multiples of `y₀` keep `‖P‖ ‖x t‖² ≥ -⟪x 0, P (x 0)⟫ > 0`. -/
theorem not_isAsymptoticallyStable_of_inner_neg {ε : ℝ} (hε : 0 ≤ ε)
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 2 * ε * ⟪y, P y⟫) {y₀ : E}
    (hy₀ : ⟪y₀, P y₀⟫ < 0) : ¬A.IsAsymptoticallyStable := by
  rintro ⟨-, δ, hδ, hA⟩
  obtain ⟨y, hy, hyP⟩ := exists_inner_neg_norm_lt hy₀ hδ
  have hx := isTrajectoryOn_exp_smul_apply A y (Ici 0)
  have hT : Tendsto (fun t : ℝ => exp (t • A) y) atTop (𝓝 0) := hA _ hx (by simpa using hy)
  have hlim : Tendsto (fun t : ℝ => ‖P‖ * ‖exp (t • A) y‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hT.norm.pow 2).const_mul ‖P‖
  obtain ⟨t, hlt, ht⟩ := ((hlim.eventually (gt_mem_nhds (neg_pos.2 hyP))).and
    (eventually_ge_atTop (0 : ℝ))).exists
  have h := hx.exp_mul_neg_inner_le hK ht
  simp only [zero_smul, exp_zero, one_apply_eq_self] at h
  have he : 1 ≤ Real.exp (2 * ε * t) := Real.one_le_exp (by positivity)
  nlinarith

/-- **Not Lyapunov stable.** If `A† P + P A ≤ 2 ε P` with `ε > 0` and some `y₀` has
`⟪y₀, P y₀⟫ < 0`, then `ẋ = A x` is not Lyapunov stable: trajectories starting at small multiples
of `y₀` grow like `exp (ε t)`. -/
theorem not_isLyapunovStable_of_inner_neg {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 2 * ε * ⟪y, P y⟫) {y₀ : E}
    (hy₀ : ⟪y₀, P y₀⟫ < 0) : ¬A.IsLyapunovStable := by
  intro hA
  obtain ⟨δ, hδ, hA⟩ := hA 1 one_pos
  obtain ⟨y, hy, hyP⟩ := exists_inner_neg_norm_lt hy₀ hδ
  have hx := isTrajectoryOn_exp_smul_apply A y (Ici 0)
  set c := -⟪y, P y⟫ with hc
  have hc0 : 0 < c := neg_pos.2 hyP
  set t := ‖P‖ / (2 * ε * c)
  have ht : 0 ≤ t := by positivity
  have h := hx.exp_mul_neg_inner_le hK ht
  simp only [zero_smul, exp_zero, one_apply_eq_self] at h
  have h1 : ‖exp (t • A) y‖ < 1 := hA _ hx (by simpa using hy) t ht
  have h2 : 2 * ε * t * c = ‖P‖ := by simp only [t]; field_simp
  have he := Real.add_one_le_exp (2 * ε * t)
  have h3 : ‖exp (t • A) y‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (exp (t • A) y)]
  nlinarith [norm_nonneg P]

/-- **An unbounded trajectory.** If `A† P + P A ≤ 2 ε P` with `ε > 0` and `⟪y₀, P y₀⟫ < 0`, then
the trajectory `t ↦ exp (t • A) y₀` of `ẋ = A x` tends to infinity in norm. -/
theorem tendsto_norm_exp_smul_apply_atTop {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 2 * ε * ⟪y, P y⟫) {y₀ : E}
    (hy₀ : ⟪y₀, P y₀⟫ < 0) : Tendsto (fun t : ℝ => ‖exp (t • A) y₀‖) atTop atTop := by
  have hx := isTrajectoryOn_exp_smul_apply A y₀ (Ici 0)
  have h0 : (fun t : ℝ => exp (t • A) y₀) 0 = y₀ := by simp
  have hC := sqrt_div_norm_pos_of_inner_neg hy₀
  refine tendsto_atTop_mono' _ ?_ ((Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop hε)).const_mul_atTop hC)
  filter_upwards [eventually_ge_atTop 0] with t ht
  simpa [h0] using hx.sqrt_mul_exp_le_norm hK ht

/-- **Lyapunov stability from a nonstrict Lyapunov inequality.** On a finite-dimensional real
inner product space, if `⟪y, P y⟫ > 0` for `y ≠ 0` and `⟪y, (A† P + P A) y⟫ ≤ 0` for every `y`,
then `ẋ = A x` is Lyapunov stable: `‖x t‖ ≤ √(M / m) ‖x 0‖` for the coercivity constants of
`P`. -/
theorem isLyapunovStable_of_inner_pos_of_nonpos [FiniteDimensional ℝ E]
    (hP : ∀ y ≠ 0, 0 < ⟪y, P y⟫) (hQ : ∀ y, ⟪y, (adjoint A * P + P * A) y⟫ ≤ 0) :
    A.IsLyapunovStable := by
  obtain ⟨m, hm, hlow⟩ := exists_pos_mul_norm_sq_le_inner_apply hP
  set M := ‖P‖ + 1
  have hM : 0 < M := by positivity
  have hup : ∀ y, ⟪y, P y⟫ ≤ M * ‖y‖ ^ 2 := fun y =>
    (le_abs_self _).trans <| (abs_inner_apply_le y).trans <|
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
  refine fun ε hε => ⟨ε * Real.sqrt (m / M), by positivity, fun x hx h0 t ht => ?_⟩
  have hV := hx.inner_apply_le_exp_mul (K := 0) (fun y => by simpa using hQ y) ht
  rw [zero_mul, Real.exp_zero, one_mul] at hV
  have hs : Real.sqrt (m / M) ^ 2 = m / M := Real.sq_sqrt (by positivity)
  have hδ : ‖x 0‖ ^ 2 < ε ^ 2 * (m / M) := by
    rw [← hs, ← mul_pow]
    exact pow_lt_pow_left₀ h0 (norm_nonneg _) two_ne_zero
  have hxt : m * ‖x t‖ ^ 2 < m * ε ^ 2 := by
    have : M * ‖x 0‖ ^ 2 < m * ε ^ 2 := by
      have := mul_lt_mul_of_pos_left hδ hM
      rwa [show M * (ε ^ 2 * (m / M)) = m * ε ^ 2 by field_simp] at this
    linarith [hlow (x t), hup (x 0)]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1
    (lt_of_mul_lt_mul_left hxt hm.le)

end ContinuousLinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix inequality `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0` is the quadratic-form
inequality `A† P + P A ≤ 2 ε P` of the Euclidean operators. -/
private theorem inner_le_of_posSemidef {A P : Matrix n n ℝ} {ε : ℝ}
    (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) (y : EuclideanSpace ℝ n) :
    ⟪y, (ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) A) * toEuclideanCLM (𝕜 := ℝ) P +
        toEuclideanCLM (𝕜 := ℝ) P * toEuclideanCLM (𝕜 := ℝ) A) y⟫ ≤
      2 * ε * ⟪y, toEuclideanCLM (𝕜 := ℝ) P y⟫ := by
  have hR : (A - ε • 1)ᵀ * P + P * (A - ε • 1) = Aᵀ * P + P * A - (2 * ε) • P := by
    rw [transpose_sub, transpose_smul, transpose_one, sub_mul, mul_sub, smul_mul_assoc,
      one_mul, mul_smul_comm, mul_one, two_mul, add_smul]
    abel
  have h := hQ.dotProduct_mulVec_nonneg y.ofLp
  rw [hR, star_trivial, neg_mulVec, dotProduct_neg, sub_mulVec, dotProduct_sub, smul_mulVec,
    dotProduct_smul, smul_eq_mul] at h
  rw [lyapunov_toEuclideanCLM, inner_toEuclideanCLM, inner_toEuclideanCLM]
  linarith

private theorem exp_smul_toLp (A : Matrix n n ℝ) (t : ℝ) (x₀ : n → ℝ) :
    exp (t • toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 x₀) = WithLp.toLp 2 (exp (t • A) *ᵥ x₀) :=
  WithLp.ofLp_injective 2 (by simp)

/-- **The growth constant is positive.** If `x₀ ⬝ᵥ P *ᵥ x₀ < 0`, then
`√(-(x₀ ⬝ᵥ P *ᵥ x₀) / ‖P‖) > 0` for the `ℓ²` operator norm of `P`: the constant of
`sqrt_mul_exp_le_norm_exp_smul_mulVec`. -/
theorem sqrt_div_norm_pos_of_dotProduct_neg {P : Matrix n n ℝ} {x₀ : n → ℝ}
    (hx₀ : x₀ ⬝ᵥ P *ᵥ x₀ < 0) :
    0 < Real.sqrt (-(x₀ ⬝ᵥ P *ᵥ x₀) / ‖toEuclideanCLM (𝕜 := ℝ) P‖) := by
  have h := ContinuousLinearMap.sqrt_div_norm_pos_of_inner_neg (P := toEuclideanCLM (𝕜 := ℝ) P)
    (y := WithLp.toLp 2 x₀) (by rwa [inner_toEuclideanCLM])
  rwa [inner_toEuclideanCLM] at h

/-- **Exponential growth from a shifted Lyapunov inequality.** If
`-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0`, then for every `x₀` the solution
`exp (t • A) *ᵥ x₀` of `ẋ = A x` satisfies `‖x t‖ ≥ C exp (ε t)` in the Euclidean norm for
`t ≥ 0`, with `C = √(-(x₀ ⬝ᵥ P *ᵥ x₀) / ‖P‖)` for the `ℓ²` operator norm of `P`. The constant is
positive when `x₀ ⬝ᵥ P *ᵥ x₀ < 0` (`sqrt_div_norm_pos_of_dotProduct_neg`) and zero otherwise. -/
theorem sqrt_mul_exp_le_norm_exp_smul_mulVec {A P : Matrix n n ℝ} {ε : ℝ}
    (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) (x₀ : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    Real.sqrt (-(x₀ ⬝ᵥ P *ᵥ x₀) / ‖toEuclideanCLM (𝕜 := ℝ) P‖) * Real.exp (ε * t) ≤
      ‖WithLp.toLp 2 (exp (t • A) *ᵥ x₀)‖ := by
  have h := (ContinuousLinearMap.isTrajectoryOn_exp_smul_apply (toEuclideanCLM (𝕜 := ℝ) A)
    (WithLp.toLp 2 x₀) (Ici 0)).sqrt_mul_exp_le_norm (inner_le_of_posSemidef hQ) ht
  simpa only [zero_smul, exp_zero, one_apply_eq_self, inner_toEuclideanCLM,
    exp_smul_toLp, WithLp.ofLp_toLp] using h

omit [DecidableEq n] in
private theorem norm_toLp_sq (y : n → ℝ) : ‖WithLp.toLp 2 y‖ ^ 2 = y ⬝ᵥ y := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  have h := inner_toEuclideanCLM (1 : Matrix n n ℝ) (WithLp.toLp 2 y) (WithLp.toLp 2 y)
  rwa [map_one, one_apply_eq_self, WithLp.ofLp_toLp, one_mulVec] at h

/-- **A lower bound on settling.** If `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0`, then the
solution `x t = exp (t • A) *ᵥ x₀` of `ẋ = A x` satisfies
`exp (2 ε t) * -(x₀ ⬝ᵥ P *ᵥ x₀) ≤ ‖P‖ * (x t ⬝ᵥ x t)` for `t ≥ 0`, for any sign of `ε`. Hence
`x t ⬝ᵥ x t > r` whenever `‖P‖ r < exp (2 ε t) * -(x₀ ⬝ᵥ P *ᵥ x₀)`: for `ε < 0` the state has not
settled into the ball `x ⬝ᵥ x ≤ r` before such a time, a lower bound complementing the upper
bounds of decay certificates. -/
theorem exp_mul_neg_le_norm_mul_dotProduct_self {A P : Matrix n n ℝ} {ε : ℝ}
    (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) (x₀ : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    Real.exp (2 * ε * t) * -(x₀ ⬝ᵥ P *ᵥ x₀) ≤
      ‖toEuclideanCLM (𝕜 := ℝ) P‖ * (exp (t • A) *ᵥ x₀ ⬝ᵥ exp (t • A) *ᵥ x₀) := by
  have h := (ContinuousLinearMap.isTrajectoryOn_exp_smul_apply (toEuclideanCLM (𝕜 := ℝ) A)
    (WithLp.toLp 2 x₀) (Ici 0)).exp_mul_neg_inner_le (inner_le_of_posSemidef hQ) ht
  simpa only [zero_smul, exp_zero, one_apply_eq_self, inner_toEuclideanCLM,
    exp_smul_toLp, WithLp.ofLp_toLp, norm_toLp_sq] using h

/-- **No asymptotic stability.** If `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0` with `ε ≥ 0` and
`x₀ ⬝ᵥ P *ᵥ x₀ < 0`, then `ẋ = A x` is not asymptotically stable. -/
theorem not_isAsymptoticallyStable_toEuclideanCLM_of_posSemidef {A P : Matrix n n ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) {x₀ : n → ℝ}
    (hx₀ : x₀ ⬝ᵥ P *ᵥ x₀ < 0) : ¬(toEuclideanCLM (𝕜 := ℝ) A).IsAsymptoticallyStable :=
  ContinuousLinearMap.not_isAsymptoticallyStable_of_inner_neg hε (inner_le_of_posSemidef hQ)
    (y₀ := WithLp.toLp 2 x₀) (by rwa [inner_toEuclideanCLM])

/-- **Instability.** If `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0` with `ε > 0` and
`x₀ ⬝ᵥ P *ᵥ x₀ < 0`, then `ẋ = A x` is not Lyapunov stable. -/
theorem not_isLyapunovStable_toEuclideanCLM_of_posSemidef {A P : Matrix n n ℝ} {ε : ℝ}
    (hε : 0 < ε) (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) {x₀ : n → ℝ}
    (hx₀ : x₀ ⬝ᵥ P *ᵥ x₀ < 0) : ¬(toEuclideanCLM (𝕜 := ℝ) A).IsLyapunovStable :=
  ContinuousLinearMap.not_isLyapunovStable_of_inner_neg hε (inner_le_of_posSemidef hQ)
    (y₀ := WithLp.toLp 2 x₀) (by rwa [inner_toEuclideanCLM])

/-- **An unbounded trajectory.** If `-((A - ε • 1)ᵀ * P + P * (A - ε • 1)) ⪰ 0` with `ε > 0`
and `x₀ ⬝ᵥ P *ᵥ x₀ < 0`, then `‖exp (t • A) *ᵥ x₀‖ → ∞` in the Euclidean norm. -/
theorem tendsto_norm_exp_smul_mulVec_atTop {A P : Matrix n n ℝ} {ε : ℝ} (hε : 0 < ε)
    (hQ : (-((A - ε • 1)ᵀ * P + P * (A - ε • 1))).PosSemidef) {x₀ : n → ℝ}
    (hx₀ : x₀ ⬝ᵥ P *ᵥ x₀ < 0) :
    Tendsto (fun t : ℝ => ‖WithLp.toLp 2 (exp (t • A) *ᵥ x₀)‖) atTop atTop := by
  simpa only [exp_smul_toLp] using
    ContinuousLinearMap.tendsto_norm_exp_smul_apply_atTop hε (inner_le_of_posSemidef hQ)
      (y₀ := WithLp.toLp 2 x₀) (by rwa [inner_toEuclideanCLM])

/-- **Lyapunov stability from a nonstrict Lyapunov inequality.** If `P ≻ 0` and
`-(Aᵀ * P + P * A) ⪰ 0`, then `ẋ = A x` is Lyapunov stable on `EuclideanSpace ℝ n`. -/
theorem isLyapunovStable_toEuclideanCLM_of_posDef_of_posSemidef {A P : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : (-(Aᵀ * P + P * A)).PosSemidef) :
    (toEuclideanCLM (𝕜 := ℝ) A).IsLyapunovStable := by
  refine ContinuousLinearMap.isLyapunovStable_of_inner_pos_of_nonpos
    (P := toEuclideanCLM (𝕜 := ℝ) P) (fun y hy => ?_) (fun y => ?_)
  · rw [inner_toEuclideanCLM]
    simpa using hP.dotProduct_mulVec_pos (x := y.ofLp) (by simpa using hy)
  · have := inner_le_of_posSemidef (ε := 0) (by simpa using hQ) y
    simpa using this

end Matrix
