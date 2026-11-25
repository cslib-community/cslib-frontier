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
    have h1 : M * Real.exp (-(α * t)) ≤ |M| :=
      (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le).trans
        (by simpa using mul_le_mul_of_nonneg_left hexp (abs_nonneg M))
    have hpos : 0 < |M| + 1 := by positivity
    have h0' := (lt_div_iff₀ hpos).1 h0
    have hle := (hM x hx t ht).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    nlinarith [norm_nonneg (x 0), abs_nonneg M]
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
    convert he.hasDerivWithinAt.mul (hV τ hτ) using 1; ring
  have hanti : AntitoneOn W (Ici a) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun τ hτ => (hW τ hτ).continuousWithinAt)
      (f' := fun τ => Real.exp (-(K * (τ - a))) * (V' τ - K * V τ))
      (fun τ hτ => ?_) (fun τ hτ => ?_)
    · rw [interior_Ici] at hτ ⊢; exact (hW τ hτ.le).mono Ioi_subset_Ici_self
    · rw [interior_Ici] at hτ
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.2 (hle τ hτ.le))
  have h := hanti self_mem_Ici (mem_Ici.2 ht) ht
  simp only [W, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  simpa only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] using
    mul_le_mul_of_nonneg_left h (Real.exp_pos (K * (t - a))).le

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
  refine ⟨⟪u, P u⟫, hP u (by rintro rfl; simp at hu), fun y => ?_⟩
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
    · have hy : ‖y‖ ^ 2 = 0 := by nlinarith [hlow y, hup y, sq_nonneg ‖y‖]
      simp [show y = 0 by simpa using hy]
    · have := mul_le_mul_of_nonneg_left (hup y) (div_nonneg hc hM.le)
      rw [← mul_assoc, div_mul_cancel₀ _ hM.ne'] at this
      linarith [hQ y]
  have hdecay := (hlow _).trans <| (hx.inner_apply_le_exp_mul hK ht).trans <|
    mul_le_mul_of_nonneg_left (hup _) (Real.exp_pos _).le
  rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀' hm]
  linarith

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
    (real_inner_le_norm _ _).trans <|
      (mul_le_mul_of_nonneg_left (P.le_opNorm y) (norm_nonneg _)).trans
        (by nlinarith [norm_nonneg y])
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
