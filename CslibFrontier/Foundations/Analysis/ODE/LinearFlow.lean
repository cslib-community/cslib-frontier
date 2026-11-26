/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/LinearFlow.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The flow of a linear time-invariant ODE

For a bounded linear operator `A : E →L[ℝ] E` on a real Banach space `E`, the curve
`t ↦ exp (t • A) x₀` solves `ẋ = A x` with `x 0 = x₀`, and it is the only solution on every
finite interval `[0, T]` and on `[0, ∞)`. No stability, spectral or diagonalizability assumption
is made. Finite-dimensional real systems are the case `E = EuclideanSpace ℝ n`,
`A = Matrix.toEuclideanCLM A`.

## Trajectories

`ContinuousLinearMap.IsTrajectoryOn A x s` says that at every time `t ∈ s` the curve `x` has
derivative `A (x t)` *within `s`*. For `s = Set.Ici 0` this is a two-sided derivative at every
`t > 0` and a right derivative at the initial time `0`; for `s = Set.Icc 0 T` the endpoint `T`
has a left derivative. Differentiability within `s` implies continuity on `s`, so no separate
continuity hypothesis is needed.

## Matrices, vectors and norms

A real `n × n` matrix acts on coordinate vectors `n → ℝ` by `Matrix.mulVec`. The type `n → ℝ`
carries Mathlib's *supremum* norm, which is not the Euclidean norm, so the statements here that
involve norms (and the stability notions built on them) are stated on `EuclideanSpace ℝ n`, whose
norm is `ℓ²`, through `Matrix.toEuclideanCLM`. Derivatives do not depend on the choice of norm,
and `Matrix.isTrajectoryOn_toEuclideanCLM_iff` translates between the two coordinate pictures.
The matrix exponential `NormedSpace.exp (t • A)` of `A : Matrix n n ℝ` only uses the entrywise
topology of matrices, so no matrix norm instance is chosen here; operator norms that appear later
are those of `Matrix.toEuclideanCLM A`, i.e. `ℓ²` operator norms.

## Main definitions

* `ContinuousLinearMap.IsTrajectoryOn A x s`: `x` solves `ẋ = A x` on the time set `s`.

## Main results

* `ContinuousLinearMap.isTrajectoryOn_exp_smul_apply`: `t ↦ exp (t • A) x₀` is a trajectory on
  every time set.
* `ContinuousLinearMap.IsTrajectoryOn.eqOn_exp_smul_apply_Icc` and
  `ContinuousLinearMap.IsTrajectoryOn.eqOn_exp_smul_apply_Ici`: uniqueness, every trajectory on
  `[0, T]` or on `[0, ∞)` is `t ↦ exp (t • A) (x 0)` there.
* `Matrix.toEuclideanCLM_exp`: `Matrix.toEuclideanCLM` commutes with the exponential.
* `Matrix.isTrajectoryOn_toEuclideanCLM_iff`: trajectories in `EuclideanSpace ℝ n` are coordinate
  curves `x : ℝ → n → ℝ` with `x' = A *ᵥ x`.
* `Matrix.eq_exp_smul_mulVec_of_hasDerivWithinAt`: every coordinate solution of `x' = A *ᵥ x` on
  `[0, ∞)` is `exp (t • A) *ᵥ x 0`.
* `Matrix.exp_smul_mul_eq_of_hasDerivWithinAt`: every matrix solution of `X' = A * X` on `[0, ∞)`
  is `exp (t • A) * X 0`, which certifies proposed closed forms of `exp (t • A) * B`.
-/

public section

open Set NormedSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The curve `x` is a trajectory of the linear ODE `ẋ = A x` on the time set `s`: at every
`t ∈ s` it has derivative `A (x t)` within `s`. On `s = Set.Ici 0` the derivative at the initial
time `0` is a right derivative. -/
@[expose] def IsTrajectoryOn (A : E →L[ℝ] E) (x : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt x (A (x t)) s t

variable {A : E →L[ℝ] E} {x : ℝ → E} {s s' : Set ℝ}

theorem IsTrajectoryOn.mono (hx : A.IsTrajectoryOn x s) (h : s' ⊆ s) :
    A.IsTrajectoryOn x s' :=
  fun t ht => (hx t (h ht)).mono h

theorem IsTrajectoryOn.continuousOn (hx : A.IsTrajectoryOn x s) : ContinuousOn x s :=
  fun t ht => (hx t ht).continuousWithinAt

variable [CompleteSpace E]

private theorem hasDerivAt_exp_smul_apply (A : E →L[ℝ] E) (x₀ : E) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => exp (τ • A) x₀) (A (exp (t • A) x₀)) t := by
  simpa using (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t x₀)

/-- **Existence.** The curve `t ↦ exp (t • A) x₀` is a trajectory of `ẋ = A x` on every time set;
its value at `0` is `x₀`. -/
theorem isTrajectoryOn_exp_smul_apply (A : E →L[ℝ] E) (x₀ : E) (s : Set ℝ) :
    A.IsTrajectoryOn (fun t => exp (t • A) x₀) s :=
  fun t _ => (hasDerivAt_exp_smul_apply A x₀ t).hasDerivWithinAt

/-- **Uniqueness on a finite interval.** A trajectory of `ẋ = A x` on `[0, T]` is
`t ↦ exp (t • A) (x 0)` there. -/
theorem IsTrajectoryOn.eqOn_exp_smul_apply_Icc {T : ℝ} (hx : A.IsTrajectoryOn x (Icc 0 T)) :
    EqOn x (fun t => exp (t • A) (x 0)) (Icc 0 T) := by
  refine ODE_solution_unique (v := fun _ => A) (fun _ => A.lipschitzWith) hx.continuousOn
    (fun t ht => (hx t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
    ((isTrajectoryOn_exp_smul_apply A (x 0) _).continuousOn)
    (fun t _ => (hasDerivAt_exp_smul_apply A (x 0) t).hasDerivWithinAt) ?_
  simp

/-- **Uniqueness on `[0, ∞)`.** A trajectory of `ẋ = A x` on `[0, ∞)` is
`t ↦ exp (t • A) (x 0)` there. -/
theorem IsTrajectoryOn.eqOn_exp_smul_apply_Ici (hx : A.IsTrajectoryOn x (Ici 0)) :
    EqOn x (fun t => exp (t • A) (x 0)) (Ici 0) :=
  fun t ht => (hx.mono Icc_subset_Ici_self).eqOn_exp_smul_apply_Icc (T := t) ⟨ht, le_rfl⟩

end ContinuousLinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Matrix.toEuclideanCLM` commutes with the exponential. -/
theorem toEuclideanCLM_exp {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (exp A) = exp (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  -- Any normed-ring structure inducing the entrywise topology computes the same exponential.
  open scoped Matrix.Norms.L2Operator in
  exact map_exp_of_mem_ball (𝕂 := 𝕜) (toEuclideanCLM (n := n) (𝕜 := 𝕜))
    ((toEuclideanCLM (n := n) (𝕜 := 𝕜)).toAlgEquiv.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional) A <|
    (expSeries_radius_eq_top 𝕜 (Matrix n n 𝕜)).symm ▸ edist_lt_top _ _

/-- The flow of `Matrix.toEuclideanCLM A` in coordinates is the matrix exponential. -/
@[simp]
theorem ofLp_exp_smul_toEuclideanCLM_apply (A : Matrix n n ℝ) (t : ℝ) (x : EuclideanSpace ℝ n) :
    (exp (t • toEuclideanCLM (𝕜 := ℝ) A) x).ofLp = exp (t • A) *ᵥ x.ofLp := by
  rw [← map_smul, ← toEuclideanCLM_exp, ofLp_toEuclideanCLM]

/-- A curve in `EuclideanSpace ℝ n` is a trajectory of `Matrix.toEuclideanCLM A` exactly when its
coordinate curve solves `x' = A *ᵥ x`. -/
theorem isTrajectoryOn_toEuclideanCLM_iff {A : Matrix n n ℝ} {x : ℝ → n → ℝ} {s : Set ℝ} :
    (toEuclideanCLM (𝕜 := ℝ) A).IsTrajectoryOn (fun t => WithLp.toLp 2 (x t)) s ↔
      ∀ t ∈ s, HasDerivWithinAt x (A *ᵥ x t) s t := by
  refine forall₂_congr fun t _ => ?_
  rw [toEuclideanCLM_toLp]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (E := fun _ : n => ℝ) _).comp_hasDerivWithinAt t h
    exact this
  · have := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (E := fun _ : n => ℝ) _).comp_hasDerivWithinAt t h
    exact this

/-- **Uniqueness in coordinates.** Every solution `x : ℝ → n → ℝ` of `x' = A *ᵥ x` on `[0, ∞)`,
with a right derivative at `0`, is `exp (t • A) *ᵥ x 0` for `t ≥ 0`. -/
theorem eq_exp_smul_mulVec_of_hasDerivWithinAt {A : Matrix n n ℝ} {x : ℝ → n → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (A *ᵥ x t) (Ici 0) t) {t : ℝ} (ht : 0 ≤ t) :
    x t = exp (t • A) *ᵥ x 0 := by
  have h := (isTrajectoryOn_toEuclideanCLM_iff.2 hx).eqOn_exp_smul_apply_Ici ht
  simpa using congrArg WithLp.ofLp h

/-- **Certifying a matrix exponential.** If every column of a matrix curve `X : ℝ → Matrix n m ℝ`
solves `x' = A *ᵥ x` on `[0, ∞)`, i.e. `X' = A * X`, then `X t = exp (t • A) * X 0` for `t ≥ 0`.
A proposed closed form for `exp (t • A) * B` is thus checked by `X 0 = B` and the derivative
obligations, without computing a matrix exponential. -/
theorem exp_smul_mul_eq_of_hasDerivWithinAt {m : Type*} {A : Matrix n n ℝ} {X : ℝ → Matrix n m ℝ}
    (hX : ∀ j, ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun τ => (X τ)ᵀ j) (A *ᵥ (X t)ᵀ j) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : exp (t • A) * X 0 = X t := by
  ext i j
  have h := congrFun (eq_exp_smul_mulVec_of_hasDerivWithinAt (hX j) ht) i
  simp only [transpose_apply] at h
  rw [h, Matrix.mul_apply, mulVec, dotProduct]
  rfl

end Matrix
