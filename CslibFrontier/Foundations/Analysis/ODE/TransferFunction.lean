/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/TransferFunction.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.Hurwitz
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Transfer functions of LTI systems

For an `LTISystem` `ẋ = A x + B u`, `y = C x + D u` with real matrices, the transfer function is
the complex matrix-valued function `H s = C (s I - A)⁻¹ B + D` (`LTISystem.transferFunction`), with
`A`, `B`, `C`, `D` read over `ℂ`. It is defined algebraically, without the Laplace transform; the
inverse is `Matrix.inv`, which is a genuine inverse exactly when `s I - A` is invertible, i.e. when
`s` is not an eigenvalue of `A` (`spectrum.notMem_iff`), equivalently not a root of the
characteristic polynomial (`Matrix.isUnit_smul_one_sub_map_iff`). At an eigenvalue Lean's junk
value `(s I - A)⁻¹ = 0` gives `H s = D`.

* Every entry of `H` is complex differentiable (holomorphic) at every `s` that is not an
  eigenvalue of `A` (`LTISystem.differentiableAt_transferFunction`): matrix inversion is
  differentiable at invertible elements.
* If every trajectory of `ẋ = A x` satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖`, every eigenvalue has
  real part at most `-α` (`Matrix.re_le_of_forall_norm_le`), so `H` is holomorphic on the half-plane
  `re s > -α` (`LTISystem.differentiableOn_transferFunction_of_norm_le`); in particular, under
  exponential stability, for instance from an accepted `Cslib.LinearAlgebra.LyapunovCert`, on an
  open half-plane containing the closed right half-plane `re s ≥ 0`
  (`LTISystem.differentiableOn_transferFunction_of_isExponentiallyStable`).

The converse fails: a pole of `(s I - A)⁻¹` can cancel in `C (s I - A)⁻¹ B`, so `H` can be
holomorphic on `re s ≥ 0` although `A` has an unstable eigenvalue (a *hidden mode*); the tests check
such an example. Internal stability is a property of `A`, not of `H`.

## Main definitions

* `LTISystem.transferFunction`: `H s = C (s I - A)⁻¹ B + D` over `ℂ`.

## Main results

* `Matrix.isUnit_smul_one_sub_map_iff`
* `LTISystem.differentiableAt_transferFunction`
* `LTISystem.differentiableOn_transferFunction_of_norm_le`
* `LTISystem.differentiableOn_transferFunction_of_isExponentiallyStable`
-/

public section

open Set Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `s I - A` is invertible over `ℂ` iff `s` is not a root of the characteristic polynomial of the
real matrix `A`. -/
theorem isUnit_smul_one_sub_map_iff {A : Matrix n n ℝ} {s : ℂ} :
    IsUnit (s • (1 : Matrix n n ℂ) - A.map (algebraMap ℝ ℂ)) ↔
      (A.charpoly.map (algebraMap ℝ ℂ)).eval s ≠ 0 := by
  rw [← charpoly_map, eval_charpoly, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, scalar_apply,
    smul_one_eq_diagonal]

end Matrix

namespace LTISystem

variable {n m p : Type*} [Fintype n] [DecidableEq n] (S : LTISystem n m p)

/-- The **transfer function** `H s = C (s I - A)⁻¹ B + D` of an LTI system, a complex `p × m`
matrix for each `s : ℂ`, with the real system matrices read over `ℂ`. The inverse is a genuine
inverse when `s` is not an eigenvalue of `A`; at an eigenvalue it is `0` and `H s = D`. -/
@[expose] noncomputable def transferFunction (s : ℂ) : Matrix p m ℂ :=
  S.C.map (algebraMap ℝ ℂ) * (s • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))⁻¹ *
    S.B.map (algebraMap ℝ ℂ) + S.D.map (algebraMap ℝ ℂ)

/-- **The transfer function is holomorphic off the spectrum.** Every entry of
`H s = C (s I - A)⁻¹ B + D` is complex differentiable at every `s` that is not an eigenvalue of
`A`. -/
theorem differentiableAt_transferFunction {s : ℂ}
    (hs : s ∉ spectrum ℂ (S.A.map (algebraMap ℝ ℂ))) (i : p) (j : m) :
    DifferentiableAt ℂ (fun z => S.transferFunction z i j) s := by
  have hu : IsUnit (s • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ)) := by
    rwa [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one] at hs
  have hinv : ∀ k l, DifferentiableAt ℂ
      (fun z : ℂ => (z • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))⁻¹ k l) s := by
    intro k l
    open scoped Matrix.Norms.Operator in
    have h1 : DifferentiableAt ℂ
        (fun z : ℂ => Ring.inverse (z • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))) s :=
      (differentiableAt_inverse hu).comp s
        ((differentiableAt_id.smul_const (1 : Matrix n n ℂ)).sub_const _)
    open scoped Matrix.Norms.Operator in
    have h2 := (LinearMap.toContinuousLinearMap
      (entryLinearMap ℂ ℂ k l : Matrix n n ℂ →ₗ[ℂ] ℂ)).differentiableAt.comp s h1
    simpa [Function.comp_def, nonsing_inv_eq_ringInverse] using h2
  have e : (fun z => S.transferFunction z i j) = fun z =>
      ∑ l, (∑ k, S.C.map (algebraMap ℝ ℂ) i k *
        (z • (1 : Matrix n n ℂ) - S.A.map (algebraMap ℝ ℂ))⁻¹ k l) * S.B.map (algebraMap ℝ ℂ) l j +
        S.D.map (algebraMap ℝ ℂ) i j := by
    funext z
    simp only [transferFunction, Matrix.add_apply, Matrix.mul_apply]
  rw [e]
  exact (DifferentiableAt.fun_sum fun l _ => (DifferentiableAt.fun_sum fun k _ =>
    (hinv k l).const_mul _).mul_const _).add_const _

/-- **Holomorphy on a half-plane from a decay rate.** If every trajectory of `ẋ = A x` on `[0, ∞)`
satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖` in the Euclidean norm, every entry of the transfer function
is holomorphic on the open half-plane `re s > -α`. -/
theorem differentiableOn_transferFunction_of_norm_le {M α : ℝ}
    (h : ∀ x : ℝ → EuclideanSpace ℝ n, (toEuclideanCLM (𝕜 := ℝ) S.A).IsTrajectoryOn x (Ici 0) →
      ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖) (i : p) (j : m) :
    DifferentiableOn ℂ (fun s => S.transferFunction s i j) {s | -α < s.re} := fun _ hs =>
  (S.differentiableAt_transferFunction (fun hμ => (not_le.2 hs) (re_le_of_forall_norm_le h hμ))
    i j).differentiableWithinAt

/-- **Stable systems have transfer functions holomorphic on the closed right half-plane.** If
`ẋ = A x` is exponentially stable in the Euclidean norm, for instance by
`Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check`, then there is `α > 0` such that
every entry of the transfer function is holomorphic on `re s > -α`, an open half-plane containing
`re s ≥ 0`. -/
theorem differentiableOn_transferFunction_of_isExponentiallyStable
    (hA : (toEuclideanCLM (𝕜 := ℝ) S.A).IsExponentiallyStable) :
    ∃ α > 0, ∀ i j, DifferentiableOn ℂ (fun s => S.transferFunction s i j) {s | -α < s.re} :=
  let ⟨_, α, hα, h⟩ := hA
  ⟨α, hα, S.differentiableOn_transferFunction_of_norm_le h⟩

end LTISystem
