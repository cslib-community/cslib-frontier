/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/StateSpace.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.VariationOfConstants
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuous-time LTI state-space systems: forced response and impulse response

A finite-dimensional real continuous-time linear time-invariant system
`ẋ = A x + B u`, `y = C x + D u` with state index `n`, input index `m` and output index `p` is an
`LTISystem n m p`: the four real matrices `A : n × n`, `B : n × m`, `C : p × n`, `D : p × m`.
States, inputs and outputs are coordinate vectors `n → ℝ`, `m → ℝ`, `p → ℝ`; no norm is used.

## Admissible inputs and solutions

The admissible inputs on a time set `[0, T]` or `[0, ∞)` are the functions `u : ℝ → m → ℝ` that
are continuous there; their values at negative times are never used, and an input need not be
bounded on `[0, ∞)`. A state curve `x` is a solution on the time set `s` (`LTISystem.IsSolutionOn`)
when it has derivative `A x t + B u t` within `s` at each `t ∈ s`: one-sided derivatives at the
endpoints of `[0, T]` and at the initial time `0` of `[0, ∞)`. Such a curve is continuous on `s`.
The homogeneous case `u = 0` is `ContinuousLinearMap.IsTrajectoryOn` of
`Matrix.toEuclideanCLM A`, through `Matrix.isTrajectoryOn_toEuclideanCLM_iff`.

For every initial state `x₀` and admissible input the unique solution is
`x t = exp (t • A) *ᵥ x₀ + ∫ s in 0..t, exp ((t - s) • A) *ᵥ (B *ᵥ u s)`
(`LTISystem.isSolutionOn_Icc`, `LTISystem.IsSolutionOn.eq_Icc` and their `Ici` versions), with no
stability, minimality, controllability, observability or diagonalizability assumption.

## Impulse response and direct feedthrough

The *response kernel* is `h t = C * exp (t • A) * B` (`LTISystem.responseKernel`, with defining
equation `LTISystem.responseKernel_eq`); its time-zero value is `h 0 = C * B`. Every solution has
output (`LTISystem.IsSolutionOn.output_eq`, `LTISystem.IsSolutionOn.output_eq_Ici`)
`y t = C *ᵥ (exp (t • A) *ᵥ x 0) + D *ᵥ u t + ∫ s in 0..t, h (t - s) *ᵥ u s`
for `t ≥ 0`: the zero-input response from the initial state, plus the zero-state input/output
response `D u + h ∗ u`. This is derived from the state equation, not from a transfer function.

The informal impulse response `D δ₀ + h` of a system with direct feedthrough is never formed:
there is no Dirac delta here, and the system's input/output behaviour is described by the pair
`(D, h)` through the formula above. For `D = 0` the causal extension `(Set.Ici 0).indicator h` is
the ordinary impulse-response function: the zero-state output is its convolution over `ℝ` with the
causal extension of the input (`LTISystem.IsSolutionOn.output_eq_integral_indicator`). An impulse
`v δ₀` is given state-jump semantics: it moves the state from `0` to `B *ᵥ v`, after which the
unforced output is `h t *ᵥ v` for `t ≥ 0` (`LTISystem.responseKernel_mulVec_eq`).

## Certifying closed forms

A proposed closed form of `h`, for instance from an untrusted symbolic tool, is certified from a
state-space realization of the proposal, without computing a matrix exponential: if a matrix curve
`X` satisfies `X 0 = B` and `X' = A * X` columnwise on `[0, ∞)`, then `h t = C * X t` for `t ≥ 0`
(`LTISystem.responseKernel_eq_of_hasDerivWithinAt`, from
`Matrix.exp_smul_mul_eq_of_hasDerivWithinAt`). The obligations are an initial value and ordinary
derivatives, discharged with Mathlib's calculus API. This module is the only import needed from
the ODE layer; a client also imports the Mathlib `HasDerivAt` rules (for `Real.exp`, `Real.sin`,
products, ...) that its closed form uses.

## Realizations of other models

The theorems here concern the matrices `A`, `B`, `C`, `D`. A model of another kind, such as a
circuit with selected input and output ports, has these responses only through a proof that its
input/output behaviour for the admissible inputs is that of an `LTISystem`: its outputs, after
subtracting the equilibrium output and input, agree with `C *ᵥ x t + D *ᵥ u t` along solutions,
including the feedthrough `D`. By `LTISystem.IsSolutionOn.output_eq` the zero-state behaviour is
determined by `(D, h)`, and `LTISystem.responseKernel_similar` shows that a change of state
coordinates does not change it. An elimination that makes the state depend on derivatives of the
input does not produce a system of this form.

## Main definitions

* `LTISystem n m p`: the matrices `A`, `B`, `C`, `D` of `ẋ = A x + B u`, `y = C x + D u`.
* `LTISystem.IsSolutionOn S u x s`: `x` solves the state equation of `S` with input `u` on `s`.
* `LTISystem.responseKernel S t = C * exp (t • A) * B`.

## Main results

* `LTISystem.isSolutionOn_Icc`, `LTISystem.isSolutionOn_Ici`: the variation-of-constants curve is
  a solution on `[0, T]`, resp. `[0, ∞)`.
* `LTISystem.IsSolutionOn.eq_Icc`, `LTISystem.IsSolutionOn.eq_Ici`: every solution is the
  variation-of-constants curve of its initial state.
* `LTISystem.IsSolutionOn.output_eq`, `LTISystem.IsSolutionOn.output_eq_Ici`: the output formula
  with initial state, feedthrough and convolution terms, on `[0, T]`, resp. `[0, ∞)`.
* `LTISystem.IsSolutionOn.output_eq_integral_indicator`: for `D = 0` and zero initial state, the
  output is the convolution over `ℝ` of the causal kernel with the causal input.
* `LTISystem.responseKernel_mulVec_eq`: the response of the unforced system from the state
  `B *ᵥ v` is `h t *ᵥ v`.
* `LTISystem.responseKernel_eq_of_hasDerivWithinAt`: certification of a closed form of `h`.
* `LTISystem.responseKernel_similar`: a change of state coordinates preserves `h` (and `D`).

## References

* S. Boyd, *EE263: Introduction to Linear Dynamical Systems*, Stanford, Lecture 14 (Stanford
  Engineering Everywhere transcript), from "So you get X of T": the forced solution formula
  (derived there with the Laplace transform; here from the state equation and uniqueness), then
  the impulse matrix `C e^{tA} B + D δ` and the feed-through term. No Dirac delta is formalized.
-/

public section

open Set NormedSpace Matrix MeasureTheory

/-- A finite-dimensional real continuous-time linear time-invariant state-space system
`ẋ = A x + B u`, `y = C x + D u`, with state index `n`, input index `m` and output index `p`. -/
structure LTISystem (n m p : Type*) where
  /-- The state matrix, `n × n`. -/
  A : Matrix n n ℝ
  /-- The input matrix, `n × m`. -/
  B : Matrix n m ℝ
  /-- The output matrix, `p × n`. -/
  C : Matrix p n ℝ
  /-- The direct-feedthrough matrix, `p × m`. -/
  D : Matrix p m ℝ

namespace LTISystem

variable {n m p : Type*} [Fintype n] [DecidableEq n] (S : LTISystem n m p)

/-! ### The response kernel -/

/-- The response kernel `h t = C * exp (t • A) * B`. For `t ≥ 0` it is the regular part of the
impulse response, and the whole impulse response when `D = 0`. -/
noncomputable def responseKernel (t : ℝ) : Matrix p m ℝ := S.C * exp (t • S.A) * S.B

/-- The defining equation of the response kernel, for every `t : ℝ`. -/
theorem responseKernel_eq (t : ℝ) : S.responseKernel t = S.C * exp (t • S.A) * S.B := by
  rfl

/-- The time-zero value of the response kernel is `C * B`. -/
@[simp]
theorem responseKernel_zero : S.responseKernel 0 = S.C * S.B := by
  simp [responseKernel_eq]

variable {S}

/-- **Certifying a closed form of the response kernel.** If the columns of a matrix curve
`X : ℝ → Matrix n m ℝ` solve `x' = A *ᵥ x` on `[0, ∞)` and `X 0 = B`, then `h t = C * X t` for
`t ≥ 0`. No matrix exponential is computed: the obligations are an initial value and ordinary
derivatives. -/
theorem responseKernel_eq_of_hasDerivWithinAt {X : ℝ → Matrix n m ℝ}
    (hX : ∀ j, ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun τ => (X τ)ᵀ j) (S.A *ᵥ (X t)ᵀ j) (Ici 0) t)
    (hX₀ : X 0 = S.B) {t : ℝ} (ht : 0 ≤ t) : S.responseKernel t = S.C * X t := by
  rw [responseKernel_eq, Matrix.mul_assoc, ← hX₀, exp_smul_mul_eq_of_hasDerivWithinAt hX ht]

/-- **Similar realizations have the same response kernel.** The change of state coordinates
`x ↦ T x` by an invertible `T` maps `(A, B, C, D)` to `(T A T⁻¹, T B, C T⁻¹, D)` and preserves the
response kernel; the feedthrough `D` is unchanged. -/
theorem responseKernel_similar {T : Matrix n n ℝ} (hT : IsUnit T) (t : ℝ) :
    ({ A := T * S.A * T⁻¹, B := T * S.B, C := S.C * T⁻¹, D := S.D } :
      LTISystem n m p).responseKernel t = S.responseKernel t := by
  have hdet := (Matrix.isUnit_iff_isUnit_det T).1 hT
  simp only [responseKernel_eq]
  rw [show t • (T * S.A * T⁻¹) = T * (t • S.A) * T⁻¹ by
    rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj T _ hT]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

/-! ### Solutions of the state equation -/

variable [Fintype m]

variable (S) in
/-- The state curve `x : ℝ → n → ℝ` solves the state equation `ẋ = A x + B u` of `S` with input
`u` on the time set `s`: at every `t ∈ s` its derivative within `s` is `A *ᵥ x t + B *ᵥ u t`. -/
@[expose] def IsSolutionOn (u : ℝ → m → ℝ) (x : ℝ → n → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt x (S.A *ᵥ x t + S.B *ᵥ u t) s t

variable {u : ℝ → m → ℝ} {x : ℝ → n → ℝ} {s s' : Set ℝ}

omit [DecidableEq n] in
theorem IsSolutionOn.mono (hx : S.IsSolutionOn u x s) (h : s' ⊆ s) : S.IsSolutionOn u x s' :=
  fun t ht => (hx t (h ht)).mono h

/-! ### Transport to `EuclideanSpace` -/

omit [DecidableEq n] [Fintype m] in
private theorem ofLp_intervalIntegral (g : ℝ → EuclideanSpace ℝ n) (a b : ℝ) :
    (∫ s in a..b, g s).ofLp = ∫ s in a..b, (g s).ofLp := by
  have h := fun μ : Measure ℝ => (EuclideanSpace.equiv n ℝ).integral_comp_comm (μ := μ) g
  simp only [intervalIntegral, WithLp.ofLp_sub]
  exact congrArg₂ _ (h _).symm (h _).symm

/-- The Euclidean variation-of-constants curve in coordinates. -/
private theorem ofLp_variationOfConstants (A : Matrix n n ℝ) (g : ℝ → n → ℝ) (x₀ : n → ℝ)
    (t : ℝ) :
    (exp (t • toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 x₀) + ∫ s in 0..t,
      exp ((t - s) • toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 (g s))).ofLp =
      exp (t • A) *ᵥ x₀ + ∫ s in 0..t, exp ((t - s) • A) *ᵥ g s := by
  rw [WithLp.ofLp_add, ofLp_intervalIntegral]
  simp

/-- In Euclidean coordinates, the state equation is the forced equation of
`Matrix.toEuclideanCLM A` with forcing `B *ᵥ u`. -/
private theorem isSolutionOn_iff_toLp :
    S.IsSolutionOn u x s ↔ ∀ t ∈ s, HasDerivWithinAt (fun τ => WithLp.toLp 2 (x τ))
      (toEuclideanCLM (𝕜 := ℝ) S.A (WithLp.toLp 2 (x t)) + WithLp.toLp 2 (S.B *ᵥ u t)) s t := by
  refine forall₂_congr fun t _ => ?_
  rw [toEuclideanCLM_toLp, ← WithLp.toLp_add]
  exact ⟨fun h => HasFDerivAt.comp_hasDerivWithinAt t
      (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (E := fun _ : n => ℝ) _) h,
    fun h => HasFDerivAt.comp_hasDerivWithinAt t
      (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (E := fun _ : n => ℝ) _) h⟩

omit [Fintype n] [DecidableEq n] in
private theorem continuousOn_toLp_mulVec (M : Matrix n m ℝ) {T : Set ℝ}
    (hu : ContinuousOn u T) : ContinuousOn (fun s => WithLp.toLp 2 (M *ᵥ u s)) T :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn
    (((continuous_const (y := M)).matrix_mulVec continuous_id).comp_continuousOn hu)

private theorem intervalIntegrable_exp_smul_mulVec (A : Matrix n n ℝ) {g : ℝ → n → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hg : ContinuousOn g (Icc 0 t)) :
    IntervalIntegrable (fun s => exp ((t - s) • A) *ᵥ g s) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht]
  have hc : Continuous fun s : ℝ => exp ((t - s) • toEuclideanCLM (𝕜 := ℝ) A) :=
    (differentiable_exp_smul_const ℝ (toEuclideanCLM (𝕜 := ℝ) A)).continuous.comp
      (continuous_const.sub continuous_id)
  simpa [Function.comp_def] using (PiLp.continuous_ofLp 2 (fun _ : n => ℝ)).comp_continuousOn
    (hc.continuousOn.clm_apply ((PiLp.continuous_toLp 2 _).comp_continuousOn hg))

/-! ### Existence and uniqueness: variation of constants -/

/-- **Existence on `[0, T]`.** For an input continuous on `[0, T]` and any initial state `x₀`, the
variation-of-constants curve is a solution on `[0, T]`. -/
theorem isSolutionOn_Icc (x₀ : n → ℝ) {T : ℝ} (hu : ContinuousOn u (Icc 0 T)) :
    S.IsSolutionOn u
      (fun t => exp (t • S.A) *ᵥ x₀ + ∫ s in 0..t, exp ((t - s) • S.A) *ᵥ (S.B *ᵥ u s))
      (Icc 0 T) := by
  refine isSolutionOn_iff_toLp.2 fun t ht => ?_
  simpa only [← ofLp_variationOfConstants, WithLp.toLp_ofLp] using
    (toEuclideanCLM (𝕜 := ℝ) S.A).hasDerivWithinAt_exp_smul_apply_add_integral_Icc
      (WithLp.toLp 2 x₀) (continuousOn_toLp_mulVec S.B hu) ht

/-- **Existence on `[0, ∞)`.** For an input continuous on `[0, ∞)` and any initial state `x₀`, the
variation-of-constants curve is a solution on `[0, ∞)`. -/
theorem isSolutionOn_Ici (x₀ : n → ℝ) (hu : ContinuousOn u (Ici 0)) :
    S.IsSolutionOn u
      (fun t => exp (t • S.A) *ᵥ x₀ + ∫ s in 0..t, exp ((t - s) • S.A) *ᵥ (S.B *ᵥ u s))
      (Ici 0) := by
  refine isSolutionOn_iff_toLp.2 fun t ht => ?_
  simpa only [← ofLp_variationOfConstants, WithLp.toLp_ofLp] using
    (toEuclideanCLM (𝕜 := ℝ) S.A).hasDerivWithinAt_exp_smul_apply_add_integral_Ici
      (WithLp.toLp 2 x₀) (continuousOn_toLp_mulVec S.B hu) ht

/-- **Uniqueness on `[0, T]`.** For an input continuous on `[0, T]`, every solution on `[0, T]` is
the variation-of-constants curve of its initial state:
`x t = exp (t • A) *ᵥ x 0 + ∫ s in 0..t, exp ((t - s) • A) *ᵥ (B *ᵥ u s)`. -/
theorem IsSolutionOn.eq_Icc {T : ℝ} (hx : S.IsSolutionOn u x (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    x t = exp (t • S.A) *ᵥ x 0 + ∫ s in 0..t, exp ((t - s) • S.A) *ᵥ (S.B *ᵥ u s) := by
  have h := congrArg WithLp.ofLp <| ContinuousLinearMap.eqOn_exp_smul_apply_add_integral_Icc
    (continuousOn_toLp_mulVec S.B hu) (isSolutionOn_iff_toLp.1 hx) ht
  rwa [ofLp_variationOfConstants, WithLp.ofLp_toLp] at h

/-- **Uniqueness on `[0, ∞)`.** For an input continuous on `[0, ∞)`, every solution on `[0, ∞)` is
the variation-of-constants curve of its initial state. -/
theorem IsSolutionOn.eq_Ici (hx : S.IsSolutionOn u x (Ici 0)) (hu : ContinuousOn u (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    x t = exp (t • S.A) *ᵥ x 0 + ∫ s in 0..t, exp ((t - s) • S.A) *ᵥ (S.B *ᵥ u s) :=
  (hx.mono Icc_subset_Ici_self).eq_Icc (T := t) (hu.mono Icc_subset_Ici_self) ⟨ht, le_rfl⟩

/-! ### The output: feedthrough and convolution -/

variable [Fintype p]

/-- **Output formula.** For an input continuous on `[0, T]`, every solution on `[0, T]` has output
`y t = C x t + D u t = C *ᵥ (exp (t • A) *ᵥ x 0) + D *ᵥ u t + ∫ s in 0..t, h (t - s) *ᵥ u s`
for `t ∈ [0, T]`, where `h` is the response kernel. The first term is the zero-input response of
the initial state; the other two are the zero-state response, with the direct feedthrough `D u`
kept separate from the convolution with `h`. -/
theorem IsSolutionOn.output_eq {T : ℝ} (hx : S.IsSolutionOn u x (Icc 0 T))
    (hu : ContinuousOn u (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    S.C *ᵥ x t + S.D *ᵥ u t = S.C *ᵥ (exp (t • S.A) *ᵥ x 0) + S.D *ᵥ u t +
      ∫ s in 0..t, S.responseKernel (t - s) *ᵥ u s := by
  have hint := intervalIntegrable_exp_smul_mulVec S.A ht.1 <|
    (((continuous_const (y := S.B)).matrix_mulVec continuous_id).comp_continuousOn hu).mono
      (Icc_subset_Icc_right ht.2)
  rw [hx.eq_Icc hu ht, mulVec_add, add_right_comm]
  congr 1
  simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Function.comp_apply,
    id, responseKernel_eq, ← mulVec_mulVec] using
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' S.C)).intervalIntegral_comp_comm hint).symm

/-- **Output formula on `[0, ∞)`.** For an input continuous on `[0, ∞)`, every solution on
`[0, ∞)` has output
`y t = C *ᵥ (exp (t • A) *ᵥ x 0) + D *ᵥ u t + ∫ s in 0..t, h (t - s) *ᵥ u s` for `t ≥ 0`. -/
theorem IsSolutionOn.output_eq_Ici (hx : S.IsSolutionOn u x (Ici 0))
    (hu : ContinuousOn u (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    S.C *ᵥ x t + S.D *ᵥ u t = S.C *ᵥ (exp (t • S.A) *ᵥ x 0) + S.D *ᵥ u t +
      ∫ s in 0..t, S.responseKernel (t - s) *ᵥ u s :=
  (hx.mono Icc_subset_Ici_self).output_eq (T := t) (hu.mono Icc_subset_Ici_self) ⟨ht, le_rfl⟩

/-- **The impulse-response theorem for `D = 0`.** With no direct feedthrough and zero initial
state, the output of every solution on `[0, ∞)` driven by an input continuous on `[0, ∞)` is the
convolution over `ℝ` of the causal kernel `(Set.Ici 0).indicator h` with the causal input
`(Set.Ici 0).indicator u`: `y t = ∫ s, h⁺ (t - s) *ᵥ u⁺ s` for `t ≥ 0`. -/
theorem IsSolutionOn.output_eq_integral_indicator (hx : S.IsSolutionOn u x (Ici 0))
    (hu : ContinuousOn u (Ici 0)) (hx₀ : x 0 = 0) (hD : S.D = 0) {t : ℝ} (ht : 0 ≤ t) :
    S.C *ᵥ x t + S.D *ᵥ u t =
      ∫ s, (Ici 0).indicator S.responseKernel (t - s) *ᵥ (Ici 0).indicator u s := by
  rw [hx.output_eq_Ici hu ht, hx₀, hD, mulVec_zero, mulVec_zero, zero_mulVec, add_zero, zero_add]
  have h : (fun s => (Ici 0).indicator S.responseKernel (t - s) *ᵥ (Ici 0).indicator u s) =
      (Icc 0 t).indicator fun s => S.responseKernel (t - s) *ᵥ u s := by
    funext s
    simp only [indicator_apply, mem_Ici, mem_Icc, sub_nonneg]
    split_ifs <;> simp_all
  rw [h, integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le ht,
    integral_Icc_eq_integral_Ioc]

/-! ### Impulses and certified closed forms -/

omit [Fintype p] in
/-- **State-jump semantics of an impulse.** An impulse `v δ₀` moves the state from `0` to
`B *ᵥ v`. The unforced solution from that state has output `C *ᵥ x t = h t *ᵥ v` for `t ≥ 0`.
This also certifies a closed form of `h t *ᵥ v` from a state curve `x`. -/
theorem responseKernel_mulVec_eq (hx : S.IsSolutionOn 0 x (Ici 0)) {v : m → ℝ}
    (hx₀ : x 0 = S.B *ᵥ v) {t : ℝ} (ht : 0 ≤ t) : S.responseKernel t *ᵥ v = S.C *ᵥ x t := by
  have hx' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (S.A *ᵥ x t) (Ici 0) t := fun t ht => by
    simpa using hx t ht
  rw [eq_exp_smul_mulVec_of_hasDerivWithinAt hx' ht, hx₀, responseKernel_eq]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

end LTISystem
