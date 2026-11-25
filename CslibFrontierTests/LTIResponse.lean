/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of LTI forced and impulse responses)

import CslibFrontier.Foundations.Analysis.ODE.StateSpace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for forced responses and impulse responses of LTI systems

A `module` client with ordinary imports: `StateSpace` is the only import from the ODE layer, and
the Mathlib `HasDerivAt` rules used by the closed forms are imported explicitly. The kernel is
reached only through public statements, among them its defining equation
`LTISystem.responseKernel_eq`.

Every closed form below is certified by `LTISystem.responseKernel_eq_of_hasDerivWithinAt`: the
proposed state curve `X` is checked against `X 0 = B` and `X' = A * X` with ordinary derivatives;
no matrix exponential is computed.

* Scalar systems `ẋ = a x + b u`, `y = c x + d u` on `Fin 1`: the kernel is `c b exp (a t)`.
  - The first deliverable of #8321, `ẋ = -x + u`, `x 0 = 0`, `y = x`:
    `y t = ∫ s in 0..t, exp (-(t - s)) • u s` for every continuous input.
  - The RC circuit, `τ = R C > 0`: `h t = τ⁻¹ exp (-t / τ)`.
  - The unstable system `A = B = C = 1`: `h t = exp t`. Existence of the response is not a
    stability claim.
  - Nonzero feedthrough `d = 2`: `y t = 2 u t + ∫ s in 0..t, exp (-(t - s)) • u s`.
* The defining equation `h t = C * exp (t • A) * B`, for every `t`, including `t < 0`.
* A two-input, one-output system (`m = Fin 2`, `p = Fin 1`) with `A = diag (-1, -2)`, `B = 1`,
  `C = (1, 1)`: `h t = (exp (-t), exp (-2 t))`, a two-column closed form.
* The repeated pole `A = !![-1, 1; 0, -1]`, `B = (0, 1)ᵀ`, `C = (1, 0)`: `h t = t exp (-t)`, a
  non-diagonalizable client.
* A damped series-RLC-type system `A = !![0, 1; -2, -2]`, `B = (0, 1)ᵀ`, `C = (1, 0)`:
  `h t = exp (-t) sin t`; the wrong candidate `t exp (-t)` (which has the correct initial value
  `C B = 0`) is rejected.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LTIResponse

open Set NormedSpace Matrix LTISystem

/-! ### Scalar systems -/

/-- The scalar system `ẋ = a x + b u`, `y = c x + d u`. -/
abbrev scalar (a b c d : ℝ) : LTISystem (Fin 1) (Fin 1) (Fin 1) := ⟨!![a], !![b], !![c], !![d]⟩

theorem responseKernel_scalar (a b c d : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (scalar a b c d).responseKernel t = !![c * (b * Real.exp (a * t))] := by
  rw [responseKernel_eq_of_hasDerivWithinAt (X := fun τ => !![b * Real.exp (a * τ)]) _ _ ht]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]
  · intro j τ _
    fin_cases j
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    fin_cases k
    have h := (((hasDerivAt_id τ).const_mul a).exp).const_mul b
    simp only [id, mul_one] at h
    convert h using 1
    · funext σ
      simp
    · simp [mulVec, dotProduct]
      ring
  · ext i j
    fin_cases i
    fin_cases j
    simp

theorem mulVec_one_by_one (c : ℝ) (v : Fin 1 → ℝ) : !![c] *ᵥ v = c • v := by
  ext i
  fin_cases i
  simp [mulVec, dotProduct]

/-- The zero-state output of a scalar system, for every input continuous on `[0, ∞)`:
`y t = d u t + ∫ s in 0..t, c b exp (a (t - s)) u s`. -/
theorem output_scalar {a b c d : ℝ} {u : ℝ → Fin 1 → ℝ} {x : ℝ → Fin 1 → ℝ}
    (hu : ContinuousOn u (Ici 0)) (hx : (scalar a b c d).IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (scalar a b c d).C *ᵥ x t + (scalar a b c d).D *ᵥ u t =
      d • u t + ∫ s in 0..t, (c * (b * Real.exp (a * (t - s)))) • u s := by
  rw [hx.output_eq_Ici hu ht, hx₀, mulVec_zero, mulVec_zero, zero_add, mulVec_one_by_one]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [responseKernel_scalar _ _ _ _ (sub_nonneg.2 hs.2), mulVec_one_by_one]

/-- **The first deliverable of #8321.** For `ẋ = -x + u`, `x 0 = 0`, `y = x`, and every input
continuous on `[0, ∞)`, every solution has output `y t = ∫ s in 0..t, exp (-(t - s)) • u s`. -/
theorem first_deliverable {u : ℝ → Fin 1 → ℝ} {x : ℝ → Fin 1 → ℝ}
    (hu : ContinuousOn u (Ici 0)) (hx : (scalar (-1) 1 1 0).IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (scalar (-1) 1 1 0).C *ᵥ x t + (scalar (-1) 1 1 0).D *ᵥ u t =
      ∫ s in 0..t, Real.exp (-(t - s)) • u s := by
  rw [output_scalar hu hx hx₀ ht]
  simp

/-- Such solutions exist: the variation-of-constants curve from `0`. -/
example {u : ℝ → Fin 1 → ℝ} (hu : ContinuousOn u (Ici 0)) :
    (scalar (-1) 1 1 0).IsSolutionOn u
      (fun t => exp (t • !![-1]) *ᵥ 0 + ∫ s in 0..t, exp ((t - s) • !![-1]) *ᵥ (!![1] *ᵥ u s))
      (Ici 0) :=
  (scalar (-1) 1 1 0).isSolutionOn_Ici 0 hu

/-- The same output as a convolution over `ℝ` of the causal kernel with the causal input
(`D = 0`). -/
example {u : ℝ → Fin 1 → ℝ} {x : ℝ → Fin 1 → ℝ}
    (hu : ContinuousOn u (Ici 0)) (hx : (scalar (-1) 1 1 0).IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (scalar (-1) 1 1 0).C *ᵥ x t + (scalar (-1) 1 1 0).D *ᵥ u t = ∫ s,
      (Ici 0).indicator (scalar (-1) 1 1 0).responseKernel (t - s) *ᵥ (Ici 0).indicator u s :=
  hx.output_eq_integral_indicator hu hx₀ (by ext i j; fin_cases i; fin_cases j; rfl) ht

/-- **Nonzero feedthrough.** For `ẋ = -x + u`, `y = x + 2 u` the direct term `2 u t` is kept
separate from the convolution. -/
example {u : ℝ → Fin 1 → ℝ} {x : ℝ → Fin 1 → ℝ}
    (hu : ContinuousOn u (Ici 0)) (hx : (scalar (-1) 1 1 2).IsSolutionOn u x (Ici 0))
    (hx₀ : x 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (scalar (-1) 1 1 2).C *ᵥ x t + (scalar (-1) 1 1 2).D *ᵥ u t =
      (2 : ℝ) • u t + ∫ s in 0..t, Real.exp (-(t - s)) • u s := by
  rw [output_scalar hu hx hx₀ ht]
  simp

/-- **The RC circuit.** For `τ = R C > 0`, `A = -1/τ`, `B = 1/τ`, `C = 1`, `D = 0`:
`h t = τ⁻¹ exp (-t / τ)` for `t ≥ 0`. -/
example {τ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    (scalar (-1 / τ) (1 / τ) 1 0).responseKernel t = !![τ⁻¹ * Real.exp (-t / τ)] := by
  rw [responseKernel_scalar _ _ _ _ ht, show -1 / τ * t = -t / τ by ring]
  simp

/-- **An unstable system.** For `A = B = C = 1`, `D = 0`: `h t = exp t`. -/
example {t : ℝ} (ht : 0 ≤ t) : (scalar 1 1 1 0).responseKernel t = !![Real.exp t] := by
  simp [responseKernel_scalar _ _ _ _ ht]

/-- **State-jump semantics of an impulse.** For `A = B = C = 1`, the impulse `v δ₀` moves the
state to `v`; the unforced solution `x t = exp t • v` from there has output `h t *ᵥ v`. -/
example (v : Fin 1 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (scalar 1 1 1 0).responseKernel t *ᵥ v = Real.exp t • v := by
  refine (responseKernel_mulVec_eq (x := fun τ => Real.exp τ • v) (fun τ _ => ?_) ?_ ht).trans ?_
  · refine ((Real.hasDerivAt_exp τ).smul_const v |>.congr_deriv ?_).hasDerivWithinAt
    simp only [Pi.zero_apply, mulVec_zero, add_zero, mulVec_one_by_one, one_smul]
  · simp only [Real.exp_zero, one_smul, mulVec_one_by_one]
  · simp only [mulVec_one_by_one, one_smul]

/-! ### The defining equation -/

/-- The defining equation is available to clients for every `t`, not only `t ≥ 0`. -/
example (S : LTISystem (Fin 2) (Fin 1) (Fin 1)) (v : Fin 1 → ℝ) :
    S.responseKernel (-1) *ᵥ v = S.C *ᵥ (exp ((-1 : ℝ) • S.A) *ᵥ (S.B *ᵥ v)) := by
  rw [responseKernel_eq, mulVec_mulVec, mulVec_mulVec]

/-- With `A = 0` the kernel is the constant `C * B`, at every time. -/
example (b c d t : ℝ) : (scalar 0 b c d).responseKernel t = !![c * b] := by
  have hA : t • (scalar 0 b c d).A = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [responseKernel_eq, hA, exp_zero, Matrix.mul_one]
  ext i j
  fin_cases i
  fin_cases j
  simp

/-! ### Two inputs, one output -/

/-- A two-input, one-output system: two decoupled modes `-1` and `-2`, each driven by its own
input, summed at the output. -/
abbrev twoInput : LTISystem (Fin 2) (Fin 2) (Fin 1) := ⟨!![-1, 0; 0, -2], 1, !![1, 1], 0⟩

/-- `h t = (exp (-t), exp (-2 t))` for `twoInput`, certified from the two-column curve
`X t = diag (exp (-t), exp (-2 t))`. -/
theorem responseKernel_twoInput {t : ℝ} (ht : 0 ≤ t) :
    twoInput.responseKernel t = !![Real.exp (-t), Real.exp (-(2 * t))] := by
  rw [responseKernel_eq_of_hasDerivWithinAt
    (X := fun τ => !![Real.exp (-τ), 0; 0, Real.exp (-(2 * τ))]) _ _ ht]
  · ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro j τ _
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    have h1 := (hasDerivAt_neg τ).exp
    have h2 := ((hasDerivAt_id τ).const_mul 2).neg.exp
    fin_cases j <;> fin_cases k
    · convert h1 using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
    · convert hasDerivAt_const τ (0 : ℝ) using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
    · convert hasDerivAt_const τ (0 : ℝ) using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
    · convert h2 using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
        ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ### A repeated pole -/

/-- The repeated-pole client: a Jordan block with eigenvalue `-1`, `B = (0, 1)ᵀ`, `C = (1, 0)`,
`D = 0`. -/
abbrev repeatedPole : LTISystem (Fin 2) (Fin 1) (Fin 1) :=
  ⟨!![-1, 1; 0, -1], !![0; 1], !![1, 0], 0⟩

/-- `h t = t exp (-t)` for the non-diagonalizable `repeatedPole`. -/
theorem responseKernel_repeatedPole {t : ℝ} (ht : 0 ≤ t) :
    repeatedPole.responseKernel t = !![t * Real.exp (-t)] := by
  rw [responseKernel_eq_of_hasDerivWithinAt
    (X := fun τ => !![τ * Real.exp (-τ); Real.exp (-τ)]) _ _ ht]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro j τ _
    fin_cases j
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    have he := (hasDerivAt_neg τ).exp
    fin_cases k
    · convert (hasDerivAt_id τ).mul he using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
        ring
    · convert he using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ### A damped second-order system, and a rejected candidate -/

/-- A damped series-RLC-type system `ẍ + 2 ẋ + 2 x = u`, `y = x`, in state-space form. -/
abbrev rlc : LTISystem (Fin 2) (Fin 1) (Fin 1) := ⟨!![0, 1; -2, -2], !![0; 1], !![1, 0], 0⟩

/-- `h t = exp (-t) sin t` for `rlc`, a polynomial-exponential-trigonometric closed form. -/
theorem responseKernel_rlc {t : ℝ} (ht : 0 ≤ t) :
    rlc.responseKernel t = !![Real.exp (-t) * Real.sin t] := by
  rw [responseKernel_eq_of_hasDerivWithinAt (X := fun τ =>
    !![Real.exp (-τ) * Real.sin τ; Real.exp (-τ) * (Real.cos τ - Real.sin τ)]) _ _ ht]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro j τ _
    fin_cases j
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    have he := (hasDerivAt_neg τ).exp
    fin_cases k
    · convert he.mul (Real.hasDerivAt_sin τ) using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
        ring
    · convert he.mul ((Real.hasDerivAt_cos τ).sub (Real.hasDerivAt_sin τ)) using 1
      · funext σ
        simp
      · simp [mulVec, dotProduct, Fin.sum_univ_two]
        ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- **A rejected candidate.** The proposal `t exp (-t)` has the right initial value
`h 0 = C B = 0` but is not the response kernel of `rlc`: at `t = 1` the certified value is
`exp (-1) sin 1 < exp (-1)`. -/
example : ¬ ∀ t ≥ 0, rlc.responseKernel t = !![t * Real.exp (-t)] := by
  intro h
  have h1 := (responseKernel_rlc zero_le_one).symm.trans (h 1 zero_le_one)
  replace h1 := congrFun (congrFun h1 0) 0
  simp only [of_apply, cons_val', empty_val', cons_val_fin_one, one_mul] at h1
  nlinarith [Real.sin_lt one_pos, Real.exp_pos (-1)]

end CslibFrontierTests.LTIResponse
