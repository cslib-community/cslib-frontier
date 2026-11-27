/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, with `Mathlib/Analysis/ODE/ImpulseBounds.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.ImpulseBounds
public import CslibFrontier.Foundations.MeasureTheory.Integral.ConvolutionWindow

/-!
# Inter-pulse contamination of a measurement window

**The question.** A pulse drives a linear channel, and some time later a gated or integrating
readout integrates the channel output over a window. How much of the reading can still be the
tail of the earlier pulse? For a single-input, single-output LTI system `ẋ = A x + B u`,
`y = C x` (no direct feedthrough) at rest before the pulse, the answer here is a bound on the
window integral of the output in terms of the pulse's `L¹` norm and the energy left in the tail
of the impulse response:

`|∫_{a+T}^{a+T+W} y| ≤ ∫_{a+T}^{a+T+W} |y| ≤ ‖p‖₁ √(W E_T)`,

where the pulse `p` ends at time `a`, the window opens `T ≥ 0` after it and has length `W ≥ 0`,
and `∫_T^∞ h² ≤ E_T` for the impulse response `h t = C exp (t A) B`
(`LTISystem.window_integral_bounds_of_tail`). Kernel-checked decay certificates give `E_T` as a
rational number (`Cslib.LinearAlgebra.DecayInequalities.sq_window_integral_le_of_tailBelow`), so
the squared bound `(∫ y)² ≤ ‖p‖₁² W E_T` is a rational inequality.

**Model and assumptions.**

* The channel is the LTI model `S` with input and output index `Fin 1`; the bound concerns the
  response kernel `h = C exp (t A) B` only, so the full impulse response is `h` exactly when
  `S.D = 0` (strictly proper), which the certificates check. A system with `D ≠ 0` passes the
  pulse straight through, and its window output also contains `D p`, which this bound ignores.
* The output is the zero-state response `y t = ∫ s, h⁺ (t - s) * p s`, with the causal kernel
  `h⁺ = (Set.Ici 0).indicator h`: the state is zero before the pulse arrives, and there are no
  other inputs. For an input continuous on `[0, ∞)`, this is the output of every solution of
  the state equation with `x 0 = 0`, by `LTISystem.IsSolutionOn.output_eq_integral_indicator`;
  for a pulse with jumps, such as a rectangular pulse, it is the usual (Carathéodory) zero-state
  response, which the ODE layer does not formalize as a solution.
* `p` is integrable and `p s = 0` for `s > a`. No sign, smoothness or bounded support to the
  left is required.
* The model is a mathematical idealization: noise, nonlinearity, and coupling not represented
  in `(A, B, C)` are outside its scope.
-/

public section

open Set MeasureTheory Matrix NormedSpace

namespace LTISystem

variable {n : Type*} [Fintype n] [DecidableEq n] {S : LTISystem n (Fin 1) (Fin 1)}

/-- The causal scalar kernel `(Set.Ici 0).indicator h` of a SISO system is a.e. strongly
measurable, since `h` is continuous on `[0, ∞)`. -/
private theorem aestronglyMeasurable_indicator_responseKernel :
    AEStronglyMeasurable (fun t => (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) t) := by
  have he : ∀ t : ℝ, S.responseKernel t 0 0 =
      (S.C *ᵥ (exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single 0 1))) 0 := fun t => by
    rw [mulVec_mulVec, mulVec_mulVec, ← responseKernel_eq, mulVec_single_one, col_apply]
  have hx : ContinuousOn (fun t : ℝ => exp (t • S.A) *ᵥ (S.B *ᵥ Pi.single 0 1)) (Ici 0) :=
    fun (t : ℝ) ht => (Matrix.hasDerivWithinAt_exp_smul_mulVec S.A _ t ht).continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ => S.responseKernel t 0 0) (Ici 0) :=
    ((continuous_apply 0).comp_continuousOn
      ((continuous_const.matrix_mulVec continuous_id).comp_continuousOn hx)).congr
      fun t _ => he t
  exact (aestronglyMeasurable_indicator_iff measurableSet_Ici).2
    (hc.aestronglyMeasurable measurableSet_Ici)

/-- **Inter-pulse contamination bound.** Let `S` be a single-input, single-output system whose
response kernel has finite tail energy `∫_T^∞ ‖h t‖_F² ≤ E` for some `T ≥ 0` (for a SISO system
`‖h t‖_F² = h t ²`). Let the input `p` be integrable and vanish after time `a`, and let
`y t = ∫ s, h⁺ (t - s) * p s` be the zero-state output, with `h⁺ = (Set.Ici 0).indicator h`.
Then for every window `[a + T, a + T + W]` with `W ≥ 0`, `y` is integrable on the window, and
`∫_{a+T}^{a+T+W} |y| ≤ ‖p‖₁ √(W E)` and `|∫_{a+T}^{a+T+W} y| ≤ ‖p‖₁ √(W E)`, where
`‖p‖₁ = ∫ s, |p s|`. The output `y` is the zero-state response; with `S.D = 0` it is the whole
output (see the module docstring for the modelling assumptions). -/
theorem window_integral_bounds_of_tail {p : ℝ → ℝ} {a T W E : ℝ} (hT : 0 ≤ T)
    (htail : IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T))
    (hE : ∫ t in Ioi T, ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤ E)
    (hp : Integrable p) (hpa : ∀ s, a < s → p s = 0) (hW : 0 ≤ W) :
    IntervalIntegrable (fun t => ∫ s, (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) (t - s) *
        p s) volume (a + T) (a + T + W) ∧
      ∫ t in (a + T)..(a + T + W),
          |∫ s, (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) (t - s) * p s| ≤
        (∫ s, |p s|) * √(W * E) ∧
      |∫ t in (a + T)..(a + T + W),
          ∫ s, (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) (t - s) * p s| ≤
        (∫ s, |p s|) * √(W * E) := by
  have hk : EqOn (fun t => (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) t ^ 2)
      (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T) := fun t ht => by
    dsimp only
    rw [indicator_of_mem (mem_Ici.2 (hT.trans (le_of_lt ht)))]
    simp
  have hg2 := htail.congr_fun hk.symm measurableSet_Ioi
  have hE' : ∫ t in Ioi T, (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) t ^ 2 ≤ E := by
    rwa [setIntegral_congr_fun measurableSet_Ioi hk]
  have hm := aestronglyMeasurable_indicator_responseKernel (S := S)
  exact ⟨(intervalIntegrable_and_integral_abs_le_of_tail hm hg2 hE' hp hpa hW).1,
    (intervalIntegrable_and_integral_abs_le_of_tail hm hg2 hE' hp hpa hW).2,
    abs_integral_le_of_tail hm hg2 hE' hp hpa hW⟩

end LTISystem
