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
  other inputs. The ODE layer connects this to solutions of the state equation only for an
  input that starts at time `0`: if `S.D = 0`, `u` is continuous on `[0, ∞)`, and `x` solves the
  state equation on `[0, ∞)` with `x 0 = 0`, then for `t ≥ 0` the output `C x t` is this
  convolution with `p` the causal extension `(Set.Ici 0).indicator u` of the input
  (`LTISystem.IsSolutionOn.output_eq_integral_indicator`). The bound below allows any `p`, but
  for a `p` that is nonzero before time `0` the convolution also contains the response to that
  history, which a solution started from `x 0 = 0` does not see. For a pulse with jumps, such
  as a rectangular pulse, the convolution is the usual (Carathéodory) zero-state response, which
  the ODE layer does not formalize as a solution.
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
measurable, since `h` is continuous (`LTISystem.continuous_responseKernel_apply`). -/
private theorem aestronglyMeasurable_indicator_responseKernel :
    AEStronglyMeasurable (fun t => (Ici 0).indicator (fun τ => S.responseKernel τ 0 0) t) :=
  (aestronglyMeasurable_indicator_iff measurableSet_Ici).2
    (S.continuous_responseKernel_apply 0 0).aestronglyMeasurable.restrict

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
  have h := intervalIntegrable_and_integral_abs_le_of_tail
    (aestronglyMeasurable_indicator_responseKernel (S := S)) hg2 hE' hp hpa hW
  exact ⟨h.1, h.2, (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans h.2⟩

end LTISystem
