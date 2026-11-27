/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of the LTI impulse-response certificates)

import CslibFrontier.Algorithms.LinearAlgebra.ImpulseCertificate

/-! # Tests for energy and decay certificates of LTI impulse responses

A `module` client with ordinary imports: the checkers are evaluated through their exposed bodies
and the soundness theorems are used through their public statements. Every acceptance and
rejection is closed by `decide +kernel`. The clients are those of #8322:

* the scalar system `A = -1`, `B = C = 1`, `D = 0`: the exact energy `1/2` (with integrability),
  the inexact upper-bound certificate `W = 1`, decay with `P = 1`, `α = β = γ = 1`, the energy
  tail and the numerical tail after `T = 2`, and settling below `1/10` after `T = 5/2`, certified
  by Taylor lower bounds for `exp`;
  overclaimed rates, energies, bounds and settling times, negative squared radii, a
  sign-corrupted model and a model with direct feedthrough are rejected;
* an RC circuit with `τ = 1/1000 s`: energy `500 s⁻¹` and decay at rate `1000 s⁻¹`, and the
  contamination of a gated reading over `[3 ms, 4 ms]` by a `1 ms` rectangular pulse ending at
  `0`, from the certified tail `∫_{3 ms}^∞ h² ≤ 5/4 s⁻¹` (#7465);
* the repeated-pole client of #8321, `h t = t exp (-t)`: energy `1/4` and decay at rate `1/2`;
  its initial output `h 0` vanishes;
* the damped RLC-type client of #8321, `h t = exp (-t) sin t`: energy `1/8`;
* a stable unobservable model with singular Gramian `diag (1/2, 0)`;
* energy lower bounds: `Q = 1/4` certifies `1/4` for the scalar client, the exact Gramian encloses
  the energy in `[1/2, 1/2]`, and a lower-bound certificate for the unstable `A = 1` is rejected
  by its stability part, although its `Q = 10` passes the semidefiniteness check;
* `A = diag (1, -1)` with unobservable unstable mode: an energy upper bound is accepted, and no
  Lyapunov certificate exists, so no internal-stability verdict follows.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ImpulseCertificate

open Set Matrix MeasureTheory Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### The scalar client `A = -1`, `B = C = 1`, `D = 0` -/

/-- `ẋ = -x + u`, `y = x`. -/
def scalar : RatLTI 1 1 1 := ⟨[[-1]], [[1]], [[1]], [[0]]⟩

/-- The `1 × 1` witness of the zero matrix. -/
def zero₁ : LDLCert := ⟨[[1]], [0]⟩

/-- `P = 1`, `α = β = γ = 1`, `lo = hi = 1`: every residual is `0`. -/
def scalarDecay : DecayCert := ⟨⟨1, 1, 1, 1, 1⟩, [[1]], zero₁, zero₁, zero₁, zero₁, zero₁⟩

theorem scalarDecay_ok : scalarDecay.check scalar = true := by decide +kernel

/-- Overclaiming the rate `α = 2` is rejected. -/
example : ({ scalarDecay with α := 2 } : DecayCert).check scalar = false := by decide +kernel

/-- The sign-corrupted unstable model `A = 1` is rejected. -/
example : scalarDecay.check (⟨[[1]], [[1]], [[1]], [[0]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

/-- A model with direct feedthrough `D = 1` is rejected. -/
example : scalarDecay.check (⟨[[-1]], [[1]], [[1]], [[1]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

/-- Settling: for `‖v‖₂ ≤ 1`, `‖h t v‖₂ ≤ 1/10` for `t ≥ 5/2`, since
`expLower 12 5 ≥ 100`, a certified lower bound for `exp 5`. -/
theorem scalar_settles : scalarDecay.impulseSettles 1 (1/100) (5/2) 12 = true := by
  decide +kernel

example {v : Fin 1 → ℝ} (hv : v ⬝ᵥ v ≤ 1) {t : ℝ} (ht : 5 / 2 ≤ t) :
    scalar.toSystem.responseKernel t *ᵥ v ⬝ᵥ scalar.toSystem.responseKernel t *ᵥ v ≤ 1/100 := by
  have := (DecayCert.decayInequalities scalarDecay_ok).responseKernel_mulVec_sq_le_of_impulseSettles
    scalar_settles
    (v := v) (t := t) (by exact_mod_cast hv) (by norm_num; linarith)
  norm_num at this
  exact this

/-- The same claim at `T = 2`, where `exp 4 < 100`, is rejected. -/
example : scalarDecay.impulseSettles 1 (1/100) 2 12 = false := by decide +kernel

/-- A negative squared input radius is rejected: it would make the hypothesis `‖v‖₂² ≤ vmax2`
unsatisfiable. -/
example : scalarDecay.impulseSettles (-1) 1 0 1 = false := by decide +kernel

/-- State settling: for `‖x 0‖₂ ≤ 1`, `‖x t‖₂ ≤ 1/10` for `t ≥ 5/2`. -/
theorem scalar_stateSettles : scalarDecay.stateSettles 1 (1/100) (5/2) 12 = true := by
  decide +kernel

example {x : ℝ → Fin 1 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (scalar.toSystem.A *ᵥ x t) (Ici 0) t)
    (h0 : x 0 ⬝ᵥ x 0 ≤ 1) {t : ℝ} (ht : 5 / 2 ≤ t) : x t ⬝ᵥ x t ≤ 1/100 := by
  have := (DecayCert.decayInequalities scalarDecay_ok).dotProduct_self_le_of_stateSettles
    scalar_stateSettles hx
    (by exact_mod_cast h0) (t := t) (by norm_num; linarith)
  norm_num at this
  exact this

/-- A negative squared initial-state radius is rejected. -/
example : scalarDecay.stateSettles (-1) 1 0 1 = false := by decide +kernel

/-- The decay certificate also proves internal stability. -/
example : (toEuclideanCLM (𝕜 := ℝ) scalar.toSystem.A).IsExponentiallyStable :=
  (DecayCert.decayInequalities scalarDecay_ok).isExponentiallyStable

/-- `h t ² ≤ exp (-2 t)` for `‖v‖₂ = 1`; here `h t = exp (-t)` and the envelope is attained. -/
example (v : Fin 1 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    scalar.toSystem.responseKernel t *ᵥ v ⬝ᵥ scalar.toSystem.responseKernel t *ᵥ v ≤
      Real.exp (-2 * t) * (v ⬝ᵥ v) := by
  simpa [scalarDecay] using
    (DecayCert.decayInequalities scalarDecay_ok).responseKernel_mulVec_sq_le v ht

/-- The first deliverable of #8322: the Gramian `W = 1/2` solves `Aᵀ W + W A + Cᵀ C = 0` exactly,
`P = 1/2` proves stability (`-(Aᵀ P + P A) = 1`), and the energy is `tr (Bᵀ W B) = 1/2`. -/
def scalarEnergy : EnergyCert := ⟨[[1/2]], ⟨⟨[[1]], [1/2]⟩, ⟨[[1]], [1]⟩⟩, [[1/2]], 1/2⟩

theorem scalarEnergy_ok : scalarEnergy.check scalar = true := by decide +kernel

/-- `∫₀^∞ h(t)² dt = 1/2` for `h t = exp (-t)`, with integrability. -/
example : IntegrableOn (fun t => scalar.toSystem.responseKernel t 0 0 ^ 2) (Ioi 0) ∧
    ∫ t in Ioi 0, scalar.toSystem.responseKernel t 0 0 ^ 2 = 1/2 := by
  simpa [scalarEnergy] using EnergyCert.integrableOn_Ioi_and_integral_eq scalarEnergy_ok

/-- A wrong energy, and a wrong Gramian, are rejected. -/
example : ({ scalarEnergy with energy := 1/4 } : EnergyCert).check scalar = false := by
  decide +kernel

example : ({ scalarEnergy with W := [[1]], energy := 1 } : EnergyCert).check scalar = false := by
  decide +kernel

/-- `W = 1` is a valid upper-bound certificate whose Gramian equation is not exact:
`-(Aᵀ W + W A + Cᵀ C) = 1 ⪰ 0`, so `∫₀^∞ h(t)² dt ≤ 1`. -/
def scalarBound : EnergyBoundCert := ⟨[[1]], ⟨[[1]], [1]⟩, ⟨[[1]], [1]⟩, 1⟩

theorem scalarBound_ok : scalarBound.check scalar = true := by decide +kernel

example : ∫ t in Ioi 0, scalar.toSystem.responseKernel t 0 0 ^ 2 ≤ 1 := by
  simpa [scalarBound] using (EnergyBoundCert.integrableOn_Ioi_and_integral_le scalarBound_ok).2

/-- Claiming the bound `1/2` from `W = 1` is rejected: the certified bound is `tr (Bᵀ W B) = 1`. -/
example : ({ scalarBound with bound := 1/2 } : EnergyBoundCert).check scalar = false := by
  decide +kernel

/-- `Q = 1/4` gives `Aᵀ Q + Q A + Cᵀ C = 1/2 ⪰ 0`, and `P = 1/2` proves stability: the energy is
at least `tr (Bᵀ Q B) = 1/4`. -/
def scalarLower : EnergyLowerCert :=
  ⟨[[1/2]], ⟨⟨[[1]], [1/2]⟩, ⟨[[1]], [1]⟩⟩, [[1/4]], ⟨[[1]], [1/2]⟩, 1/4⟩

theorem scalarLower_ok : scalarLower.check scalar = true := by decide +kernel

example : 1/4 ≤ ∫ t in Ioi 0, ∑ i, ∑ j, scalar.toSystem.responseKernel t i j ^ 2 := by
  simpa [scalarLower] using (EnergyLowerCert.integrableOn_Ioi_and_le_integral scalarLower_ok).2

/-- Claiming more than `tr (Bᵀ Q B) = 1/4` from `Q = 1/4` is rejected. -/
example : ({ scalarLower with bound := 1/2 } : EnergyLowerCert).check scalar = false := by
  decide +kernel

/-- The exact Gramian `1/2` as `Q` and as `W` encloses the energy in `[1/2, 1/2]`. -/
example : ∫ t in Ioi 0, ∑ i, ∑ j, scalar.toSystem.responseKernel t i j ^ 2 ∈
    Icc (1/2 : ℝ) (1/2) := by
  have hl : (⟨[[1/2]], ⟨⟨[[1]], [1/2]⟩, ⟨[[1]], [1]⟩⟩, [[1/2]], zero₁, 1/2⟩ :
      EnergyLowerCert).check scalar = true := by
    decide +kernel
  have hu : (⟨[[1/2]], ⟨[[1]], [1/2]⟩, zero₁, 1/2⟩ : EnergyBoundCert).check scalar = true := by
    decide +kernel
  simpa using (EnergyLowerCert.integrableOn_Ioi_and_integral_mem_Icc hl hu).2

/-- The stability part is needed. For the unstable `A = 1`, `Q = 10` satisfies
`Aᵀ Q + Q A + Cᵀ C = 21 ⪰ 0` although the energy is infinite; the certificate is rejected because
its Lyapunov certificate is. -/
example : (⟨[[1/2]], ⟨⟨[[1]], [1/2]⟩, ⟨[[1]], [1]⟩⟩, [[10]], ⟨[[1]], [21]⟩, 10⟩ :
    EnergyLowerCert).check (⟨[[1]], [[1]], [[1]], [[0]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

example : (⟨[[1]], [21]⟩ : LDLCert).checkPosSemidef 1
    (rowsLin 1 1 1 (rowsGram 1 1 [[1]]) (lyapunovResidual 1 [[1]] [[10]])) = true := by
  decide +kernel

/-- A model with direct feedthrough gets no impulse-energy certificate. -/
example : scalarEnergy.check (⟨[[-1]], [[1]], [[1]], [[1]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

example : scalarBound.check (⟨[[-1]], [[1]], [[1]], [[1]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

/-- The energy tail after `T`: `∫_T^∞ h(t)² dt ≤ exp (-2 T) / 2`. -/
example {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioi T, scalar.toSystem.responseKernel t 0 0 ^ 2 ≤ Real.exp (-2 * T) / 2 := by
  have hD := DecayCert.decayInequalities scalarDecay_ok
  have := (hD.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le hT).2
  have htr : rowsTrace 1 (rowsCongr 1 1 scalar.B [[1]]) = 1 := by decide +kernel
  simpa [htr, scalarDecay] using this

/-- The numerical tail `∫_2^∞ h(t)² dt ≤ 1/100`, from `exp 4 ≥ expLower 12 4 > 50`; the
claim `1/200` is rejected. -/
example : ∫ t in Ioi (2 : ℝ), ∑ i, ∑ j, scalar.toSystem.responseKernel t i j ^ 2 ≤ 1/100 := by
  have h : scalarDecay.tailBelow (rowsTrace 1 (rowsCongr 1 1 scalar.B scalarDecay.P)) (1/100) 2
      12 = true := by
    decide +kernel
  have := (DecayCert.decayInequalities scalarDecay_ok).integral_Ioi_frobeniusSq_le_of_tailBelow h
  norm_num at this ⊢
  exact this

example : scalarDecay.tailBelow (rowsTrace 1 (rowsCongr 1 1 scalar.B scalarDecay.P)) (1/200) 2
    12 = false := by
  decide +kernel

/-! ### An RC circuit

`R = 1 kΩ`, `C = 1 µF`, so `τ = R C = 1/1000 s`; the state is the capacitor voltage, the input
is the source voltage and the output is the capacitor voltage: `A = -1/τ`, `B = 1/τ`, `C = 1`,
`D = 0`. The impulse response `h t = τ⁻¹ exp (-t / τ)` is measured in `s⁻¹` (volts of output per
volt-second of input impulse), and its energy `∫₀^∞ h² = 1 / (2 τ) = 500 s⁻¹`. -/

def rc : RatLTI 1 1 1 := ⟨[[-1000]], [[1000]], [[1]], [[0]]⟩

theorem rc_energy : (⟨[[1/2000]], ⟨⟨[[1]], [1/2000]⟩, ⟨[[1]], [1]⟩⟩, [[1/2000]], 500⟩ :
    EnergyCert).check rc = true := by
  decide +kernel

/-- Decay at rate `α = 1/τ = 1000 s⁻¹` with `P = 1`, `γ = 1` and `β = 10⁶`: the envelope
`h t ² ≤ 10⁶ exp (-2000 t)` is attained. -/
theorem rc_decay : (⟨⟨1000, 1, 1, 1, 1000000⟩, [[1]], zero₁, zero₁, zero₁, zero₁, zero₁⟩ :
    DecayCert).check rc = true := by
  decide +kernel

/-- The decay certificate `rc_decay` as a named value. -/
def rcDecay : DecayCert := ⟨⟨1000, 1, 1, 1, 1000000⟩, [[1]], zero₁, zero₁, zero₁, zero₁, zero₁⟩

/-- The certified tail `∫_{3 ms}^∞ h² ≤ 5/4 s⁻¹`: with `τ = tr (Bᵀ P B) = 10⁶`, the check is
`γ τ / (2 α) = 500 ≤ (5/4) expLower 14 6`, and `expLower 14 6 ≈ 401.96 ≤ exp 6`. -/
theorem rc_tail : rcDecay.tailBelow (rowsTrace 1 (rowsCongr 1 1 rc.B rcDecay.P)) (5/4) (3/1000)
    14 = true := by
  decide +kernel

/-- With one Taylor term fewer, `expLower 13 6 ≈ 399.87 < 400`, the same tail is rejected. -/
example : rcDecay.tailBelow (rowsTrace 1 (rowsCongr 1 1 rc.B rcDecay.P)) (5/4) (3/1000)
    13 = false := by
  decide +kernel

/-- **Inter-pulse contamination for the RC channel.** A rectangular source pulse of height
`v` volts on `[-1 ms, 0]` (so `‖p‖₁ = |v| · 10⁻³ V s`) drives the RC circuit at rest. A gated
readout integrates the capacitor voltage over the window `[3 ms, 4 ms]`. The pulse's
contribution to the reading satisfies `(∫ y)² ≤ v² · 10⁻⁶ · 10⁻³ · 5/4 = v² / (8 · 10⁸)`, i.e.
`|∫ y| ≤ 3.54 · 10⁻⁵ |v| V s`. The exact value is
`v (1 - e⁻¹) (e⁻³ - e⁻⁴) / 1000 ≈ 1.99 · 10⁻⁵ v V s`, so the bound is within a factor `1.8`.
The output is the zero-state convolution with the causal kernel (the pulse is discontinuous, so
it is not an admissible input of the ODE layer). -/
example (v : ℝ) :
    (∫ t in (3/1000 : ℝ)..4/1000,
        ∫ s, (Ici 0).indicator (fun t => rc.toSystem.responseKernel t 0 0) (t - s) *
          (Icc (-(1/1000 : ℝ)) 0).indicator (fun _ => v) s) ^ 2 ≤ v ^ 2 / 800000000 := by
  have hp : Integrable ((Icc (-(1/1000 : ℝ)) 0).indicator fun _ => v) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hpa : ∀ s : ℝ, 0 < s → (Icc (-(1/1000 : ℝ)) 0).indicator (fun _ => v) s = 0 :=
    fun s hs => indicator_of_notMem (fun h => by linarith [h.2]) _
  have hn : ∫ s, |(Icc (-(1/1000 : ℝ)) 0).indicator (fun _ => v) s| = |v| / 1000 := by
    have : (fun s => |(Icc (-(1/1000 : ℝ)) 0).indicator (fun _ => v) s|) =
        (Icc (-(1/1000 : ℝ)) 0).indicator fun _ => |v| := by
      funext s
      by_cases hs : s ∈ Icc (-(1/1000 : ℝ)) 0
      · rw [indicator_of_mem hs, indicator_of_mem hs]
      · rw [indicator_of_notMem hs, indicator_of_notMem hs, abs_zero]
    rw [this, integral_indicator measurableSet_Icc, setIntegral_const]
    simp
    ring
  have := ((DecayCert.decayInequalities rc_decay).sq_window_integral_le_of_tailBelow rc_tail hp
    hpa (by norm_num : (0 : ℝ) ≤ 1/1000)).2
  have hw₁ : ((0 : ℝ) + ((3/1000 : ℚ) : ℝ)) = 3/1000 := by norm_num
  have hw₂ : (3/1000 : ℝ) + 1/1000 = 4/1000 := by norm_num
  rw [hn, hw₁, hw₂] at this
  refine this.trans_eq ?_
  rw [div_pow, sq_abs]
  push_cast
  ring

/-! ### Two-state clients -/

/-- The `2 × 2` witness of the zero matrix. -/
def zero₂ : LDLCert := ⟨[[1], [0, 1]], [0, 0]⟩

/-- The repeated-pole client of #8321: `A = !![-1, 1; 0, -1]`, `B = (0, 1)ᵀ`, `C = (1, 0)`,
with `h t = t exp (-t)`. -/
def repeatedPole : RatLTI 2 1 1 := ⟨[[-1, 1], [0, -1]], [[0], [1]], [[1, 0]], [[0]]⟩

/-- `W = !![1/2, 1/4; 1/4, 1/4]` and energy `1/4`; stability from
`P = !![1/2, 1/4; 1/4, 3/4]` with `-(Aᵀ P + P A) = 1`. -/
theorem repeatedPole_energy : (⟨[[1/2, 1/4], [1/4, 3/4]],
    ⟨⟨[[1], [1/2, 1]], [1/2, 5/8]⟩, ⟨[[1], [0, 1]], [1, 1]⟩⟩,
    [[1/2, 1/4], [1/4, 1/4]], 1/4⟩ : EnergyCert).check repeatedPole = true := by
  decide +kernel

/-- Decay with `P = 1` at the rate `α = 1/2`, `γ = β = 1`: `(t exp (-t))² ≤ exp (-t)`. -/
def repeatedPoleDecay : DecayCert :=
  ⟨⟨1/2, 1, 1, 1, 1⟩, [[1, 0], [0, 1]], ⟨[[1], [-1, 1]], [1, 0]⟩, zero₂, zero₂,
    ⟨[[1], [0, 1]], [0, 1]⟩, zero₁⟩

theorem repeatedPoleDecay_ok : repeatedPoleDecay.check repeatedPole = true := by decide +kernel

/-- The rate `α = 1` is not certified by `P = 1`. -/
example : ({ repeatedPoleDecay with α := 1 } : DecayCert).check repeatedPole = false := by
  decide +kernel

/-- The output vanishes at time `0` (`h 0 = C B = 0`), although the impulse stores energy in the
state: the settling bounds are normalized by the input `‖v‖₂²`, never by the initial output. -/
example : repeatedPole.toSystem.responseKernel 0 = 0 := by
  rw [LTISystem.responseKernel_zero]
  ext i j
  fin_cases i
  fin_cases j
  simp [RatLTI.toSystem, repeatedPole, Matrix.mul_apply, Fin.sum_univ_two, ofLists_apply,
    ofList_apply]

/-- The damped series-RLC-type client of #8321, `A = !![0, 1; -2, -2]`, `B = (0, 1)ᵀ`,
`C = (1, 0)`, with `h t = exp (-t) sin t`: energy `1/8`, from `W = !![3/4, 1/4; 1/4, 1/8]`, and
stability from `P = !![5/4, 1/4; 1/4, 3/8]`. -/
def rlc : RatLTI 2 1 1 := ⟨[[0, 1], [-2, -2]], [[0], [1]], [[1, 0]], [[0]]⟩

theorem rlc_energy : (⟨[[5/4, 1/4], [1/4, 3/8]],
    ⟨⟨[[1], [1/5, 1]], [5/4, 13/40]⟩, ⟨[[1], [0, 1]], [1, 1]⟩⟩,
    [[3/4, 1/4], [1/4, 1/8]], 1/8⟩ : EnergyCert).check rlc = true := by
  decide +kernel

/-- A stable but unobservable model, `A = -1`, `B = 1`, `C = (1, 0)`: its Gramian
`W = diag (1/2, 0)` is singular, and it is accepted with energy `1/2`. -/
def unobservable : RatLTI 2 2 1 := ⟨[[-1, 0], [0, -1]], [[1, 0], [0, 1]], [[1, 0]], [[0, 0]]⟩

theorem unobservable_energy : (⟨[[1/2, 0], [0, 1/2]],
    ⟨⟨[[1], [0, 1]], [1/2, 1/2]⟩, ⟨[[1], [0, 1]], [1, 1]⟩⟩,
    [[1/2, 0], [0, 0]], 1/2⟩ : EnergyCert).check unobservable = true := by
  decide +kernel

/-- An unstable model whose unstable mode is unobservable: `A = diag (1, -1)`, `B = 1`,
`C = (0, 1)`. `W = diag (0, 1/2)` certifies the energy bound `1/2`. -/
def hiddenUnstable : RatLTI 2 2 1 := ⟨[[1, 0], [0, -1]], [[1, 0], [0, 1]], [[0, 1]], [[0, 0]]⟩

theorem hiddenUnstable_bound : (⟨[[0, 0], [0, 1/2]], ⟨[[1], [0, 1]], [0, 1/2]⟩, zero₂, 1/2⟩ :
    EnergyBoundCert).check hiddenUnstable = true := by
  decide +kernel

/-- No internal-stability verdict follows: no Lyapunov certificate exists for `A = diag (1, -1)`,
since `e₀ᵀ (Aᵀ P + P A) e₀ = 2 P₀₀ > 0` for every `P ≻ 0`. -/
theorem hiddenUnstable_no_lyapunov (c : LyapunovCert) (P : List (List ℚ)) :
    c.check 2 hiddenUnstable.A P = false := by
  by_contra h
  obtain ⟨hP, hQ⟩ := LyapunovCert.posDef_of_check (Bool.eq_true_of_not_eq_false h)
  have h₁ := hP.dotProduct_mulVec_pos (x := ![1, 0]) (by simp)
  have h₂ := hQ.dotProduct_mulVec_pos (x := ![1, 0]) (by simp)
  simp [hiddenUnstable, ofLists_apply, ofList_apply, dotProduct, mulVec, Fin.sum_univ_two,
    Matrix.mul_apply] at h₁ h₂
  linarith

end CslibFrontierTests.ImpulseCertificate
