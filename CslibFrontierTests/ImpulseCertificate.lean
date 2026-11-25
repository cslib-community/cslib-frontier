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
* an RC circuit with `τ = 1/1000 s`: energy `500 s⁻¹` and decay at rate `1000 s⁻¹`;
* the repeated-pole client of #8321, `h t = t exp (-t)`: energy `1/4` and decay at rate `1/2`;
  its initial output `h 0` vanishes;
* the damped RLC-type client of #8321, `h t = exp (-t) sin t`: energy `1/8`;
* a stable unobservable model with singular Gramian `diag (1/2, 0)`;
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
def scalarDecay : DecayCert := ⟨[[1]], 1, 1, 1, 1, 1, zero₁, zero₁, zero₁, zero₁, zero₁⟩

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
  have := DecayCert.responseKernel_mulVec_sq_le_of_impulseSettles scalarDecay_ok scalar_settles
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
  have := DecayCert.dotProduct_self_le_of_stateSettles scalarDecay_ok scalar_stateSettles hx
    (by exact_mod_cast h0) (t := t) (by norm_num; linarith)
  norm_num at this
  exact this

/-- A negative squared initial-state radius is rejected. -/
example : scalarDecay.stateSettles (-1) 1 0 1 = false := by decide +kernel

/-- The decay certificate also proves internal stability. -/
example : (toEuclideanCLM (𝕜 := ℝ) scalar.toSystem.A).IsExponentiallyStable :=
  DecayCert.isExponentiallyStable scalarDecay_ok

/-- `h t ² ≤ exp (-2 t)` for `‖v‖₂ = 1`; here `h t = exp (-t)` and the envelope is attained. -/
example (v : Fin 1 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    scalar.toSystem.responseKernel t *ᵥ v ⬝ᵥ scalar.toSystem.responseKernel t *ᵥ v ≤
      Real.exp (-2 * t) * (v ⬝ᵥ v) := by
  simpa [scalarDecay] using DecayCert.responseKernel_mulVec_sq_le scalarDecay_ok v ht

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

/-- A model with direct feedthrough gets no impulse-energy certificate. -/
example : scalarEnergy.check (⟨[[-1]], [[1]], [[1]], [[1]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

example : scalarBound.check (⟨[[-1]], [[1]], [[1]], [[1]]⟩ : RatLTI 1 1 1) = false := by
  decide +kernel

/-- The energy tail after `T`: `∫_T^∞ h(t)² dt ≤ exp (-2 T) / 2`. -/
example {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioi T, scalar.toSystem.responseKernel t 0 0 ^ 2 ≤ Real.exp (-2 * T) / 2 := by
  have := (DecayCert.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le scalarDecay_ok hT).2
  have htr : rowsTrace 1 (rowsCongr 1 1 scalar.B [[1]]) = 1 := by decide +kernel
  simpa [htr, scalarDecay] using this

/-- The numerical tail `∫_2^∞ h(t)² dt ≤ 1/100`, from `exp 4 ≥ expLower 12 4 > 50`; the
claim `1/200` is rejected. -/
example : ∫ t in Ioi (2 : ℝ), ∑ i, ∑ j, scalar.toSystem.responseKernel t i j ^ 2 ≤ 1/100 := by
  have h : scalarDecay.tailBelow scalar (1/100) 2 12 = true := by decide +kernel
  have := DecayCert.integral_Ioi_frobeniusSq_le_of_tailBelow scalarDecay_ok h
  norm_num at this ⊢
  exact this

example : scalarDecay.tailBelow scalar (1/200) 2 12 = false := by decide +kernel

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
theorem rc_decay : (⟨[[1]], 1000, 1, 1, 1, 1000000, zero₁, zero₁, zero₁, zero₁, zero₁⟩ :
    DecayCert).check rc = true := by
  decide +kernel

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
  ⟨[[1, 0], [0, 1]], 1/2, 1, 1, 1, 1, ⟨[[1], [-1, 1]], [1, 0]⟩, zero₂, zero₂,
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
