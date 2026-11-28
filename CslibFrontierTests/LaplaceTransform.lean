/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of Laplace transforms and transfer functions)

import CslibFrontier.Foundations.Analysis.LaplaceTransform.Deriv
import CslibFrontier.Foundations.Analysis.ODE.LaplaceTransferFunction
import CslibFrontierTests.TransferFunction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for Laplace transforms of LTI responses

A `module` client using the public statements only.

* Milestone 1: `laplace (exp (-t)) s = 1 / (s + 1)` and `laplace (t exp (-t)) s = 1 / (s + 1) ^ 2`
  on `re s > -1`; holomorphy; the derivative rule for `f = exp (-t)`; the convolution theorem for
  `exp (-t) ∗ exp (-t)`; the derivative rule for `f = exp (2 t)`, whose derivative has the larger
  constant `2`.
* The RC circuit `A = -1/τ`, `B = 1/τ`, `C = 1`, `D = 0` with `τ > 0`: `H s = 1 / (τ s + 1)`,
  `laplace h s = 1 / (τ s + 1)` on `re s > -1/τ`, and `laplace y = H · laplace u` for every
  admissible input.
* The repeated pole `A = !![-1, 1; 0, -1]`, `B = (0, 1)ᵀ`, `C = (1, 0)`: `h t = t exp (-t)`,
  `H s = 1 / (s + 1) ^ 2` for `s ≠ -1`, and `laplace h = H` on a half-plane `re s > -α`, `α > 0`,
  obtained from the stability of `A`; the transform computed in milestone 1 agrees with it; `-1`
  is a pole of `H`.
* A hidden unstable mode, `A = diag (1, -1, -3)`, `B = (0, 1, 1)ᵀ`, `C = (0, 1, -2)`: `1` is an
  eigenvalue of `A` but not a pole of `H`; `laplace h = H` on `re s > -1`. The systems `hidden`
  and `Adef` and their transfer functions come from `CslibFrontierTests.TransferFunction`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LaplaceTransform

open Set Matrix NormedSpace LTISystem CslibFrontierTests.TransferFunction Filter Topology

/-! ### Milestone 1 -/

theorem laplace_exp_neg {s : ℂ} (hs : -1 < s.re) :
    laplace (fun t : ℝ => Complex.exp (-t)) s = 1 / (s + 1) := by
  have h := laplace_cexp (a := -1) (s := s) (by simpa using hs)
  simp only [neg_one_mul, sub_neg_eq_add] at h
  exact h

theorem laplaceConvergent_exp_neg {s : ℂ} (hs : -1 < s.re) :
    LaplaceConvergent (fun t : ℝ => Complex.exp (-t)) s := by
  have h := laplaceConvergent_cexp (a := -1) (s := s) (by simpa using hs)
  simp only [neg_one_mul] at h
  exact h

theorem laplace_mul_exp_neg {s : ℂ} (hs : -1 < s.re) :
    laplace (fun t : ℝ => (t : ℂ) * Complex.exp (-t)) s = 1 / (s + 1) ^ 2 := by
  have h := laplace_mul_cexp (a := -1) (s := s) (by simpa using hs)
  simp only [neg_one_mul, sub_neg_eq_add] at h
  exact h

theorem norm_exp_neg_le (t : ℝ) : ‖Complex.exp (-t)‖ ≤ 1 * Real.exp (-1 * t) := by
  rw [one_mul, Complex.norm_exp, neg_one_mul]
  simp

/-- `laplace (exp (-t))` is holomorphic on `re s > -1`. -/
example : DifferentiableOn ℂ (laplace fun t : ℝ => Complex.exp (-t)) {s | -1 < s.re} :=
  differentiableOn_laplace (Continuous.aestronglyMeasurable (by fun_prop))
    fun t _ => norm_exp_neg_le t

/-- The derivative rule for `f t = exp (-t)`, `f' t = -exp (-t)`, `f 0 = 1`:
`laplace f' s = s laplace f s - 1`. -/
example {s : ℂ} (hs : -1 < s.re) :
    laplace (fun t : ℝ => -Complex.exp (-t)) s = s * (1 / (s + 1)) - 1 := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun τ : ℝ => Complex.exp (-τ)) (-Complex.exp (-t)) t :=
    fun t _ => by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).cexp
  rw [laplace_deriv (Continuous.continuousWithinAt (by fun_prop)) hd
    (fun t _ => norm_exp_neg_le t) (fun t _ => by rw [norm_neg]; exact norm_exp_neg_le t)
    (by simpa using hs) (by simpa using hs), laplace_exp_neg hs]
  simp

/-- The derivative rule for `f t = exp (2 t)`, `f' t = 2 exp (2 t)`: the natural bounds have
different constants, `‖f t‖ ≤ 1 · exp (2 t)` and `‖f' t‖ ≤ 2 · exp (2 t)`. -/
example {s : ℂ} (hs : 2 < s.re) :
    laplace (fun t : ℝ => 2 * Complex.exp (2 * t)) s = s * (1 / (s - 2)) - 1 := by
  have hd : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun τ : ℝ => Complex.exp (2 * τ)) (2 * Complex.exp (2 * t)) t := fun t _ => by
    simpa [mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul 2).cexp
  rw [laplace_deriv (M := 1) (M' := 2) (σ := 2) (σ' := 2)
    (Continuous.continuousWithinAt (by fun_prop)) hd
    (fun t _ => by rw [one_mul, Complex.norm_exp]; simp)
    (fun t _ => by rw [norm_mul, Complex.norm_exp]; simp) hs hs,
    laplace_cexp (a := 2) (by simpa using hs)]
  simp

/-- The convolution theorem for `exp (-t) ∗ exp (-t)` (which is `t exp (-t)`). -/
example {s : ℂ} (hs : -1 < s.re) :
    laplace (causalConvolution (ContinuousLinearMap.mul ℂ ℂ) (fun t : ℝ => Complex.exp (-t))
      (fun t : ℝ => Complex.exp (-t))) s = 1 / (s + 1) ^ 2 := by
  rw [laplace_causalConvolution _ (laplaceConvergent_exp_neg hs) (laplaceConvergent_exp_neg hs),
    ContinuousLinearMap.mul_apply', laplace_exp_neg hs, div_mul_div_comm, one_mul, sq]

/-! ### The RC circuit -/

/-- The RC circuit with time constant `τ = R C`. -/
noncomputable abbrev rc (τ : ℝ) : LTISystem (Fin 1) (Fin 1) (Fin 1) :=
  ⟨!![-τ⁻¹], !![τ⁻¹], !![1], !![0]⟩

theorem exp_smul_rc (τ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    exp (t • (rc τ).A) = !![Real.exp (-τ⁻¹ * t)] := by
  have h := exp_smul_mul_eq_of_hasDerivWithinAt (A := (rc τ).A)
    (X := fun σ => !![Real.exp (-τ⁻¹ * σ)]) ?_ ht
  · have h1 : (!![Real.exp (-τ⁻¹ * 0)] : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [h1, Matrix.mul_one] at h
    exact h
  · intro j σ _
    fin_cases j
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    fin_cases k
    have h := ((hasDerivAt_id σ).const_mul (-τ⁻¹)).exp
    simp only [id, mul_one] at h
    convert h using 1
    · funext σ
      simp
    · simp [mulVec, dotProduct]
      ring

theorem abs_exp_smul_rc_le (τ : ℝ) :
    ∀ t ∈ Ioi (0 : ℝ), ∀ i j, |exp (t • (rc τ).A) i j| ≤ 1 * Real.exp (-τ⁻¹ * t) := by
  intro t ht i j
  fin_cases i
  fin_cases j
  rw [exp_smul_rc τ (le_of_lt ht)]
  simp [abs_of_pos (Real.exp_pos _)]

theorem transferFunction_rc {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ} (hs : (τ : ℂ) * s + 1 ≠ 0) :
    (rc τ).transferFunction s 0 0 = 1 / (τ * s + 1) := by
  have hne : s + (τ : ℂ)⁻¹ ≠ 0 := by
    intro h
    apply hs
    have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
    calc (τ : ℂ) * s + 1 = τ * (s + (τ : ℂ)⁻¹) := by field_simp
      _ = 0 := by rw [h, mul_zero]
  have hA : s • (1 : Matrix (Fin 1) (Fin 1) ℂ) - (rc τ).A.map (algebraMap ℝ ℂ) =
      !![s + (τ : ℂ)⁻¹] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hinv : (!![s + (τ : ℂ)⁻¹])⁻¹ = !![(s + (τ : ℂ)⁻¹)⁻¹] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i
    fin_cases j
    simp [hne]
  unfold LTISystem.transferFunction
  rw [hA, hinv]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  simp [Matrix.mul_apply]
  field_simp

theorem mul_add_one_ne_zero {τ : ℝ} (hτ : 0 < τ) {s : ℂ} (hs : -τ⁻¹ < s.re) :
    (τ : ℂ) * s + 1 ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.one_re, Complex.zero_re] at h1
  have h2 : -1 < τ * s.re := by
    have := mul_lt_mul_of_pos_left hs hτ
    rwa [mul_neg, mul_inv_cancel₀ hτ.ne'] at this
  linarith

/-- **The RC circuit, impulse response.** `laplace h s = 1 / (τ s + 1)` on `re s > -1/τ`. -/
example {τ : ℝ} (hτ : 0 < τ) {s : ℂ} (hs : -τ⁻¹ < s.re) :
    laplace (fun t => ((rc τ).responseKernel t 0 0 : ℂ)) s = 1 / (τ * s + 1) := by
  rw [laplace_responseKernel_eq_transferFunction_sub (rc τ) (abs_exp_smul_rc_le τ) hs,
    transferFunction_rc hτ.ne' (mul_add_one_ne_zero hτ hs)]
  simp

/-- **The RC circuit, forced response.** For every solution with zero initial state driven by a
continuous input whose transform converges at `s`, `laplace y s = laplace u s / (τ s + 1)` on
`re s > -1/τ`. -/
example {τ : ℝ} (hτ : 0 < τ) {s : ℂ} (hs : -τ⁻¹ < s.re) {u : ℝ → Fin 1 → ℝ}
    {x : ℝ → Fin 1 → ℝ} (hx : (rc τ).IsSolutionOn u x (Ici 0)) (hx₀ : x 0 = 0)
    (hu : ContinuousOn u (Ici 0)) (huL : LaplaceConvergent (fun t j => (u t j : ℂ)) s) :
    laplace (fun t i => ((((rc τ).C *ᵥ x t + (rc τ).D *ᵥ u t) i : ℝ) : ℂ)) s 0 =
      1 / (τ * s + 1) * laplace (fun t j => (u t j : ℂ)) s 0 := by
  rw [hx.laplace_output hx₀ hu huL (abs_exp_smul_rc_le τ) hs]
  simp only [mulVec, dotProduct, Fin.sum_univ_one]
  rw [transferFunction_rc hτ.ne' (mul_add_one_ne_zero hτ hs)]

/-! ### The repeated pole -/

/-- A Jordan block with eigenvalue `-1`, `B = (0, 1)ᵀ`, `C = (1, 0)`, `D = 0`. -/
abbrev repeatedPole : LTISystem (Fin 2) (Fin 1) (Fin 1) :=
  ⟨!![-1, 1; 0, -1], !![0; 1], !![1, 0], 0⟩

/-- `h t = t exp (-t)`, certified from a realization. -/
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

/-- The milestone-1 transform of the repeated-pole kernel: `1 / (s + 1) ^ 2` on `re s > -1`. -/
theorem laplace_responseKernel_repeatedPole {s : ℂ} (hs : -1 < s.re) :
    laplace (fun t => (repeatedPole.responseKernel t 0 0 : ℂ)) s = 1 / (s + 1) ^ 2 := by
  rw [laplace_congr (g := fun t : ℝ => (t : ℂ) * Complex.exp (-t)) fun t ht => by
    simp [responseKernel_repeatedPole (le_of_lt ht)]]
  exact laplace_mul_exp_neg hs

theorem isHurwitz_repeatedPole : repeatedPole.A.IsHurwitz := isHurwitz_Adef

/-- `H s = 1 / (s + 1) ^ 2` for `s ≠ -1`, computed algebraically. -/
theorem transferFunction_repeatedPole {s : ℂ} (hs : s + 1 ≠ 0) :
    repeatedPole.transferFunction s 0 0 = 1 / (s + 1) ^ 2 := by
  have hA : s • (1 : Matrix (Fin 2) (Fin 2) ℂ) - repeatedPole.A.map (algebraMap ℝ ℂ) =
      !![s + 1, -1; 0, s + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hinv : (!![s + 1, -1; 0, s + 1])⁻¹ = !![(s + 1)⁻¹, ((s + 1) ^ 2)⁻¹; 0, (s + 1)⁻¹] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    ring
  unfold LTISystem.transferFunction
  rw [hA, hinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The repeated pole, frequency domain.** By stability there is `α > 0` such that on
`re s > -α` the transfer function equals the transform of the impulse response; with the
milestone-1 transform this gives `H s = 1 / (s + 1) ^ 2` there, in agreement with
`transferFunction_repeatedPole`. -/
example : ∃ α > 0, ∀ s : ℂ, -α < s.re → -1 < s.re →
    repeatedPole.transferFunction s 0 0 = 1 / (s + 1) ^ 2 := by
  obtain ⟨M, α, hα, h⟩ := isHurwitz_repeatedPole.isExponentiallyStable
  refine ⟨α, hα, fun s hs h1 => ?_⟩
  have e := laplace_responseKernel_eq_transferFunction_sub repeatedPole
    (abs_exp_smul_apply_le_of_forall_norm_le h) hs 0 0
  rw [laplace_responseKernel_repeatedPole h1] at e
  simpa using e.symm

/-- Every pole of the repeated-pole transfer function has real part at most `-α` for some
`α > 0`, from the stability of `A`. -/
example : ∃ α > 0, ∀ z : ℂ,
    meromorphicOrderAt (fun s => repeatedPole.transferFunction s 0 0) z < 0 → z.re ≤ -α :=
  let ⟨α, hα, h⟩ := exists_pos_re_le_of_meromorphicOrderAt_neg_of_isExponentiallyStable
    repeatedPole isHurwitz_repeatedPole.isExponentiallyStable
  ⟨α, hα, h 0 0⟩

/-- **The repeated pole is a pole.** `-1` is a pole of `H`, although `H (-1) = 0` there by the
junk value of the matrix inverse: the order sees only a punctured neighbourhood. -/
example : meromorphicOrderAt (fun s => repeatedPole.transferFunction s 0 0) (-1) < 0 := by
  have h : (fun s => repeatedPole.transferFunction s 0 0) =ᶠ[𝓝[≠] (-1 : ℂ)]
      (· - (-1)) ^ (-2 : ℤ) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ -1)
    rw [transferFunction_repeatedPole fun h => hs (eq_neg_of_add_eq_zero_left h)]
    simp [_root_.zpow_neg]
  rw [meromorphicOrderAt_congr h, meromorphicOrderAt_zpow_id_sub_const]
  decide

/-! ### The hidden unstable mode -/

/-- **Hidden-mode warning, poles.** `1` is an eigenvalue of `hidden.A` (`one_mem_spectrum`), but
it is not a pole of `H`: the order of `H` at `1` is nonnegative. -/
example : 0 ≤ meromorphicOrderAt (fun s => hidden.transferFunction s 0 0) 1 := by
  have hopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_transferFunction_hidden.analyticAt
    (hopen.mem_nhds (by norm_num))).meromorphicOrderAt_nonneg

/-- `h t = exp (-t) - 2 exp (-3 t)`: the unstable mode is invisible in the impulse response. -/
theorem responseKernel_hidden (t : ℝ) :
    hidden.responseKernel t 0 0 = Real.exp (-t) - 2 * Real.exp (-3 * t) := by
  have hA : hidden.A = diagonal d := rfl
  rw [responseKernel_eq, hA, ← diagonal_smul, exp_diagonal, Pi.exp_def]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, ← Real.exp_eq_exp_ℝ]
  simp [TransferFunction.hidden, d]
  ring_nf

/-- **Hidden-mode warning, transforms.** Although the flow of `hidden.A` grows like `exp t`, the
transform of the impulse response converges on `re s > -1` and equals `H` there. -/
example {s : ℂ} (hs : -1 < s.re) :
    laplace (fun t => (hidden.responseKernel t 0 0 : ℂ)) s = hidden.transferFunction s 0 0 := by
  have h1 := laplaceConvergent_cexp (a := -1) (s := s) (by simpa using hs)
  have h3 := (laplaceConvergent_cexp (a := -3) (s := s) (by simp; linarith)).const_mul 2
  rw [laplace_congr (g := fun t : ℝ => Complex.exp (-1 * t) - 2 * Complex.exp (-3 * t))
    fun t _ => by simp [responseKernel_hidden], laplace_sub h1 h3, laplace_const_mul,
    laplace_cexp (by simpa using hs), laplace_cexp (by simp; linarith),
    transferFunction_hidden (ne_zero_of_re hs).1 (ne_zero_of_re hs).2, g]
  obtain ⟨n1, n3⟩ := ne_zero_of_re hs
  rw [sub_neg_eq_add, sub_neg_eq_add]
  field_simp
  ring

end CslibFrontierTests.LaplaceTransform
