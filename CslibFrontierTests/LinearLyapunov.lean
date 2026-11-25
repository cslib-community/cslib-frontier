/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for linear time-invariant flows and the quadratic Lyapunov criterion

* Scalar systems `ẋ = a x` on `ℝ`: the flow is `exp (a t) x₀`; `a = -1` is exponentially
  stable, `a = 0` is Lyapunov stable but not asymptotically stable, and `a = 1` is not Lyapunov
  stable. These check both sides of the stability definitions.
* The non-diagonalizable `A = !![-1, 1; 0, -1]`: `exp (t • A) = exp (-t) • !![1, t; 0, 1]` for
  `t ≥ 0`, obtained from uniqueness, and exponential stability from the certificate `P = 1`.
* The concrete example of #8320: `A = !![0, 1; -2, -3]` and `P = !![5/4, 1/4; 1/4, 1/4]` with
  `Aᵀ P + P A = -1`. The kernel accepts its `LDLᵀ` certificate (`decide +kernel`), and
  `Cslib.LinearAlgebra.LyapunovCert.isExponentiallyStable_of_check` turns acceptance into
  exponential stability of all trajectories. Corrupted certificates are rejected, and so is every
  certificate with `P = 1`, although `A` is stable: rejection is not instability.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearLyapunov

open Set Filter Topology NormedSpace Matrix ContinuousLinearMap Mathlib.Tactic.Matrix
open Cslib.LinearAlgebra

/-! ### Scalar systems -/

/-- The scalar system `ẋ = a x` on `ℝ`. -/
noncomputable abbrev scalar (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

theorem isTrajectoryOn_scalar (a x₀ : ℝ) (s : Set ℝ) :
    (scalar a).IsTrajectoryOn (fun t => Real.exp (a * t) * x₀) s := fun t _ => by
  have h := (((hasDerivAt_id t).const_mul a).exp).mul_const x₀
  refine (h.congr_deriv ?_).hasDerivWithinAt
  simp only [id, mul_one, scalar, smul_apply, coe_id', smul_eq_mul]
  ring

/-- Every scalar trajectory on `[0, ∞)` is `exp (a t) * x 0`. -/
theorem scalar_eq {a : ℝ} {x : ℝ → ℝ} (hx : (scalar a).IsTrajectoryOn x (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : x t = Real.exp (a * t) * x 0 := by
  have h₁ := hx.eqOn_exp_smul_apply_Ici ht
  have h₂ := (isTrajectoryOn_scalar a (x 0) (Ici 0)).eqOn_exp_smul_apply_Ici ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h₂
  rw [h₁, h₂]

/-- The scalar flow, for `t ≥ 0`. -/
example (a x₀ t : ℝ) (ht : 0 ≤ t) : exp (t • scalar a) x₀ = Real.exp (a * t) * x₀ := by
  simpa using ((isTrajectoryOn_scalar a x₀ (Ici 0)).eqOn_exp_smul_apply_Ici ht).symm

/-- `ẋ = -x` is exponentially stable, with `M = 1` and `α = 1`. -/
example : (scalar (-1)).IsExponentiallyStable := by
  refine ⟨1, 1, one_pos, fun x hx t ht => ?_⟩
  rw [scalar_eq hx ht, norm_mul, Real.norm_eq_abs, Real.abs_exp]
  simp

/-- `ẋ = 0` is Lyapunov stable. -/
example : (scalar 0).IsLyapunovStable := fun ε hε => ⟨ε, hε, fun x hx h0 t ht => by
  rwa [scalar_eq hx ht, zero_mul, Real.exp_zero, one_mul]⟩

/-- `ẋ = 0` is not asymptotically stable: nonzero constants do not tend to `0`. -/
example : ¬ (scalar 0).IsAsymptoticallyStable := by
  rintro ⟨-, δ, hδ, h⟩
  have hx : (scalar 0).IsTrajectoryOn (fun _ => δ / 2) (Ici 0) := by
    simpa using isTrajectoryOn_scalar 0 (δ / 2) (Ici 0)
  have := tendsto_nhds_unique (h _ hx (by simp [abs_of_pos hδ]; linarith)) tendsto_const_nhds
  linarith

/-- `ẋ = x` is not Lyapunov stable. -/
example : ¬ (scalar 1).IsLyapunovStable := by
  intro h
  obtain ⟨δ, hδ, hδ'⟩ := h 1 one_pos
  have hx := isTrajectoryOn_scalar 1 (δ / 2) (Ici 0)
  have h0 : ‖Real.exp (1 * 0) * (δ / 2)‖ < δ := by
    simp [abs_of_pos hδ]
    linarith
  -- At time `t = log (4 / δ)` the trajectory has reached `2`.
  have ht : 0 ≤ Real.log (4 / δ) ⊔ 0 := le_max_right _ _
  have h1 := hδ' _ hx h0 _ ht
  have hexp : 4 / δ ≤ Real.exp (1 * (Real.log (4 / δ) ⊔ 0)) := by
    rw [one_mul]
    calc 4 / δ = Real.exp (Real.log (4 / δ)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_max_left _ _)
  rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have : 4 / δ * (δ / 2) = 2 := by field_simp; norm_num
  nlinarith [mul_le_mul_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ δ / 2)]

/-! ### A non-diagonalizable matrix -/

/-- A Jordan block with the repeated eigenvalue `-1`. -/
abbrev jordan : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 0, -1]

/-- For `t ≥ 0`, `exp (t • jordan) = exp (-t) • !![1, t; 0, 1]`; this is derived from uniqueness
of trajectories, without diagonalizing. -/
example {t : ℝ} (ht : 0 ≤ t) : exp (t • jordan) = Real.exp (-t) • !![1, t; 0, 1] := by
  ext i j
  -- The `j`-th column solves the ODE with the `j`-th basis vector as initial value.
  let x : ℝ → Fin 2 → ℝ := fun τ => Real.exp (-τ) • (!![1, τ; 0, 1] *ᵥ Pi.single j 1)
  have hx : ∀ τ ∈ Ici (0 : ℝ), HasDerivWithinAt x (jordan *ᵥ x τ) (Ici 0) τ := by
    intro τ _
    refine (hasDerivAt_pi.2 fun k => ?_).hasDerivWithinAt
    have he := (hasDerivAt_neg τ).exp
    fin_cases j <;> fin_cases k
    · simpa [x, jordan, mulVec, dotProduct, Fin.sum_univ_two] using he
    · simpa [x, jordan, mulVec, dotProduct, Fin.sum_univ_two] using (hasDerivAt_const τ 0)
    · have h2 : HasDerivAt (fun τ => Real.exp (-τ) * τ) (Real.exp (-τ) * -1 * τ + Real.exp (-τ) * 1)
          τ := he.mul (hasDerivAt_id' τ)
      convert h2 using 1
      · funext σ
        simp [x]
      · simp [x, jordan, mulVec, dotProduct, Fin.sum_univ_two]
    · simpa [x, jordan, mulVec, dotProduct, Fin.sum_univ_two] using he
  have h := congrFun (eq_exp_smul_mulVec_of_hasDerivWithinAt hx ht) i
  simp only [x, neg_zero, Real.exp_zero, one_smul] at h
  fin_cases i <;> fin_cases j <;> simpa [mulVec, dotProduct, Fin.sum_univ_two] using h.symm

/-- The Jordan block is exponentially stable, certified by `P = 1`. -/
example : (toEuclideanCLM (𝕜 := ℝ) jordan).IsExponentiallyStable := by
  refine isExponentiallyStable_toEuclideanCLM_of_posDef (P := 1) PosDef.one ?_
  have : -(jordanᵀ * 1 + 1 * jordan) = !![2, -1; -1, 2] := by
    rw [show jordanᵀ = !![-1, 0; 1, -1] from by ext i j; fin_cases i <;> fin_cases j <;> rfl]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  rw [this]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · have : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext fun k => by fin_cases k <;> simp [h.1, h.2])
    simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, star_trivial]
    rcases this with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0 - v 1), sq_nonneg (v 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0 - v 1), sq_nonneg (v 0)]

/-! ### The concrete certificate of #8320, accepted by the `LDLᵀ` checker of #8319 -/

/-- The rows of the system matrix `!![0, 1; -2, -3]` of the #8320 example. -/
def Arows : List (List ℚ) := [[0, 1], [-2, -3]]

/-- The rows of the Lyapunov matrix `P = !![5/4, 1/4; 1/4, 1/4]`. -/
def Prows : List (List ℚ) := [[5/4, 1/4], [1/4, 1/4]]

/-- The `LDLᵀ` witnesses: `P = L * diagonal (5/4, 1/5) * Lᵀ` with `L = !![1, 0; 1/5, 1]`, and
the residual `-(Aᵀ * P + P * A) = 1`, which the checker recomputes from `A` and `P`, with `L = 1`
and `d = (1, 1)`. -/
def cert : LyapunovCert := ⟨⟨[[1], [1/5, 1]], [5/4, 1/5]⟩, ⟨[[1], [0, 1]], [1, 1]⟩⟩

theorem cert_ok : cert.check 2 Arows Prows = true := by decide +kernel

/-- The system matrix of the #8320 example, over `ℝ`. -/
abbrev Aex : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -2, -3]

theorem map_Arows : (ofLists 2 2 Arows).map ((↑) : ℚ → ℝ) = Aex := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Arows, ofLists_apply, ofList_apply]

/-- Every trajectory of `ẋ = Aex x` in `EuclideanSpace ℝ (Fin 2)` decays exponentially in the
Euclidean norm, from the kernel's acceptance of `cert`. -/
theorem isExponentiallyStable_Aex : (toEuclideanCLM (𝕜 := ℝ) Aex).IsExponentiallyStable :=
  map_Arows ▸ LyapunovCert.isExponentiallyStable_of_check cert_ok

/-- The same conclusion for coordinate solutions `x : ℝ → Fin 2 → ℝ` of `x' = Aex *ᵥ x`, measured
in the Euclidean norm of `WithLp.toLp 2 (x t)` (not the supremum norm of `Fin 2 → ℝ`). -/
example : ∃ M α : ℝ, 0 < α ∧ ∀ x : ℝ → Fin 2 → ℝ,
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (Aex *ᵥ x t) (Ici 0) t) →
      ∀ t ≥ 0, ‖WithLp.toLp 2 (x t)‖ ≤ M * Real.exp (-(α * t)) * ‖WithLp.toLp 2 (x 0)‖ := by
  obtain ⟨M, α, hα, h⟩ := isExponentiallyStable_Aex
  exact ⟨M, α, hα, fun x hx => h _ (isTrajectoryOn_toEuclideanCLM_iff.2 hx)⟩

/-! ### Rejected certificates

Rejection is not instability: `Aex` is exponentially stable, yet no certificate is accepted with
`P = 1`, since `-(Aexᵀ + Aex) = !![0, 1; 1, 6]` is not positive definite. -/

/-- A corrupted witness for `P`. -/
example : (⟨⟨[[1], [1/4, 1]], [5/4, 1/5]⟩, cert.Q⟩ : LyapunovCert).check 2 Arows Prows = false := by
  decide +kernel

/-- The same certificate for the unstable `!![0, 1; 2, 3]`, whose residual is not `1`. -/
example : cert.check 2 [[0, 1], [2, 3]] Prows = false := by decide +kernel

/-- No certificate is accepted for the stable `Aex` with `P = 1`. -/
theorem rejected_P_one (c : LyapunovCert) : c.check 2 Arows [[1, 0], [0, 1]] = false := by
  by_contra h
  have hQ := (LyapunovCert.posDef_of_check (Bool.eq_true_of_not_eq_false h)).2
  have := hQ.dotProduct_mulVec_pos (x := ![1, 0]) (by simp)
  norm_num [Arows, ofLists_apply, ofList_apply, dotProduct, mulVec, Fin.sum_univ_two,
    Matrix.mul_apply] at this

end CslibFrontierTests.LinearLyapunov
