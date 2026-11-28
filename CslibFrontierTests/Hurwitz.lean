/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of the Hurwitz characterization)

import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
import CslibFrontier.Foundations.Analysis.ODE.Hurwitz

/-! # Tests for Hurwitz matrices and the Lyapunov equation

A `module` client using the public statements only.

* The defective matrix `A = !![-1, 1; 0, -1]` (a repeated eigenvalue `-1` with a single
  eigenvector). It is Hurwitz by the definition, since `det (μ I - A) = (μ + 1)²`; hence
  `exp (t A) → 0` and `ẋ = A x` is exponentially stable, with no diagonalization. Independently, a
  kernel-checked certificate with `P = 1` proves exponential stability, which gives Hurwitz again
  through the converse. The Lyapunov equation `Aᵀ P + P A = -1` has the unique solution
  `P = !![1/2, 1/4; 1/4, 3/4]`, which is positive definite by
  `Matrix.IsHurwitz.posDef_of_lyapunov_eq`, and every `Q ≻ 0` has exactly one solution `P ≻ 0`.
* A non-Hurwitz matrix: `A = diag (1, -1, -3)` has the unstable eigenvalue `1`, so it is not
  exponentially stable and no `P ≻ 0` solves `Aᵀ P + P A = -1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Hurwitz

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### A defective Hurwitz matrix -/

/-- The rows of the defective matrix `!![-1, 1; 0, -1]`. -/
def Arows : List (List ℚ) := [[-1, 1], [0, -1]]

/-- The rows of `P = 1`. -/
def Prows : List (List ℚ) := [[1, 0], [0, 1]]

/-- `P = 1 = L * diagonal (1, 1) * Lᵀ` with `L = 1`, and the residual
`-(Aᵀ + A) = !![2, -1; -1, 2] = L * diagonal (2, 3/2) * Lᵀ` with `L = !![1, 0; -1/2, 1]`. -/
def cert : LyapunovCert := ⟨⟨[[1], [0, 1]], [1, 1]⟩, ⟨[[1], [-1/2, 1]], [2, 3/2]⟩⟩

theorem cert_ok : cert.check 2 Arows Prows = true := by decide +kernel

/-- The defective matrix over `ℝ`. -/
abbrev Adef : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 0, -1]

/-- `Adef` is Hurwitz directly from the definition: `det (μ I - A) = (μ + 1)²`, so the only
eigenvalue is `-1`, a defective double eigenvalue. -/
theorem isHurwitz_Adef_of_det : Adef.IsHurwitz := by
  intro μ hμ
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, det_fin_two] at hμ
  have h : (μ + 1) ^ 2 = 0 := by
    rw [← hμ]
    simp [Adef]
    ring
  rw [eq_neg_of_add_eq_zero_left (pow_eq_zero_iff two_ne_zero |>.1 h)]
  norm_num

/-- The flow of the defective matrix tends to `0`. -/
example : Filter.Tendsto (fun t : ℝ => NormedSpace.exp (t • Adef)) Filter.atTop (nhds 0) :=
  isHurwitz_Adef_of_det.tendsto_exp_smul

/-- `ẋ = Adef x` is exponentially stable in the Euclidean norm, from the spectrum alone. -/
example : (toEuclideanCLM (𝕜 := ℝ) Adef).IsExponentiallyStable :=
  isHurwitz_iff_isExponentiallyStable.1 isHurwitz_Adef_of_det

theorem map_Arows : (ofLists 2 2 Arows).map ((↑) : ℚ → ℝ) = Adef := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Arows, ofLists_apply, ofList_apply]

theorem isHurwitz_Adef : Adef.IsHurwitz :=
  isHurwitz_of_isExponentiallyStable <|
    map_Arows ▸ LyapunovCert.isExponentiallyStable_of_check cert_ok

/-- The Lyapunov solution for `Q = 1`. -/
noncomputable abbrev Pdef : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/4; 1/4, 3/4]

theorem lyapunov_Pdef : Adefᵀ * Pdef + Pdef * Adef = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `Pdef` is the only solution of `Aᵀ P + P A = -1`, among all real matrices. -/
example (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : Adefᵀ * P + P * Adef = -1) : P = Pdef :=
  (isHurwitz_Adef.existsUnique_lyapunov_eq 1).unique hP lyapunov_Pdef

/-- `Pdef ≻ 0`, from the Lyapunov theorem rather than a direct computation. -/
example : Pdef.PosDef := isHurwitz_Adef.posDef_of_lyapunov_eq PosDef.one lyapunov_Pdef

/-- `Pdef` is the only symmetric solution and the only positive definite one. -/
example : ∃! P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ Adefᵀ * P + P * Adef = -1 :=
  isHurwitz_Adef.existsUnique_posDef_lyapunov_eq PosDef.one

/-- Every `Q ≻ 0` has exactly one solution `P ≻ 0`. -/
example (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosDef) :
    ∃! P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ Adefᵀ * P + P * Adef = -Q :=
  isHurwitz_iff_forall_posDef_existsUnique_posDef.1 isHurwitz_Adef Q hQ

/-- Every `Q ≻ 0` admits a solution `P ≻ 0`. -/
example (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosDef) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ Adefᵀ * P + P * Adef = -Q :=
  isHurwitz_iff_forall_posDef_exists_posDef.1 isHurwitz_Adef Q hQ

/-! ### A matrix that is not Hurwitz -/

/-- The diagonal entries `1, -1, -3`. -/
def d : Fin 3 → ℝ := ![1, -1, -3]

/-- A diagonal matrix with the unstable eigenvalue `1`. -/
noncomputable abbrev Aunst : Matrix (Fin 3) (Fin 3) ℝ := diagonal d

theorem one_mem_spectrum : (1 : ℂ) ∈ spectrum ℂ (Aunst.map (algebraMap ℝ ℂ)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, one_smul,
    diagonal_map (map_zero _), ← diagonal_one, diagonal_sub, det_diagonal, Fin.prod_univ_three]
  simp [d]

theorem not_isHurwitz_Aunst : ¬ Aunst.IsHurwitz := fun h => by
  have := h 1 one_mem_spectrum
  norm_num at this

/-- `ẋ = Aunst x` is not exponentially stable. -/
example : ¬ (toEuclideanCLM (𝕜 := ℝ) Aunst).IsExponentiallyStable :=
  fun h => not_isHurwitz_Aunst (isHurwitz_iff_isExponentiallyStable.2 h)

/-- No positive definite `P` solves the Lyapunov equation for `Q = 1`. -/
example : ¬ ∃ P : Matrix (Fin 3) (Fin 3) ℝ, P.PosDef ∧ Aunstᵀ * P + P * Aunst = -1 :=
  fun ⟨P, hP, hPQ⟩ => not_isHurwitz_Aunst <| isHurwitz_iff_exists_posDef.2
    ⟨P, hP, by rw [hPQ, neg_neg]; exact PosDef.one⟩

end CslibFrontierTests.Hurwitz
