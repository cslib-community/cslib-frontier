/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of transfer functions)

import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
import CslibFrontier.Foundations.Analysis.ODE.TransferFunction

/-! # Tests for transfer functions

A `module` client using the public statements only.

* The transfer functions of the stable defective system `A = !![-1, 1; 0, -1]` are holomorphic
  on an open half-plane containing `re s ≥ 0`.
* The hidden-mode warning: `A = diag (1, -1, -3)` has the unstable eigenvalue `1`, so `A` is not
  Hurwitz; but with `B = (0, 1, 1)ᵀ` and `C = (0, 1, -2)` the transfer function is
  `H s = (1 - s) / ((s + 1) (s + 3))` wherever `s ≠ -1, -3`, including at the cancelled
  eigenvalue `s = 1`, so `H` is holomorphic on `re s > -1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.TransferFunction

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### A defective stable system -/

/-- The defective matrix over `ℝ`. -/
abbrev Adef : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 0, -1]

theorem isHurwitz_Adef : Adef.IsHurwitz := by
  intro μ hμ
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, det_fin_two] at hμ
  have h : (μ + 1) ^ 2 = 0 := by
    rw [← hμ]
    simp [Adef]
    ring
  rw [eq_neg_of_add_eq_zero_left (pow_eq_zero_iff two_ne_zero |>.1 h)]
  norm_num

/-- For every `B`, `C`, `D` the transfer function of the stable defective system is holomorphic
on an open half-plane containing `re s ≥ 0`. -/
example (B : Matrix (Fin 2) (Fin 1) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ)
    (D : Matrix (Fin 1) (Fin 1) ℝ) : ∃ α > 0, DifferentiableOn ℂ
      (fun s => (LTISystem.mk Adef B C D).transferFunction s 0 0) {s | -α < s.re} :=
  let ⟨α, hα, h⟩ := LTISystem.differentiableOn_transferFunction_of_isExponentiallyStable
    (LTISystem.mk Adef B C D) isHurwitz_Adef.isExponentiallyStable
  ⟨α, hα, h 0 0⟩

/-! ### A hidden unstable mode -/

/-- The diagonal entries `1, -1, -3` of the state matrix. -/
def d : Fin 3 → ℝ := ![1, -1, -3]

/-- A system whose unstable mode `1` is neither controllable nor observable. -/
noncomputable def hidden : LTISystem (Fin 3) (Fin 1) (Fin 1) where
  A := diagonal d
  B := !![0; 1; 1]
  C := !![0, 1, -2]
  D := 0

theorem one_mem_spectrum : (1 : ℂ) ∈ spectrum ℂ (hidden.A.map (algebraMap ℝ ℂ)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, one_smul,
    show hidden.A = diagonal d from rfl, diagonal_map (map_zero _), ← diagonal_one, diagonal_sub,
    det_diagonal, Fin.prod_univ_three]
  simp [d]

theorem not_isHurwitz_hidden : ¬ hidden.A.IsHurwitz := fun h => by
  have := h 1 one_mem_spectrum
  norm_num at this

/-- No positive definite `P` solves the Lyapunov equation for `Q = 1`. -/
example : ¬ ∃ P : Matrix (Fin 3) (Fin 3) ℝ, P.PosDef ∧ hidden.Aᵀ * P + P * hidden.A = -1 :=
  fun ⟨P, hP, hPQ⟩ => not_isHurwitz_hidden <| isHurwitz_iff_exists_posDef.2
    ⟨P, hP, by rw [hPQ, neg_neg]; exact PosDef.one⟩

/-- The visible part of the transfer function. -/
noncomputable def g (s : ℂ) : ℂ := (1 - s) / ((s + 1) * (s + 3))

theorem transferFunction_hidden {s : ℂ} (h1 : s + 1 ≠ 0) (h3 : s + 3 ≠ 0) :
    hidden.transferFunction s 0 0 = g s := by
  have hA : s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - hidden.A.map (algebraMap ℝ ℂ) =
      diagonal fun i => s - d i := by
    rw [show hidden.A = diagonal d from rfl, diagonal_map (map_zero _), smul_one_eq_diagonal,
      diagonal_sub]
    rfl
  unfold LTISystem.transferFunction
  rw [hA]
  by_cases hs : s = 1
  · subst hs
    rw [nonsing_inv_apply_not_isUnit _ (by simp [det_diagonal, Fin.prod_univ_three, d])]
    simp [g, hidden]
  · have hd : ∀ i, s - d i ≠ 0 := fun i => by
      fin_cases i
      · simpa [d] using sub_ne_zero.2 hs
      · simpa [d] using h1
      · simpa [d] using h3
    rw [inv_eq_left_inv (B := diagonal fun i => (s - d i)⁻¹) (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hd i)))]
    have h1' : s - 1 ≠ 0 := sub_ne_zero.2 hs
    simp [hidden, g, Matrix.mul_apply, Fin.sum_univ_three, d]
    field_simp
    ring

/-- **Hidden-mode warning.** The transfer function of `hidden` is holomorphic on `re s > -1`, in
particular on the closed right half-plane, although `hidden.A` is not Hurwitz. -/
example : DifferentiableOn ℂ (fun s => hidden.transferFunction s 0 0) {s | -1 < s.re} := by
  have hne : ∀ s ∈ {s : ℂ | -1 < s.re}, s + 1 ≠ 0 ∧ s + 3 ≠ 0 := fun s hs => by
    constructor <;> intro h <;> have := congrArg Complex.re h <;> simp at this hs <;> linarith
  refine DifferentiableOn.congr (f := g) (fun s hs => ?_) fun s hs =>
    transferFunction_hidden (hne s hs).1 (hne s hs).2
  have hg : DifferentiableAt ℂ (fun z : ℂ => (1 - z) / ((z + 1) * (z + 3))) s := by
    apply DifferentiableAt.div <;> first | fun_prop | exact mul_ne_zero (hne s hs).1 (hne s hs).2
  exact hg.differentiableWithinAt

end CslibFrontierTests.TransferFunction
