/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.KernelVector
import Mathlib.Algebra.BigOperators.Fin

/-!
# Linear system solving and prescribed-entry kernel vectors by elimination

Building on the spanning kernel family `Cslib.LinearAlgebra.kernelBasis` from
`CslibFrontier.Foundations.LinearAlgebra.KernelVector`, this module defines two total elimination
functions over any field with decidable equality:

* `Cslib.LinearAlgebra.kernelVecAt A j`: selects the first member of `kernelBasis A` whose entry
  `j` is nonzero and scales it so entry `j` is `1`, returning `0` when every kernel vector of `A`
  has entry `j` equal to `0` (`Cslib.LinearAlgebra.mulVec_kernelVecAt`,
  `Cslib.LinearAlgebra.kernelVecAt_apply_self_eq_one_iff`,
  `Cslib.LinearAlgebra.kernelVecAt_eq_zero`).
* `Cslib.LinearAlgebra.vecMulSolve M b`: solves `w ᵥ* M = b` whenever a solution exists
  (`Cslib.LinearAlgebra.vecMul_vecMulSolve`, `Cslib.LinearAlgebra.vecMul_vecMulSolve_iff`) and
  returns `0` otherwise (`Cslib.LinearAlgebra.vecMulSolve_eq_zero`), by running
  `kernelVecAt (vecMulSolveMatrix M b) 0` on `(b ‖ Mᵀ)` so a kernel vector with first coordinate
  `1` solves `b + w ᵥ* M = 0`.

Related and distinct: `Matrix.solveVec` in `CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss`
is noncomputable and takes explicit pivot row and column lists as arguments (with its only certified
algorithm, `ratSolve`, specialized to `ℚ`). Here no pivot selections are supplied, and every
operation unfolds to a fixed arithmetic expression over the field matching the circuit bounds in
`CslibFrontier.Computability.Circuit.LinearSolve`.

## Main definitions

* `Cslib.LinearAlgebra.kernelPivotAt`: first member of `kernelBasis A` with nonzero entry `j`.
* `Cslib.LinearAlgebra.kernelVecAt`: kernel vector normalized to `1` at entry `j`, or `0`.
* `Cslib.LinearAlgebra.vecMulSolveMatrix`: augmented matrix whose kernel encodes
  `x₀ • b + w ᵥ* M = 0`.
* `Cslib.LinearAlgebra.vecMulSolve`: straight-line solver for `w ᵥ* M = b`.

## Main results

* `Cslib.LinearAlgebra.mulVec_kernelVecAt`: `kernelVecAt A j` lies in the kernel of `A`.
* `Cslib.LinearAlgebra.kernelVecAt_apply_self_eq_one_iff`: entry `j` is `1` iff some kernel vector
  has nonzero entry `j`.
* `Cslib.LinearAlgebra.kernelVecAt_eq_zero`: `kernelVecAt A j = 0` when every kernel vector vanishes
  at entry `j`.
* `Cslib.LinearAlgebra.vecMul_vecMulSolve`: `vecMulSolve M b ᵥ* M = b` whenever a solution exists.
* `Cslib.LinearAlgebra.vecMul_vecMulSolve_iff`: `vecMulSolve M b ᵥ* M = b ↔ ∃ w, w ᵥ* M = b`.
* `Cslib.LinearAlgebra.vecMulSolve_eq_zero`: `vecMulSolve M b = 0` when no solution exists.
-/

public section

namespace Cslib.LinearAlgebra

open Finset
open scoped Matrix

variable {F : Type*} [Field F] [DecidableEq F] {n r : ℕ}

/-- The first member of `kernelBasis A` whose entry `j` is nonzero, or zero if there is none. -/
@[expose] def kernelPivotAt (A : Matrix (Fin r) (Fin n) F) (j : Fin n) : Fin n → F :=
  ∑ i, firstFlags (fun i => kernelBasis A i j) i • kernelBasis A i

/-- **A kernel vector with a prescribed entry equal to one.** The first member of `kernelBasis A`
whose entry `j` is nonzero, scaled so that this entry is one; zero if every kernel vector has
entry `j` equal to zero. -/
@[expose] def kernelVecAt (A : Matrix (Fin r) (Fin n) F) (j : Fin n) : Fin n → F :=
  (kernelPivotAt A j j)⁻¹ • kernelPivotAt A j

private theorem mulVec_kernelPivotAt (A : Matrix (Fin r) (Fin n) F) (j : Fin n) :
    A *ᵥ kernelPivotAt A j = 0 := by
  rcases sum_firstFlags_smul_eq (fun i => kernelBasis A i j) (kernelBasis A) with
    ⟨-, h⟩ | ⟨i, -, -, h⟩
  · rw [kernelPivotAt, h, Matrix.mulVec_zero]
  · rw [kernelPivotAt, h, mulVec_kernelBasis]

/-- `kernelVecAt A j` lies in the kernel of `A`. -/
theorem mulVec_kernelVecAt (A : Matrix (Fin r) (Fin n) F) (j : Fin n) :
    A *ᵥ kernelVecAt A j = 0 := by
  rw [kernelVecAt, Matrix.mulVec_smul, mulVec_kernelPivotAt A j, smul_zero]

/-- Entry `j` of `kernelVecAt A j` is one exactly when some kernel vector of `A` has a nonzero
entry `j`. -/
theorem kernelVecAt_apply_self_eq_one_iff (A : Matrix (Fin r) (Fin n) F) (j : Fin n) :
    kernelVecAt A j j = 1 ↔ ∃ v, A *ᵥ v = 0 ∧ v j ≠ 0 := by
  constructor
  · intro h
    exact ⟨_, mulVec_kernelVecAt A j, by rw [h]; exact one_ne_zero⟩
  · rintro ⟨v, hv, hvj⟩
    obtain ⟨c, rfl⟩ := exists_eq_sum_kernelBasis A hv
    rcases sum_firstFlags_smul_eq (fun i => kernelBasis A i j) (kernelBasis A) with
      ⟨hb, -⟩ | ⟨i, hi, -, h⟩
    · refine absurd ?_ hvj
      rw [Finset.sum_apply]
      exact sum_eq_zero fun i _ => by
        rw [Pi.smul_apply, show kernelBasis A i j = 0 from congrFun hb i, smul_zero]
    · rw [kernelVecAt, Pi.smul_apply, kernelPivotAt, h, smul_eq_mul]
      exact inv_mul_cancel₀ hi

/-- When every kernel vector of `A` has entry `j` equal to zero, `kernelVecAt A j` is zero. -/
theorem kernelVecAt_eq_zero (A : Matrix (Fin r) (Fin n) F) (j : Fin n)
    (h : ∀ v, A *ᵥ v = 0 → v j = 0) : kernelVecAt A j = 0 := by
  rw [kernelVecAt, h _ (mulVec_kernelPivotAt A j), inv_zero, zero_smul]

/-- The matrix whose kernel vectors `(x₀, w)` are the solutions of `x₀ • b + w ᵥ* M = 0`: its
column `0` is `b` and its column `k + 1` is row `k` of `M`. -/
@[expose] def vecMulSolveMatrix (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F) :
    Matrix (Fin n) (Fin (r + 1)) F :=
  fun l => Fin.cons (b l) fun k => M k l

/-- **Solving `w ᵥ* M = b` by elimination.** The output is a solution whenever there is one
(`vecMul_vecMulSolve`) and `0` otherwise (`vecMulSolve_eq_zero`). -/
@[expose] def vecMulSolve (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F) : Fin r → F :=
  fun k => -kernelVecAt (vecMulSolveMatrix M b) 0 k.succ

omit [DecidableEq F] in
private theorem vecMulSolveMatrix_mulVec (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F)
    (x : Fin (r + 1) → F) (l : Fin n) :
    (vecMulSolveMatrix M b *ᵥ x) l = b l * x 0 + ∑ k, M k l * x k.succ := by
  simp [Matrix.mulVec, dotProduct, vecMulSolveMatrix, Fin.sum_univ_succ]

/-- `vecMulSolve M b` solves `w ᵥ* M = b` whenever a solution exists. -/
theorem vecMul_vecMulSolve (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F)
    (h : ∃ w, w ᵥ* M = b) : vecMulSolve M b ᵥ* M = b := by
  obtain ⟨w, rfl⟩ := h
  set B := vecMulSolveMatrix M (w ᵥ* M) with hB
  have hone : kernelVecAt B 0 0 = 1 := by
    refine (kernelVecAt_apply_self_eq_one_iff B 0).2 ⟨Fin.cons (-1) w, ?_, by simp⟩
    funext l
    rw [hB, vecMulSolveMatrix_mulVec]
    simp [Matrix.vecMul, dotProduct, mul_comm]
  funext l
  have hl := congrFun (mulVec_kernelVecAt B 0) l
  rw [hB, vecMulSolveMatrix_mulVec, ← hB, hone, mul_one, Pi.zero_apply] at hl
  have : (vecMulSolve M (w ᵥ* M) ᵥ* M) l = -∑ k, M k l * kernelVecAt B 0 k.succ := by
    simp [Matrix.vecMul, dotProduct, vecMulSolve, ← hB, mul_comm, Finset.sum_neg_distrib]
  rw [this]
  exact (eq_neg_of_add_eq_zero_left hl).symm

/-- `vecMulSolve M b` solves `w ᵥ* M = b` if and only if a solution exists. -/
theorem vecMul_vecMulSolve_iff (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F) :
    vecMulSolve M b ᵥ* M = b ↔ ∃ w, w ᵥ* M = b :=
  ⟨fun h => ⟨_, h⟩, vecMul_vecMulSolve M b⟩

/-- When `w ᵥ* M = b` has no solution, `vecMulSolve M b` is zero. -/
theorem vecMulSolve_eq_zero (M : Matrix (Fin r) (Fin n) F) (b : Fin n → F)
    (h : ¬ ∃ w, w ᵥ* M = b) : vecMulSolve M b = 0 := by
  have hz : kernelVecAt (vecMulSolveMatrix M b) 0 = 0 := by
    refine kernelVecAt_eq_zero _ _ fun v hv => ?_
    by_contra hv0
    refine h ⟨fun k => -(v 0)⁻¹ * v k.succ, funext fun l => ?_⟩
    have hl := congrFun hv l
    rw [vecMulSolveMatrix_mulVec, Pi.zero_apply] at hl
    have hs : ∑ k, M k l * v k.succ = -(b l * v 0) := eq_neg_of_add_eq_zero_right hl
    simp only [Matrix.vecMul, dotProduct]
    calc ∑ k, -(v 0)⁻¹ * v k.succ * M k l
        = -(v 0)⁻¹ * ∑ k, M k l * v k.succ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc, mul_comm (v k.succ)]
      _ = b l := by
        rw [hs, neg_mul_neg, mul_comm (b l), ← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
  funext k
  simp only [vecMulSolve, hz, Pi.zero_apply, neg_zero]

end Cslib.LinearAlgebra
