/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, finite-dimensional polar decomposition)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.UnitaryGroup
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Matrix.Block

/-!
# Finite-dimensional polar decomposition

Matrices with the same column Gram matrix differ by a unitary on the left. The Gram
identity first gives an isometry on the range and the finite-dimensional extension theorem
makes it unitary on the whole space. The result gives a polar decomposition even at
singular inputs and a variational characterization of the trace norm.

## Main results

* `Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq`: align two equal Gram factors.
* `Matrix.exists_unitary_polar`: factor a square matrix into a unitary and its positive modulus.
* `Matrix.traceNorm_eq_max_re_trace`: a unitary attains the trace norm by maximizing overlap.
-/

public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Two matrices with the same column Gram matrix differ by a unitary on the left. -/
theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq [Finite n] (A B : Matrix m n ℂ)
    (h : Aᴴ * A = Bᴴ * B) : ∃ U ∈ unitaryGroup m ℂ, U * A = B := by
  classical
  let := Fintype.ofFinite n
  let f := A.toEuclideanLin
  let g := B.toEuclideanLin
  have hs : (LinearMap.adjoint f).comp f = (LinearMap.adjoint g).comp g := by
    have he (M : Matrix m n ℂ) :
        (Mᴴ * M).toEuclideanLin = (LinearMap.adjoint M.toEuclideanLin).comp M.toEuclideanLin := by
      change Matrix.toLpLin 2 2 (Mᴴ * M) = _
      rw [toLpLin_mul_same]
      exact congrArg (fun L => L.comp M.toEuclideanLin) (toEuclideanLin_conjTranspose_eq_adjoint M)
    rw [← he A, ← he B, h]
  have hn (x) : ‖f x‖ = ‖g x‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h₁ : inner ℂ (f x) (f x) = inner ℂ (g x) (g x) := by
      rw [← LinearMap.adjoint_inner_right f, ← LinearMap.adjoint_inner_right g]
      exact congrArg (fun L : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n =>
        inner ℂ x (L x)) hs
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h₁]
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply norm_eq_zero.mp
    rw [← hn x, hx, norm_zero]
  let L := ((LinearMap.ker f).liftQ g hk).comp f.quotKerEquivRange.symm.toLinearMap
  have hL (x) : L ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ x
  let V : LinearMap.range f →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    ⟨L, by
      rintro ⟨_, x, rfl⟩
      rw [hL]
      exact (hn x).symm⟩
  let U := Matrix.toEuclideanLin.symm V.extend.toLinearMap
  have hU : U.toEuclideanLin = V.extend.toLinearMap := LinearEquiv.apply_symm_apply _ _
  refine ⟨U, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff_forall_norm_toEuclideanCLM]
    intro x
    change ‖U.toEuclideanLin x‖ = ‖x‖
    rw [hU]
    exact V.extend.norm_map x
  · apply Matrix.toEuclideanLin.injective
    change Matrix.toLpLin 2 2 (U * A) = B.toEuclideanLin
    rw [toLpLin_mul_same]
    change U.toEuclideanLin.comp f = g
    rw [hU]
    ext x : 1
    exact (V.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩).trans (hL x)

omit [DecidableEq m] in
/-- The trace norm is the trace of the positive modulus `√(Aᴴ A)`. -/
@[expose] noncomputable def traceNorm (A : Matrix m n ℂ) : ℝ :=
  (CFC.sqrt (Aᴴ * A)).trace.re

/-- A square matrix is a unitary times its positive modulus. -/
theorem exists_unitary_polar (A : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, U * CFC.sqrt (Aᴴ * A) = A := by
  apply exists_unitary_mul_eq_of_conjTranspose_mul_eq
  have h := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  rw [h.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg]

omit [DecidableEq n] in
/-- Taking the adjoint of one factor in the real trace pairing with a Hermitian matrix
preserves the pairing. -/
theorem IsHermitian.re_trace_conjTranspose_mul {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (U : Matrix n n ℂ) : (Uᴴ * H).trace.re = (U * H).trace.re := by
  have h : ((U * H)ᴴ).trace.re = (U * H).trace.re := by
    rw [trace_conjTranspose, Complex.star_def, Complex.conj_re]
  rwa [conjTranspose_mul, hH.eq, trace_mul_comm H] at h

private theorem re_trace_mul_le_trace_of_unitary (U H : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) (hH : H.PosSemidef) :
    (U * H).trace.re ≤ H.trace.re := by
  have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
  have hconj := hH.isHermitian.re_trace_conjTranspose_mul U
  have h := (Complex.nonneg_iff.mp
    ((posSemidef_conjTranspose_mul_self (1 - U)).trace_mul_nonneg hH)).1
  rw [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, mul_sub, hUU,
    Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, sub_mul, sub_mul, sub_mul, trace_sub,
    trace_sub, trace_sub, Complex.sub_re, Complex.sub_re, Complex.sub_re, hconj] at h
  simp only [Matrix.one_mul] at h
  linarith

/-- Real trace overlap with a unitary is bounded by the trace norm. -/
theorem re_trace_conjTranspose_mul_le_traceNorm (A U : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) : (Uᴴ * A).trace.re ≤ A.traceNorm := by
  obtain ⟨V, hV, hAV⟩ := exists_unitary_polar A
  have hU' : Uᴴ ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact (mem_unitaryGroup_iff').mp hU
  have hW : Uᴴ * V ∈ unitaryGroup n ℂ := (unitaryGroup n ℂ).mul_mem hU' hV
  conv_lhs => rw [← hAV, ← Matrix.mul_assoc]
  exact re_trace_mul_le_trace_of_unitary _ _ hW
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A)))

/-- The polar witness attains the trace norm as a complex trace with zero imaginary part. -/
theorem trace_conjTranspose_mul_eq_traceNorm_of_polar (A U : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) (h : U * CFC.sqrt (Aᴴ * A) = A) :
    (Uᴴ * A).trace = (A.traceNorm : ℂ) := by
  have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
  conv_lhs => rw [← h, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  unfold traceNorm
  have hpos := (Matrix.nonneg_iff_posSemidef.mp
    (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg
  exact Complex.ext rfl (Complex.nonneg_iff.mp hpos).2.symm

/-- The trace norm is the maximum real trace overlap with a unitary, attained by a polar
factor. -/
theorem traceNorm_eq_max_re_trace (A : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ,
      (Uᴴ * A).trace.re = A.traceNorm ∧
      ∀ V ∈ unitaryGroup n ℂ, (Vᴴ * A).trace.re ≤ (Uᴴ * A).trace.re := by
  obtain ⟨U, hU, h⟩ := A.exists_unitary_polar
  have he : (Uᴴ * A).trace.re = A.traceNorm := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re
      (trace_conjTranspose_mul_eq_traceNorm_of_polar A U hU h)
  exact ⟨U, hU, he, fun V hV => he ▸ A.re_trace_conjTranspose_mul_le_traceNorm V hV⟩

omit [DecidableEq m] in
/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (A : Matrix m n ℂ) : 0 ≤ A.traceNorm :=
  (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg).1

/-- The trace norm of a positive semidefinite matrix is its real trace. -/
theorem PosSemidef.traceNorm_eq_trace_re {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.traceNorm = A.trace.re := by
  rw [traceNorm, hA.isHermitian.eq, CFC.sqrt_mul_self _ hA.nonneg]

/-- The triangle inequality for the trace norm of square matrices. -/
theorem traceNorm_add_le (A B : Matrix n n ℂ) :
    (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨U, hU, hEq, _⟩ := (A + B).traceNorm_eq_max_re_trace
  rw [← hEq, Matrix.mul_add, trace_add, Complex.add_re]
  exact add_le_add (A.re_trace_conjTranspose_mul_le_traceNorm U hU)
    (B.re_trace_conjTranspose_mul_le_traceNorm U hU)

omit [DecidableEq m] in
@[simp] theorem traceNorm_neg (A : Matrix m n ℂ) : (-A).traceNorm = A.traceNorm := by
  rw [traceNorm, traceNorm, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

private theorem traceNorm_adjoint_square (A : Matrix n n ℂ) :
    Aᴴ.traceNorm = A.traceNorm := by
  obtain ⟨U, hU, hA⟩ := A.exists_unitary_polar
  let H := CFC.sqrt (Aᴴ * A)
  have hH : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hUU : Uᴴ * U = 1 := (mem_unitaryGroup_iff').mp hU
  have hroot : CFC.sqrt (A * Aᴴ) = U * H * Uᴴ := by
    apply CFC.sqrt_unique _ (hH.mul_mul_conjTranspose_same U).nonneg
    rw [← show U * H = A from hA, conjTranspose_mul, hH.isHermitian.eq]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (U * H) Uᴴ U, hUU, Matrix.mul_one]
  unfold traceNorm
  rw [conjTranspose_conjTranspose, hroot, trace_mul_comm (U * H) Uᴴ,
    ← Matrix.mul_assoc, hUU, Matrix.one_mul]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private theorem fromBlocks_posSemidef_diagonal [Finite m] [Finite n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A 0 0 B).PosSemidef := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simpa only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, star_eq_conjTranspose]
    using posSemidef_conjTranspose_mul_self (fromBlocks R 0 0 S)

open Classical in
private theorem sqrt_fromBlocks_diagonal {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (fromBlocks A 0 0 B) = fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  classical
  apply CFC.sqrt_unique _
    (fromBlocks_posSemidef_diagonal _ _ ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add,
    add_zero, CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]

/-- The trace norm of a rectangular matrix is unchanged by taking the conjugate transpose. -/
theorem traceNorm_conjTranspose (A : Matrix m n ℂ) : Aᴴ.traceNorm = A.traceNorm := by
  let B : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 A 0 0
  have h := traceNorm_adjoint_square B
  unfold traceNorm at h ⊢
  rw [conjTranspose_conjTranspose] at h ⊢
  have hleft : B * Bᴴ = fromBlocks (A * Aᴴ) 0 0 0 := by
    simp [B, fromBlocks_conjTranspose, fromBlocks_multiply]
  have hright : Bᴴ * B = fromBlocks 0 0 0 (Aᴴ * A) := by
    simp [B, fromBlocks_conjTranspose, fromBlocks_multiply]
  rw [hleft, hright, sqrt_fromBlocks_diagonal _ _ (posSemidef_self_mul_conjTranspose A)
    PosSemidef.zero, sqrt_fromBlocks_diagonal _ _ PosSemidef.zero
      (posSemidef_conjTranspose_mul_self A), CFC.sqrt_zero, CFC.sqrt_zero] at h
  simpa [Matrix.trace, Fintype.sum_sum_type, fromBlocks] using h

/-- Trace is invariant under unitary conjugation. -/
theorem trace_conjStarAlgAut (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- Trace norm is invariant under unitary conjugation. -/
theorem traceNorm_conjStarAlgAut (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).traceNorm = A.traceNorm := by
  let F := Unitary.conjStarAlgAut ℂ _ U
  let H := CFC.sqrt (Aᴴ * A)
  have hH : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hpos : (F H).PosSemidef := hH.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hroot : CFC.sqrt ((F A)ᴴ * F A) = F H := by
    apply CFC.sqrt_unique _ hpos.nonneg
    rw [← map_mul, ← star_eq_conjTranspose (F A), ← map_star, ← map_mul]
    change F (CFC.sqrt (Aᴴ * A) * CFC.sqrt (Aᴴ * A)) = F (Aᴴ * A)
    rw [CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg]
  change (CFC.sqrt ((F A)ᴴ * F A)).trace.re = H.trace.re
  rw [hroot, trace_conjStarAlgAut]

end Matrix
