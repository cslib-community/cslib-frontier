/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (Mathlib, matrix left-kernel dimension and parity-check matrices)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Matrix left-kernel dimension and parity-check matrices

For an `m × n` matrix `F` over a field `K`, the left kernel `ker Fᵀ.mulVecLin` has dimension
`leftKernelDim F` satisfying `leftKernelDim F + F.rank = m` (`Matrix.leftKernelDim_add_rank`),
so `m - n ≤ leftKernelDim F` (`Matrix.sub_le_leftKernelDim`). Choosing a basis of the left
kernel yields a surjective parity-check matrix `H : Matrix (Fin (leftKernelDim F)) (Fin m) K`
satisfying `H * F = 0` (`Matrix.exists_parityCheckMatrix`).

## Main definitions

* `Matrix.leftKernelDim`: dimension of the left kernel `ker Fᵀ.mulVecLin`.

## Main results

* `Matrix.leftKernelDim_add_rank`: rank-nullity identity `leftKernelDim F + F.rank = m`.
* `Matrix.sub_le_leftKernelDim`: lower bound `m - n ≤ leftKernelDim F`.
* `Matrix.exists_parityCheckMatrix`: existence of a surjective left-kernel parity-check matrix
  `H` with `H * F = 0`.
* `Matrix.parityCheck_mulVec_of_eq_zero`: `H * F = 0` implies `H *ᵥ (F *ᵥ w) = 0`.
-/

public section

namespace Matrix

variable {K : Type*} [Field K] {m n r : ℕ}

/-- The dimension of the left kernel `ker Fᵀ` of `F : Matrix (Fin m) (Fin n) K`. -/
noncomputable def leftKernelDim (F : Matrix (Fin m) (Fin n) K) : ℕ :=
  Module.finrank K (LinearMap.ker Fᵀ.mulVecLin)

/-- Rank-nullity on `Fᵀ`: `leftKernelDim F + F.rank = m`. -/
theorem leftKernelDim_add_rank (F : Matrix (Fin m) (Fin n) K) :
    leftKernelDim F + F.rank = m := by
  have hrn := Fᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Fᵀ.rank + leftKernelDim F = Module.finrank K (Fin m → K) at hrn
  rw [Matrix.rank_transpose, Module.finrank_fin_fun] at hrn
  omega

/-- Any `m × n` matrix over a field has left-kernel dimension at least `m - n`. -/
theorem sub_le_leftKernelDim (F : Matrix (Fin m) (Fin n) K) :
    m - n ≤ leftKernelDim F := by
  have hsum := leftKernelDim_add_rank F
  have hr : F.rank ≤ n := by simpa [Fintype.card_fin] using F.rank_le_card_width
  omega

/-- Every `F : Matrix (Fin m) (Fin n) K` admits an explicit parity-check matrix `H` with
`leftKernelDim F` rows such that `H * F = 0` and `H.mulVecLin` is surjective. -/
theorem exists_parityCheckMatrix (F : Matrix (Fin m) (Fin n) K) :
    ∃ H : Matrix (Fin (leftKernelDim F)) (Fin m) K,
      H * F = 0 ∧ Function.Surjective H.mulVecLin := by
  let b := (Module.finBasis K (LinearMap.ker Fᵀ.mulVecLin)).reindex
    (finCongr rfl : Fin (Module.finrank K (LinearMap.ker Fᵀ.mulVecLin)) ≃
      Fin (leftKernelDim F))
  let H : Matrix (Fin (leftKernelDim F)) (Fin m) K :=
    Matrix.of fun i j => (b i : Fin m → K) j
  refine ⟨H, ?_, ?_⟩
  · ext i k
    have hker : Fᵀ.mulVec (b i : Fin m → K) = 0 := (b i).property
    have hk := congrFun hker k
    simpa [H, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using hk
  · have hHT_inj : LinearMap.ker Hᵀ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro c hc
      have hsum : (∑ i, c i • (b i : LinearMap.ker Fᵀ.mulVecLin)) = 0 := by
        apply Subtype.ext
        ext j
        have hj := congrFun hc j
        simpa [H, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm,
          Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] using hj
      ext i
      exact linearIndependent_iff'.mp b.linearIndependent Finset.univ c hsum i (Finset.mem_univ i)
    have hrank := leftKernelDim_add_rank H
    rw [leftKernelDim, hHT_inj, finrank_bot, zero_add] at hrank
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
      (hrank.trans (Module.finrank_fin_fun K).symm))

/-- A left-kernel check annihilates every vector in the image of `F`. -/
theorem parityCheck_mulVec_of_eq_zero {H : Matrix (Fin r) (Fin m) K}
    {F : Matrix (Fin m) (Fin n) K} (hHF : H * F = 0) (w : Fin n → K) :
    H *ᵥ (F *ᵥ w) = 0 := by
  rw [Matrix.mulVec_mulVec, hHF, Matrix.zero_mulVec]

end Matrix
