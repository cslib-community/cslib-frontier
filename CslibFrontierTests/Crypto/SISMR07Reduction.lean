/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.SIS.MR07Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Tests for `CslibFrontier/Crypto/Computational/SIS/MR07Reduction.lean`

Ordinary `module` client verifying the strict-PPT Micciancio–Regev `IncGDD` and `GIVP` reductions
(`MR07Reduction`, `MR07Reduction.Shorten`, `MR07Reduction.IncGDD`) on a concrete non-diagonal,
non-symmetric `2 × 2` full-rank integer lattice `B = [[1, 1], [0, 2]]` (`det B = 2`, `B ≠ Bᵀ`):

1. Strict-PPT instantiation (`isPPTOn_singleIncGDDCall`, `isPPTOn_mr07IncGDDReduction`,
   `isPPTOn_mr07GIVPReduction`) on concrete polytime SIS parameters `(n, m, q, β) = (2, 17, 330, 5)`
   and an explicit strict-PPT solver `zeroSISSolver`.
2. Basis-orientation check distinguishing `B` from `Bᵀ` via `intTableMaxColSqNorm` and
   `intTableMaxSqNormIdx`, plus unconditional `guardedUpdateIntTable_invariants` and
   `ratOrthoTargetIntTable_spec` verification across the `module` boundary.
3. Zero-assumption non-vacuity instantiation of `mr07GIVPReduction_succProb_ge` and
   `mr07GIVPReduction_succProb_ge_half` on `B = [[1, 1], [0, 2]]`: since `330² = 108900 < 2¹⁷` and
   `64 · 2² · 17 · 5² = 108800 ≤ 330²`, pigeonhole on `Fin 17 → Bool` gives an explicit solver with
   `sisEll2Advantage = 1`, discharging every hypothesis of `mr07GIVPReduction_succProb_ge` with
   zero free assumptions.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SISMR07Reduction

open Cslib Cslib.Crypto Cslib.Crypto.SIS Cslib.Crypto.SIS.MR07 Cslib.LinearAlgebra
open Cslib.Probability Cslib.ProbComp Turing.MultiTapeTM ComputableInPolyTime ZLattice
open scoped BigOperators ENNReal NNReal RealInnerProductSpace _root_.Matrix

/-! ### 1. Concrete Non-Diagonal `2 × 2` Lattice & Polytime SIS Family -/

private def testB : Matrix (Fin 2) (Fin 2) ℤ := ![![1, 1], ![0, 2]]

private theorem testB_det_ne_zero : testB.det ≠ 0 := by decide

private theorem testB_ne_transpose : testB ≠ testBᵀ := by decide

private def testSISParams : SISParams where
  n _ := 2
  m _ := 17
  q _ := 330
  β _ := 5
  hq _ := ⟨by decide⟩

private theorem testSISParams_polyTime : MR07ParamPolyTime testSISParams where
  hn := ComputableInPolyTime.const 2
  hm := ComputableInPolyTime.const 17
  hβ := ComputableInPolyTime.const 5
  hq := ComputableInPolyTime.const 330

/-! ### 2. Basis-Orientation & Shortening Helper Checks across the `module` Boundary -/

private theorem testB_colSqNorm (j : Fin 2) :
    intTableColSqNorm (RowTable.ofMatrix testB) j.val = if j = 0 then 1 else 5 := by
  rw [intTableColSqNorm_eq_sum_sq, RowTable.numRows_ofMatrix]
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, List.range_succ, List.range_zero, List.map_append,
      List.map_singleton, List.map_nil, List.sum_append, List.sum_singleton, List.sum_nil,
      zero_add,
      RowTable.entry_ofMatrix_of_lt testB (by decide : 0 < 2) (by decide : 0 < 2),
      RowTable.entry_ofMatrix_of_lt testB (by decide : 1 < 2) (by decide : 0 < 2),
      RowTable.entry_ofMatrix_of_lt testB (by decide : 0 < 2) (by decide : 1 < 2),
      RowTable.entry_ofMatrix_of_lt testB (by decide : 1 < 2) (by decide : 1 < 2)] <;>
    decide

private theorem testBT_colSqNorm (j : Fin 2) :
    intTableColSqNorm (RowTable.ofMatrix testBᵀ) j.val = if j = 0 then 2 else 4 := by
  rw [intTableColSqNorm_eq_sum_sq, RowTable.numRows_ofMatrix]
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, List.range_succ, List.range_zero, List.map_append,
      List.map_singleton, List.map_nil, List.sum_append, List.sum_singleton, List.sum_nil,
      zero_add,
      RowTable.entry_ofMatrix_of_lt testBᵀ (by decide : 0 < 2) (by decide : 0 < 2),
      RowTable.entry_ofMatrix_of_lt testBᵀ (by decide : 1 < 2) (by decide : 0 < 2),
      RowTable.entry_ofMatrix_of_lt testBᵀ (by decide : 0 < 2) (by decide : 1 < 2),
      RowTable.entry_ofMatrix_of_lt testBᵀ (by decide : 1 < 2) (by decide : 1 < 2)] <;>
    decide

private theorem testB_maxColSqNorm_eq_five :
    intTableMaxColSqNorm (RowTable.ofMatrix testB) = 5 := by
  refine le_antisymm ?_ ?_
  · refine intTableMaxColSqNorm_le _ fun j hj => ?_
    rw [RowTable.numCols_ofMatrix] at hj
    have h := testB_colSqNorm ⟨j, hj⟩
    dsimp only at h
    split_ifs at h <;> omega
  · have h1 := testB_colSqNorm 1
    simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte] at h1
    simpa [h1] using intTableColSqNorm_le_max (RowTable.ofMatrix testB) (j := 1)
      (by rw [RowTable.numCols_ofMatrix]; decide)

private theorem testBT_maxColSqNorm_eq_four :
    intTableMaxColSqNorm (RowTable.ofMatrix testBᵀ) = 4 := by
  refine le_antisymm ?_ ?_
  · refine intTableMaxColSqNorm_le _ fun j hj => ?_
    rw [RowTable.numCols_ofMatrix] at hj
    have h := testBT_colSqNorm ⟨j, hj⟩
    dsimp only at h
    split_ifs at h <;> omega
  · have h1 := testBT_colSqNorm 1
    simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte] at h1
    simpa [h1] using intTableColSqNorm_le_max (RowTable.ofMatrix testBᵀ) (j := 1)
      (by rw [RowTable.numCols_ofMatrix]; decide)

private theorem testB_maxSqNormIdx_eq_one :
    intTableMaxSqNormIdx (RowTable.ofMatrix testB) = 1 := by
  have heq := intTableMaxSqNormIdx_eq_maxSqNormIndex (m := 1) (RowTable.ofMatrix testB) rfl rfl
  rw [heq]
  have hS : (fun j i : Fin 2 => ((RowTable.ofMatrix testB).entry i.val j.val : ℚ)) =
      (fun j i : Fin 2 => (testB i j : ℚ)) := by
    funext j i
    rw [RowTable.entry_ofMatrix_of_lt testB i.isLt j.isLt]
  rw [hS]
  have hmax := MR07Shorten.sqNormRat_le_maxSqNormIndex (fun j i : Fin 2 => (testB i j : ℚ)) 1
  have h0 : MR07Shorten.sqNormRat (fun i : Fin 2 => (testB i 0 : ℚ)) = 1 := by
    simp [MR07Shorten.sqNormRat, Fin.sum_univ_two, testB]
  have h1 : MR07Shorten.sqNormRat (fun i : Fin 2 => (testB i 1 : ℚ)) = 5 := by
    simp [MR07Shorten.sqNormRat, Fin.sum_univ_two, testB]; norm_num
  set idx : Fin 2 := MR07Shorten.maxSqNormIndex (fun j i : Fin 2 => (testB i j : ℚ))
  change idx.val = 1
  by_contra hne
  have hlt := idx.isLt
  have hidx0 : idx = 0 := Fin.ext (by omega)
  rw [h1, hidx0, h0] at hmax
  norm_num at hmax

private theorem testB_ratOrthoTarget_spec :
    let T := RowTable.ofMatrix testB
    let S : Fin 2 → Fin 2 → ℚ := fun j i => (T.entry i.val j.val : ℚ)
    let iStar := MR07Shorten.maxSqNormIndex S
    let tE := MR07Shorten.toEuclidean
      (fun k : Fin 2 => (ratOrthoTargetIntTable T).getD k.val 0)
    intTableMaxSqNormIdx T = iStar.val ∧
    ‖intCol (Matrix.of fun i j : Fin 2 => T.entry i.val j.val) iStar‖ =
      ‖intCol (Matrix.of fun i j : Fin 2 => T.entry i.val j.val)‖ ∧
    (∀ j, j ≠ iStar → ⟪tE, intCol (Matrix.of fun i j : Fin 2 => T.entry i.val j.val) j⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖intCol (Matrix.of fun i j : Fin 2 => T.entry i.val j.val)‖ < ‖tE‖ ∧
    ‖tE‖ ≤ (9 / 16 : ℝ) * ‖intCol (Matrix.of fun i j : Fin 2 => T.entry i.val j.val)‖ := by
  have hmat : (Matrix.of fun i j : Fin 2 => (RowTable.ofMatrix testB).entry i.val j.val) =
      testB := by
    ext i j; exact RowTable.entry_ofMatrix_of_lt testB i.isLt j.isLt
  have hli : LinearIndependent ℝ
      (intCol (Matrix.of fun i j : Fin 2 => (RowTable.ofMatrix testB).entry i.val j.val)) := by
    rw [hmat, linearIndependent_intCol_iff_det_ne_zero]
    exact testB_det_ne_zero
  exact ratOrthoTargetIntTable_spec (RowTable.ofMatrix testB) rfl rfl hli

/-! ### 3. Strict-PPT Certificates on a Concrete PPT SIS Solver -/

private noncomputable def zeroSISSolver : testSISParams.Solver :=
  fun _ _ => pure 0

private theorem zeroSISSolver_isPPT : zeroSISSolver.IsPPT := by
  have hconst : ComputableInPolyTime
      (fun _ : testSISParams.Input => encList encIntBin (List.replicate 17 (0 : ℤ)))
      testSISParams.encInput encBits :=
    ComputableInPolyTime.const _
  refine (hconst.isPPTOn).congr fun x => ?_
  have hlist : (List.ofFn (0 : Fin (testSISParams.m x.secParam) → ℤ)) =
      List.replicate 17 (0 : ℤ) := by
    refine List.ext_getElem (by rw [List.length_ofFn]; rfl) fun i h₁ h₂ => ?_
    rw [List.getElem_ofFn, List.getElem_replicate]
    rfl
  simp [zeroSISSolver, SIS.encodeVec, hlist]

private theorem test_isPPTOn_singleIncGDDCall :
    IsPPTOn IncGDDInput.enc (encList encIntBin)
      (singleIncGDDCall testSISParams zeroSISSolver) :=
  isPPTOn_singleIncGDDCall testSISParams_polyTime zeroSISSolver_isPPT

private theorem test_isPPTOn_mr07IncGDDReduction :
    IsPPTOn IncGDDInput.enc (encList encIntBin)
      (mr07IncGDDReduction testSISParams zeroSISSolver) :=
  isPPTOn_mr07IncGDDReduction testSISParams_polyTime zeroSISSolver_isPPT

private theorem test_isPPTOn_mr07GIVPReduction :
    IsPPTOn GIVPInput.enc IntTable.enc
      (mr07GIVPReduction testSISParams 1 zeroSISSolver) :=
  isPPTOn_mr07GIVPReduction testSISParams_polyTime 1 zeroSISSolver_isPPT

/-! ### 4. Zero-Assumption Non-Vacuity Instantiation of `mr07GIVPReduction_succProb_ge` -/

private theorem exists_ell2_solution_testSISParams
    (A : Matrix (Fin 2) (Fin 17) (ZMod 330)) :
    ∃ z : Fin 17 → ℤ, SIS.IsEll2Solution A (5 : ℝ) z := by
  let f : (Fin 17 → Bool) → (Fin 2 → ZMod 330) :=
    fun b => A *ᵥ fun j => if b j then (1 : ZMod 330) else 0
  have hcard : Fintype.card (Fin 2 → ZMod 330) < Fintype.card (Fin 17 → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Fintype.card_bool]
    decide
  obtain ⟨x, y, hxy, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  let z : Fin 17 → ℤ := fun j => (if x j then 1 else 0) - (if y j then 1 else 0)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro hz0
    apply hxy
    funext j
    have hj := congrFun hz0 j
    cases hx : x j <;> cases hy : y j <;> simp [z, hx, hy] at hj ⊢
  · have hcoord : ∀ j : Fin 17, (z j : ℝ) ^ 2 ≤ 1 := fun j => by
      cases hx : x j <;> cases hy : y j <;> norm_num [z, hx, hy]
    have hsum : ∑ j : Fin 17, (z j : ℝ) ^ 2 ≤ (17 : ℝ) := by
      calc ∑ j : Fin 17, (z j : ℝ) ^ 2 ≤ ∑ _j : Fin 17, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => hcoord j
        _ = 17 := by simp
    have hnorm : ‖(WithLp.toLp 2 fun j : Fin 17 => (z j : ℝ) : EuclideanSpace ℝ (Fin 17))‖ ^ 2 ≤
        (5 : ℝ) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hnorm
  · unfold InKernelLattice
    have hcast : (Int.cast ∘ z : Fin 17 → ZMod 330) =
        (fun j => if x j then (1 : ZMod 330) else 0) -
        (fun j => if y j then (1 : ZMod 330) else 0) := by
      funext j; cases x j <;> cases y j <;> simp [z]
    rw [hcast, Matrix.mulVec_sub]
    change f x - f y = 0
    rw [hfeq, sub_self]

private noncomputable def pigeonholeSISSolver : testSISParams.Solver :=
  fun _ A => pure (Classical.choose (exists_ell2_solution_testSISParams A))

private theorem sisEll2Advantage_pigeonhole_eq_one (κ : ℕ) :
    (sisEll2Advantage (testSISParams.q κ) (testSISParams.β κ : ℝ)
      (pigeonholeSISSolver κ) : ℝ) = 1 := by
  let S : Matrix (Fin 2) (Fin 17) (ZMod 330) → ProbComp (Fin 17 → ℤ) :=
    fun A => pure (Classical.choose (exists_ell2_solution_testSISParams A))
  change (((ProbComp.eval (sisEll2Experiment 330 (5 : ℝ) S)) true).toNNReal : ℝ) = 1
  have heval : (ProbComp.eval (sisEll2Experiment 330 (5 : ℝ) S)) true = 1 := by
    unfold sisEll2Experiment
    rw [ProbComp.eval_bind, PMF.bind_apply]
    have hpt : ∀ A : Matrix (Fin 2) (Fin 17) (ZMod 330),
        (ProbComp.eval (ProbComp.uniform (Matrix (Fin 2) (Fin 17) (ZMod 330)))) A *
          (ProbComp.eval (do
            let z ← S A
            return @decide (SIS.IsEll2Solution A (5 : ℝ) z)
              (Classical.propDecidable _))) true =
        (ProbComp.eval (ProbComp.uniform (Matrix (Fin 2) (Fin 17) (ZMod 330)))) A := fun A => by
      have hspec := Classical.choose_spec (exists_ell2_solution_testSISParams A)
      have h1 : (ProbComp.eval (do
          let z ← S A
          return @decide (SIS.IsEll2Solution A (5 : ℝ) z)
            (Classical.propDecidable _))) true = 1 := by
        dsimp only [S]
        rw [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, ProbComp.eval_pure,
          PMF.pure_apply]
        simp [hspec]
      rw [h1, mul_one]
    simp_rw [hpt]
    exact (ProbComp.eval _).tsum_coe
  rw [heval]
  simp

private theorem test_mr07Eps_unfold :
    mr07Eps 17 5 0 1 = 1 / (400 * 5 * 17 ^ 2 * 1) := by
  unfold mr07Eps
  norm_num

private theorem test_mr07GIVPReduction_succProb_ge_concrete :
    let ε := mr07Eps 17 5 0 1
    let φ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) → ℝ :=
      fun L => ZLattice.smoothingParameter L ε
    (3 / 4 : ℝ) ≤
      ((ProbComp.eval
        (mr07GIVPReduction testSISParams 1 pigeonholeSISSolver
          ⟨0, RowTable.ofMatrix testB⟩)).toOuterMeasure
        {T | ∃ S : Matrix (Fin 2) (Fin 2) ℤ, T = RowTable.ofMatrix S ∧
          GIVP.IsSolution φ (8 * (5 : ℝ) * Real.sqrt 2) (intLattice testB)
            (intColCast testB S testB_det_ne_zero)}).toReal := by
  have h := mr07GIVPReduction_succProb_ge testSISParams 1 pigeonholeSISSolver 0
    (by decide) (by decide) (by decide) (by decide)
    (by rw [sisEll2Advantage_pigeonhole_eq_one 0]; norm_num)
    testB testB_det_ne_zero
  dsimp only [testSISParams] at h
  rw [show (1 - (1 / 4 : ℝ) * (2 : ℝ) ^ (-((0 : ℕ) : ℤ))) = (3 / 4 : ℝ) by norm_num] at h
  exact h

private theorem test_mr07GIVPReduction_succProb_ge_half_concrete :
    let ε := mr07Eps 17 5 0 1
    let φ : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) → ℝ :=
      fun L => ZLattice.smoothingParameter L ε
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval
        (mr07GIVPReduction testSISParams 1 pigeonholeSISSolver
          ⟨0, RowTable.ofMatrix testB⟩)).toOuterMeasure
        {T | ∃ S : Matrix (Fin 2) (Fin 2) ℤ, T = RowTable.ofMatrix S ∧
          GIVP.IsSolution φ (8 * (5 : ℝ) * Real.sqrt 2) (intLattice testB)
            (intColCast testB S testB_det_ne_zero)}).toReal :=
  mr07GIVPReduction_succProb_ge_half testSISParams 1 pigeonholeSISSolver 0
    (by decide) (by decide) (by decide) (by decide)
    (by rw [sisEll2Advantage_pigeonhole_eq_one 0]; norm_num)
    testB testB_det_ne_zero

end CslibFrontierTests.Crypto.SISMR07Reduction
