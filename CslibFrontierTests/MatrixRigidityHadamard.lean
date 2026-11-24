/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Hadamard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Basic

/-!
# Tests for Hadamard and Sylvester–Hadamard matrix rigidity

Exercises `CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Hadamard` through an ordinary
`module` import:

* target rank `r = 0` across `ℚ`, `ℝ`, and `ZMod 2`;
* tight equality `(sylvesterHadamard ℚ 1).rigidity 1 = 1` and
  `(sylvesterHadamard ℝ 1).rigidity 1 = 1` at `n = 2, r = 1`;
* tight equality `(sylvesterHadamard ℚ 2).rigidity 1 = 4` at `n = 4, r = 1` (strictly exceeding the
  rank-deficit lower bound `4 - 1 = 3`), together with `2 ≤ rigidity 2 ≤ 3` at `n = 4, r = 2`;
* `n = 8` (`k = 3`) at `r = 1, 2, 3, 4` over `ℚ` and `ℝ` (including non-power-of-two `r = 3` where
  `8 ^ 2 ≤ 12 * rigidity 3` forces `6 ≤ rigidity 3`), and at `r = 1, 2` over `ZMod 3`;
* an asymmetric complex Hadamard matrix `!![1, I; 1, -I]` over `ℂ` where `H * Hᵀ ≠ 2 • 1` while
  `H * Hᴴ = 2 • 1`, verifying conjugate-transpose semantics and `IsHadamard` dot-notation;
* formal counterexamples showing that `2 * r ≤ n`, `(2 : K) ≠ 0`, and row orthogonality cannot be
  omitted.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.MatrixRigidityHadamard

open Matrix
open scoped Kronecker

/-! ### Target rank `r = 0` -/

example :
    (sylvesterHadamard ℚ 0).rigidity 0 = 1 ∧
    (sylvesterHadamard ℚ 1).rigidity 0 = 4 ∧
    (sylvesterHadamard ℝ 2).rigidity 0 = 16 ∧
    (sylvesterHadamard (ZMod 2) 3).rigidity 0 = 64 :=
  ⟨rigidity_sylvesterHadamard_zero ℚ 0,
   rigidity_sylvesterHadamard_zero ℚ 1,
   rigidity_sylvesterHadamard_zero ℝ 2,
   rigidity_sylvesterHadamard_zero (ZMod 2) 3⟩

/-! ### Tight equality at `n = 2, r = 1` over `ℚ` and `ℝ` -/

example : (sylvesterHadamard ℚ 1).rigidity 1 = 1 := by
  refine le_antisymm ?_ ?_
  · let B : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, 1]
    have hBeq : B = vecMulVec ![1, 1] ![1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B, vecMulVec_apply]
    have hBrank : B.rank ≤ 1 := hBeq ▸ rank_vecMulVec_le _ _
    refine (rigidity_le hBrank).trans ?_
    have hfilt :
        (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
          sylvesterHadamard ℚ 1 p.1 p.2 ≠ B p.1 p.2) = {(1, 1)} := by
      rw [sylvesterHadamard_one]
      ext ⟨i, j⟩
      (fin_cases i <;> fin_cases j <;> simp [B]); norm_num
    rw [diffCount_eq_card_filter, hfilt, Finset.card_singleton]
  · have h := two_pow_le_four_mul_rigidity_sylvesterHadamard ℚ (k := 1) (r := 1)
      (by omega) (by norm_num)
    omega

example : (sylvesterHadamard ℝ 1).rigidity 1 = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
    have hBeq : B = vecMulVec ![1, 1] ![1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B, vecMulVec_apply]
    have hBrank : B.rank ≤ 1 := hBeq ▸ rank_vecMulVec_le _ _
    refine (rigidity_le hBrank).trans ?_
    have hfilt :
        (Finset.univ.filter fun p : Fin 2 × Fin 2 =>
          sylvesterHadamard ℝ 1 p.1 p.2 ≠ B p.1 p.2) = {(1, 1)} := by
      rw [sylvesterHadamard_one]
      ext ⟨i, j⟩
      (fin_cases i <;> fin_cases j <;> simp [B]); norm_num
    rw [diffCount_eq_card_filter, hfilt, Finset.card_singleton]
  · have h := (isHadamard_sylvesterHadamard ℝ 1).card_sq_le_four_mul_rigidity (r := 1)
      (by omega) (by simp)
    simp only [Fintype.card_fin] at h
    omega

/-! ### Tight equality at `n = 4, r = 1` (`rigidity = 4 > 3`) and `r = 2` (`2 ≤ rigidity ≤ 3`) -/

private theorem sylvesterHadamard_two_eq (R : Type*) [CommRing R] :
    sylvesterHadamard R 2 = !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterHadamard_apply, Finset.prod_range_succ,
      show Nat.testBit 1 0 = true by decide, show Nat.testBit 1 1 = false by decide,
      show Nat.testBit 2 0 = false by decide, show Nat.testBit 2 1 = true by decide,
      show Nat.testBit 3 0 = true by decide, show Nat.testBit 3 1 = true by decide]

-- `vecMulVec ![1, 1, 1, -1] ![1, 1, 1, -1]` matches `sylvesterHadamard ℚ 2` in 12 of 16 entries,
-- proving that `n² / (4r) = 4` is tight at `n = 4, r = 1` as well.
example : (sylvesterHadamard ℚ 2).rigidity 1 = 4 := by
  refine le_antisymm ?_ ?_
  · let u : Fin 4 → ℚ := ![1, 1, 1, -1]
    let B : Matrix (Fin 4) (Fin 4) ℚ := vecMulVec u u
    have hBrank : B.rank ≤ 1 := rank_vecMulVec_le u u
    refine (rigidity_le hBrank).trans ?_
    have hfilt :
        (Finset.univ.filter fun p : Fin 4 × Fin 4 =>
          sylvesterHadamard ℚ 2 p.1 p.2 ≠ B p.1 p.2) = {(0, 3), (1, 1), (2, 2), (3, 0)} := by
      rw [sylvesterHadamard_two_eq]
      ext ⟨i, j⟩
      (fin_cases i <;> fin_cases j <;> simp [B, u]) <;> norm_num
    rw [diffCount_eq_card_filter, hfilt]
    decide
  · have h := (isHadamard_sylvesterHadamard ℚ 2).card_sq_le_four_mul_rigidity_of_trivialStar
      (r := 1) (by omega) (by simp)
    simp only [Fintype.card_fin] at h
    omega

-- At the upper endpoint `2 * r = 4` (`r = 2`), the Hadamard bound gives `2 ≤ rigidity 2`, while
-- an explicit 2-dimensional row space achieves `3` changes (`rigidity 2 ≤ 3 < (4 - 2)²`).
example :
    2 ≤ (sylvesterHadamard ℚ 2).rigidity 2 ∧
    (sylvesterHadamard ℚ 2).rigidity 2 ≤ 3 := by
  refine ⟨?_, ?_⟩
  · have h := two_pow_le_four_mul_rigidity_sylvesterHadamard ℚ (k := 2) (r := 2)
      (by omega) (by norm_num)
    omega
  · let C : Matrix (Fin 4) (Fin 2) ℚ := !![1, 0; 0, 1; 0, -1; 0, 1]
    let D : Matrix (Fin 2) (Fin 4) ℚ := !![1, 1, 1, 1; 1, -1, 1, 1]
    let B : Matrix (Fin 4) (Fin 4) ℚ := C * D
    have hrank : B.rank ≤ 2 :=
      (rank_mul_le_left C D).trans ((rank_le_card_width C).trans_eq (Fintype.card_fin 2))
    refine (rigidity_le hrank).trans ?_
    have hfilt :
        (Finset.univ.filter fun p : Fin 4 × Fin 4 =>
          sylvesterHadamard ℚ 2 p.1 p.2 ≠ B p.1 p.2) = {(1, 3), (2, 0), (3, 2)} := by
      rw [sylvesterHadamard_two_eq]
      ext ⟨i, j⟩
      (fin_cases i <;> fin_cases j <;> simp [B, C, D]) <;> norm_num
    rw [diffCount_eq_card_filter, hfilt]
    decide

/-! ### `n = 8` (`k = 3`), non-power-of-two `r = 3`, and odd characteristic `ZMod 3` -/

-- At `n = 8, r = 3`, `64 ≤ 12 * rigidity 3` forces `rigidity 3 ≥ ⌈64 / 12⌉ = 6 > ⌊64 / 12⌋`.
example : 16 ≤ (sylvesterHadamard ℚ 3).rigidity 1 ∧
    8 ≤ (sylvesterHadamard ℚ 3).rigidity 2 ∧
    6 ≤ (sylvesterHadamard ℚ 3).rigidity 3 ∧
    4 ≤ (sylvesterHadamard ℝ 3).rigidity 4 := by
  have h1 := two_pow_le_four_mul_rigidity_sylvesterHadamard ℚ (k := 3) (r := 1)
    (by omega) (by norm_num)
  have h2 := two_pow_le_four_mul_rigidity_sylvesterHadamard ℚ (k := 3) (r := 2)
    (by omega) (by norm_num)
  have h3 := two_pow_le_four_mul_rigidity_sylvesterHadamard ℚ (k := 3) (r := 3)
    (by omega) (by norm_num)
  have h4 := two_pow_le_four_mul_rigidity_sylvesterHadamard ℝ (k := 3) (r := 4)
    (by omega) (by norm_num)
  omega

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Over `ZMod 3` (characteristic `3 ≠ 2`), Midrijānis's block-tiling theorem applies at `r = 1, 2`.
example : 16 ≤ (sylvesterHadamard (ZMod 3) 3).rigidity 1 ∧
    8 ≤ (sylvesterHadamard (ZMod 3) 3).rigidity 2 := by
  have hchar : (2 : ZMod 3) ≠ 0 := by decide
  have h0 := two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow (K := ZMod 3) hchar
    (k := 3) (t := 0) (by omega)
  have h1 := two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow (K := ZMod 3) hchar
    (k := 3) (t := 1) (by omega)
  norm_num at h0 h1
  exact ⟨by omega, by omega⟩

/-! ### Asymmetric complex Hadamard boundary witness (`H * Hᵀ ≠ n • 1` while `H * Hᴴ = n • 1`) -/

private noncomputable def asymComplexHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.I; 1, -Complex.I]

-- `asymComplexHadamard` is not symmetric and fails un-conjugated `H * Hᵀ = 2 • 1`, yet satisfies
-- `Matrix.IsHadamard` under `conjTranspose` and therefore has rank `2` and
-- `4 ≤ (H ⊗ₖ H).rigidity 1`.
example : asymComplexHadamard * asymComplexHadamardᵀ ≠ (2 : ℂ) • 1 ∧
    asymComplexHadamard.IsHadamard ∧
    asymComplexHadamard.rank = 2 ∧
    4 ≤ (asymComplexHadamard ⊗ₖ asymComplexHadamard).rigidity 1 := by
  have hnot_trans : asymComplexHadamard * asymComplexHadamardᵀ ≠ (2 : ℂ) • 1 := by
    intro h
    have h00 := congr_fun₂ h 0 0
    simp [asymComplexHadamard, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hHad : asymComplexHadamard.IsHadamard := by
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [asymComplexHadamard, Unitary.mem_iff]
    · ext i j
      (fin_cases i <;> fin_cases j <;>
        simp [asymComplexHadamard, Matrix.mul_apply, Fin.sum_univ_two]) <;> norm_num
    · ext i j
      (fin_cases i <;> fin_cases j <;>
        simp [asymComplexHadamard, Matrix.mul_apply, Fin.sum_univ_two]) <;> ring
  have hrank : asymComplexHadamard.rank = 2 := by
    simpa using hHad.rank_eq_card (by norm_num)
  have hKron : (asymComplexHadamard ⊗ₖ asymComplexHadamard).IsHadamard := hHad.kronecker hHad
  have hrig := hKron.card_sq_le_four_mul_rigidity (r := 1) (by omega) (by simp)
  simp only [Fintype.card_prod, Fintype.card_fin] at hrig
  exact ⟨hnot_trans, hHad, hrank, by omega⟩

/-! ### Boundary counterexamples showing hypotheses cannot be omitted -/

-- 1. `2 * r ≤ n` is sharp: at `n = 4, r = 3` (`2 * r = 6 > 4`), changing only entry `(0, 0)` from
-- `1` to `-3` makes row `0` equal `-(row 1 + row 2 + row 3)`, so `rigidity 3 = 1` and
-- `4 * 3 * rigidity 3 = 12 < 16 = 4 ^ 2`.
example :
    (sylvesterHadamard ℚ 2).rigidity 3 = 1 ∧
    4 * 3 * (sylvesterHadamard ℚ 2).rigidity 3 < 2 ^ (2 * 2) := by
  have h1 : (sylvesterHadamard ℚ 2).rigidity 3 = 1 := by
    refine le_antisymm ?_ ?_
    · let C : Matrix (Fin 4) (Fin 3) ℚ := !![-1, -1, -1; 1, 0, 0; 0, 1, 0; 0, 0, 1]
      let D : Matrix (Fin 3) (Fin 4) ℚ := !![1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]
      let B : Matrix (Fin 4) (Fin 4) ℚ := C * D
      have hrank : B.rank ≤ 3 :=
        (rank_mul_le_left C D).trans ((rank_le_card_width C).trans_eq (Fintype.card_fin 3))
      refine (rigidity_le hrank).trans ?_
      have hfilt :
          (Finset.univ.filter fun p : Fin 4 × Fin 4 =>
            sylvesterHadamard ℚ 2 p.1 p.2 ≠ B p.1 p.2) = {(0, 0)} := by
        rw [sylvesterHadamard_two_eq]
        ext ⟨i, j⟩
        (fin_cases i <;> fin_cases j <;> simp [B, C, D]); norm_num
      rw [diffCount_eq_card_filter, hfilt, Finset.card_singleton]
    · have hrank : (sylvesterHadamard ℚ 2).rank = 4 := by
        simpa using rank_sylvesterHadamard_of_two_ne_zero (K := ℚ) two_ne_zero 2
      have hlow := (sylvesterHadamard ℚ 2).rank_sub_le_rigidity 3
      omega
  exact ⟨h1, by omega⟩

-- 2. `(2 : K) ≠ 0` is sharp: in characteristic two (`ZMod 2`), `sylvesterHadamard (ZMod 2) 2` is
-- the all-ones matrix of rank `1`, so its `1`-rigidity is `0` rather than `≥ 4`.
example : (sylvesterHadamard (ZMod 2) 2).rigidity 1 = 0 := by
  let B : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    !![1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, 1]
  have heq : sylvesterHadamard (ZMod 2) 2 = B := by
    rw [sylvesterHadamard_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hBeq : B = vecMulVec ![1, 1, 1, 1] ![1, 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, vecMulVec_apply]
  rw [rigidity_eq_zero_iff, heq, hBeq]
  exact rank_vecMulVec_le _ _

-- 3. `IsHadamard` orthogonality cannot be weakened to `±1` entries alone: the `4 × 4` rational
-- all-ones matrix has unitary `±1` entries (`∀ i j, J i j ∈ unitary ℚ`) yet `¬ J.IsHadamard` and
-- `J.rigidity 1 = 0`.
example :
    let J : Matrix (Fin 4) (Fin 4) ℚ := !![1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, 1]
    (∀ i j, J i j ∈ unitary ℚ) ∧ ¬ J.IsHadamard ∧ J.rigidity 1 = 0 := by
  intro J
  have hJeq : J = vecMulVec ![1, 1, 1, 1] ![1, 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, vecMulVec_apply]
  refine ⟨fun i j => ?_, fun hJ => ?_,
    rigidity_eq_zero_iff.mpr (hJeq ▸ rank_vecMulVec_le _ _)⟩
  · fin_cases i <;> fin_cases j <;> simp [J]
  · have h01 := congr_fun₂ hJ.mul_conjTranspose 0 1
    simp [J, Matrix.mul_apply, Fin.sum_univ_four] at h01
    norm_num at h01

end CslibFrontierTests.MatrixRigidityHadamard
