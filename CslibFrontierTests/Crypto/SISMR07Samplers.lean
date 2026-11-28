/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.SIS.MR07Samplers
import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for `CslibFrontier/Crypto/Computational/SIS/MR07Samplers.lean`

Ordinary `module` client verifying the strict-PPT lattice samplers and typed-law bridges on the
non-diagonal, non-symmetric `2 × 2` lattice pair `B = [[1, 1], [0, 2]]` (`det B = 2`, `B ≠ Bᵀ`)
and `S = [[2, 3], [0, 4]]` (`det S = 8`, `S = B * [[2, 1], [0, 2]]`, quotient index `D = 4`):

1. Basis-orientation checks distinguishing `B` from `Bᵀ` for both `quotientReduceInt` and
   `gridReduceInt` (proved across the `module` boundary from `quotientIndex_eq_natAbs_div_det`,
   `quotientReduceInt_spec`, and `gridReduceInt_spec`).
2. End-to-end strict-PPT typed-law `CloseTo` client reaching
   `PMF.uniformOfFintype (SublatticeQuot B S)` with explicit `< 1` bound `1 / 16` and lossless
   support recovery (`mem_support_sampleQuotientModS_exists_sublatticeQuot`).
3. End-to-end strict-PPT typed-law `CloseTo` client on nonzero rational target `[1/3, -1/2]`
   reaching `MR07.idealGridSample` on `GridRep B 2 × intLattice B` with explicit `< 1` bound
   `ENNReal.ofReal (1 / 2)` and lossless support recovery
   (`mem_support_sampleGridGaussian_exists_gridRep`).
4. Explicit `IsPPTOn` runtime certificates for both `sampleGridGaussian` and `sampleQuotientModS`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SISMR07Samplers

open Module ProbabilityTheory Cslib Cslib.Crypto.SIS.MR07 Cslib.Probability Cslib.LinearAlgebra
open ZLattice
open scoped ENNReal RealInnerProductSpace _root_.Matrix

private def testBTab : IntTable := ⟨2, 2, [[1, 1], [0, 2]]⟩
private def testBTTab : IntTable := ⟨2, 2, [[1, 0], [1, 2]]⟩
private def testSTab : IntTable := ⟨2, 2, [[2, 3], [0, 4]]⟩

private def testB : Matrix (Fin 2) (Fin 2) ℤ := ![![1, 1], ![0, 2]]
private def testS : Matrix (Fin 2) (Fin 2) ℤ := ![![2, 3], ![0, 4]]

private theorem testB_det_ne_zero : testB.det ≠ 0 := by decide
private theorem testS_det_ne_zero : testS.det ≠ 0 := by decide

private theorem testBTab_entry (i j : Fin 2) : testBTab.entry i.val j.val = testB i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem testBTTab_entry (i j : Fin 2) : testBTTab.entry i.val j.val = testBᵀ i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem testSTab_entry (i j : Fin 2) : testSTab.entry i.val j.val = testS i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem testBTab_wellFormed : testBTab.WellFormed := by
  refine ⟨rfl, fun row hrow => ?_⟩
  simp only [testBTab, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> rfl

private theorem testSTab_wellFormed : testSTab.WellFormed := by
  refine ⟨rfl, fun row hrow => ?_⟩
  simp only [testSTab, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> rfl

private theorem test_sublattice_le : intLattice testS ≤ intLattice testB := by
  rw [intLattice, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change intCol testS j ∈ intLattice testB
  rw [mem_intLattice_iff]
  fin_cases j
  · refine ⟨![2, 0], ?_⟩
    ext i; fin_cases i <;> simp [intCol, testS, testB, Matrix.mulVec, dotProduct]
  · refine ⟨![1, 2], ?_⟩
    ext i; fin_cases i <;> simp [intCol, testS, testB, Matrix.mulVec, dotProduct]

private theorem testS_real_inv :
    (testS.map (Int.cast : ℤ → ℝ))⁻¹ = !![(1 / 2 : ℝ), -3 / 8; 0, 1 / 4] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [testS, Matrix.mul_apply, Matrix.map]; norm_num

private theorem testB_real_inv :
    (testB.map (Int.cast : ℤ → ℝ))⁻¹ = !![(1 : ℝ), -1 / 2; 0, 1 / 2] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [testB, Matrix.mul_apply, Matrix.map]; norm_num

private theorem testBT_real_inv :
    (testBᵀ.map (Int.cast : ℤ → ℝ))⁻¹ = !![(1 : ℝ), 0; -1 / 2, 1 / 2] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [testB, Matrix.mul_apply, Matrix.map, Matrix.transpose]
  norm_num

private theorem list_eq_pair_of_getD {l : List ℤ} (hlen : l.length = 2) {a b : ℤ}
    (h0 : l.getD 0 0 = a) (h1 : l.getD 1 0 = b) : l = [a, b] := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi _
  have hi' : i < 2 := by simpa [hlen] using hi
  have hi_l : i < l.length := hlen.symm ▸ hi'
  have hg : l[i]'hi_l = l.getD i 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_l, Option.getD_some]
  interval_cases i
  · simpa [hg] using h0
  · simpa [hg] using h1

private theorem floor_of_bounds {x : ℝ} {z : ℤ} (hlo : (z : ℝ) ≤ x) (hhi : x < (z : ℝ) + 1) :
    Int.floor x = z :=
  Int.floor_eq_iff.mpr ⟨hlo, hhi⟩

private theorem quotientReduceInt_pair_eq (TB : IntTable) (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hBrows : TB.numRows = 2) (hBcols : TB.numCols = 2)
    (hBmat : ∀ i j : Fin 2, TB.entry i.val j.val = B i j) (x : List ℕ) (a b : ℤ)
    (hcoords : ∀ i : Fin 2,
      modParallelepiped testS
        (WithLp.toLp 2 fun k : Fin 2 =>
          ((B *ᵥ fun j : Fin 2 => (x.getD j.val 0 : ℤ)) k : ℝ)) i =
        ((![a, b] i : ℤ) : ℝ)) :
    quotientReduceInt 2 TB testSTab x = [a, b] := by
  obtain ⟨hlen, hvec⟩ := quotientReduceInt_spec TB testSTab B testS
    hBrows hBcols hBmat rfl rfl testSTab_entry testS_det_ne_zero x
  refine list_eq_pair_of_getD hlen ?_ ?_
  · exact Int.cast_injective
      ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hvec).trans (hcoords 0))
  · exact Int.cast_injective
      ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hvec).trans (hcoords 1))

private theorem gridReduceInt_pair_eq (TB : IntTable) (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hBrows : TB.numRows = 2) (hBcols : TB.numCols = 2)
    (hBmat : ∀ i j : Fin 2, TB.entry i.val j.val = B i j) (hB : B.det ≠ 0)
    (r' : List ℤ) (u0 u1 y0 y1 : ℤ)
    (hu_eval : ∀ i : Fin 2,
      modParallelepiped B
        (-((3 : ℝ)⁻¹ • WithLp.toLp 2 fun k : Fin 2 => (r'.getD k.val 0 : ℝ))) i =
        (3 : ℝ)⁻¹ * ((![u0, u1] i : ℤ) : ℝ))
    (hy_eval : ∀ i : Fin 2,
      (3 : ℝ)⁻¹ * (r'.getD i.val 0 : ℝ) + (3 : ℝ)⁻¹ * ((![u0, u1] i : ℤ) : ℝ) =
        ((![y0, y1] i : ℤ) : ℝ)) :
    gridReduceInt 2 3 TB r' = ([u0, u1], [y0, y1]) := by
  obtain ⟨hl1, hl2, hu, hy, _⟩ :=
    gridReduceInt_spec TB B hBrows hBcols hBmat hB (q := 3) (by decide) r'
  have hu_coord : ∀ i : Fin 2, (gridReduceInt 2 3 TB r').1.getD i.val 0 = ![u0, u1] i := by
    intro i
    have h := (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hu).trans (hu_eval i)
    have hcast : ((gridReduceInt 2 3 TB r').1.getD i.val 0 : ℝ) = ((![u0, u1] i : ℤ) : ℝ) := by
      change (3 : ℝ)⁻¹ * ((gridReduceInt 2 3 TB r').1.getD i.val 0 : ℝ) = _ at h
      linarith
    exact Int.cast_injective hcast
  have hy_coord : ∀ i : Fin 2, (gridReduceInt 2 3 TB r').2.getD i.val 0 = ![y0, y1] i := by
    intro i
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) hy
    change ((gridReduceInt 2 3 TB r').2.getD i.val 0 : ℝ) =
      (3 : ℝ)⁻¹ * (r'.getD i.val 0 : ℝ) +
        (3 : ℝ)⁻¹ * ((gridReduceInt 2 3 TB r').1.getD i.val 0 : ℝ) at h
    rw [hu_coord i, hy_eval i] at h
    exact Int.cast_injective h
  exact Prod.ext (list_eq_pair_of_getD hl1 (hu_coord 0) (hu_coord 1))
    (list_eq_pair_of_getD hl2 (hy_coord 0) (hy_coord 1))

/-! ### 1. Non-diagonal basis-orientation tests (`B` vs `Bᵀ`) -/

example : testB ≠ testBᵀ := by decide

/-- Explicit checked quotient test distinguishing `B` from `Bᵀ`: `B *ᵥ [0, 1] = [1, 2]` reduces
mod `P(S)` to `[3, 2]` (whereas `Bᵀ *ᵥ [0, 1] = [0, 2]` reduces to `[2, 2]`), and
`quotientIndex testBTab testSTab = 4`. -/
example :
    quotientIndex testBTab testSTab = 4 ∧
    quotientReduceInt 2 testBTab testSTab [0, 1] = [3, 2] ∧
    quotientReduceInt 2 testBTTab testSTab [0, 1] = [2, 2] := by
  have hD : quotientIndex testBTab testSTab = 4 := by
    rw [quotientIndex_eq_natAbs_div_det testBTab testSTab testB testS
      testBTab_wellFormed testSTab_wellFormed rfl testBTab_entry rfl testSTab_entry
      testB_det_ne_zero test_sublattice_le]
    decide
  have hfl1 : Int.floor (-1 / 4 : ℝ) = -1 := floor_of_bounds (by norm_num) (by norm_num)
  have hfl2 : Int.floor (-3 / 4 : ℝ) = -1 := floor_of_bounds (by norm_num) (by norm_num)
  have hfl3 : Int.floor (1 / 2 : ℝ) = 0 := floor_of_bounds (by norm_num) (by norm_num)
  have hB_red : quotientReduceInt 2 testBTab testSTab [0, 1] = [3, 2] := by
    refine quotientReduceInt_pair_eq testBTab testB rfl rfl testBTab_entry [0, 1] 3 2 fun i => ?_
    fin_cases i <;> (
      unfold modParallelepiped; dsimp only; rw [testS_real_inv]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, testB, testS, Matrix.map,
        List.getD, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num [hfl1, hfl3])
  have hBT_red : quotientReduceInt 2 testBTTab testSTab [0, 1] = [2, 2] := by
    refine quotientReduceInt_pair_eq testBTTab testBᵀ rfl rfl testBTTab_entry
      [0, 1] 2 2 fun i => ?_
    fin_cases i <;> (
      unfold modParallelepiped; dsimp only; rw [testS_real_inv]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, testB, testS, Matrix.transpose,
        Matrix.map, List.getD, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num [hfl2, hfl3])
  exact ⟨hD, hB_red, hBT_red⟩

/-- Explicit checked grid-reduction test distinguishing `B` from `Bᵀ` at `q = 3, r' = [1, 1]`:
`B⁻¹ *ᵥ (-1/3, -1/3) = (-1/6, -1/6)` yields `([5, 5], [2, 2])`, whereas
`(Bᵀ)⁻¹ *ᵥ (-1/3, -1/3) = (-1/3, 0)` yields `([2, 2], [1, 1])`. -/
example :
    gridReduceInt 2 3 testBTab [1, 1] = ([5, 5], [2, 2]) ∧
    gridReduceInt 2 3 testBTTab [1, 1] = ([2, 2], [1, 1]) := by
  have hfl6 : Int.floor (-1 / 6 : ℝ) = -1 := floor_of_bounds (by norm_num) (by norm_num)
  have hfl3 : Int.floor (-1 / 3 : ℝ) = -1 := floor_of_bounds (by norm_num) (by norm_num)
  have hB_grid : gridReduceInt 2 3 testBTab [1, 1] = ([5, 5], [2, 2]) := by
    refine gridReduceInt_pair_eq testBTab testB rfl rfl testBTab_entry testB_det_ne_zero
      [1, 1] 5 5 2 2 (fun i => ?_) (fun i => by fin_cases i <;> norm_num [List.getD])
    fin_cases i <;> (
      unfold modParallelepiped; dsimp only; rw [testB_real_inv]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, testB, Matrix.map, List.getD,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.smul_apply,
        PiLp.neg_apply, smul_eq_mul]
      norm_num [hfl6])
  have hBT_det : testBᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact testB_det_ne_zero
  have hBT_grid : gridReduceInt 2 3 testBTTab [1, 1] = ([2, 2], [1, 1]) := by
    refine gridReduceInt_pair_eq testBTTab testBᵀ rfl rfl testBTTab_entry hBT_det
      [1, 1] 2 2 1 1 (fun i => ?_) (fun i => by fin_cases i <;> norm_num [List.getD])
    fin_cases i <;> (
      unfold modParallelepiped; dsimp only; rw [testBT_real_inv]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, testB, Matrix.transpose,
        Matrix.map, List.getD, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      norm_num [hfl3])
  exact ⟨hB_grid, hBT_grid⟩

/-! ### 2. End-to-end typed-law `CloseTo` client: quotient sampler ↔ `SublatticeQuot` -/

private def concreteQuotInput : QuotientSampleInput :=
  { dim := 2, basis := testBTab, sublattice := testSTab, extraBits := 5 }

example :
    CloseTo ((ProbComp.eval (sampleQuotientModS concreteQuotInput)).map
        (decodeSublatticeQuot testB testS))
      (PMF.uniformOfFintype (SublatticeQuot testB testS)) (1 / 16 : ℝ≥0∞) ∧
    (∀ v ∈ (ProbComp.eval (sampleQuotientModS concreteQuotInput)).support,
      ∃ qv : SublatticeQuot testB testS,
        v = sublatticeQuotToList qv ∧ decodeSublatticeQuot testB testS v = qv) := by
  refine ⟨?_, fun v hv => mem_support_sampleQuotientModS_exists_sublatticeQuot concreteQuotInput
    testB testS rfl rfl testBTab_entry rfl rfl testSTab_entry testS_det_ne_zero test_sublattice_le
    hv⟩
  have h := closeTo_eval_sampleQuotientModS_uniform concreteQuotInput testB testS
    testBTab_wellFormed testSTab_wellFormed rfl rfl testBTab_entry rfl rfl testSTab_entry
    testB_det_ne_zero testS_det_ne_zero test_sublattice_le
  have hbound : ((2 : ℝ≥0∞) / 2 ^ 5) = (1 / 16 : ℝ≥0∞) := by
    rw [show (2 : ℝ≥0∞) ^ 5 = 2 * 16 by norm_num]
    conv_lhs => arg 1; rw [← mul_one (2 : ℝ≥0∞)]
    rw [ENNReal.mul_div_mul_left 1 16 (by norm_num) (by simp)]
  exact hbound ▸ h

/-! ### 3. End-to-end typed-law `CloseTo` client: grid sampler ↔ `MR07.idealGridSample` -/

private theorem exp_neg_nat_mul_log_two (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log 2)) = ((2 : ℝ) ^ k)⁻¹ := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]

private noncomputable abbrev D1 := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) intLatticeReal

private instance : DiscreteTopology D1 := ZLattice.discreteTopology_dualSubmodule intLatticeReal
private instance : IsZLattice ℝ D1 := ZLattice.isZLattice_dualSubmodule intLatticeReal

private theorem dual_small_two : ZLattice.gaussianMass D1 (1 / 2) 0 - 1 ≤ 1 / 2 := by
  have hexp : Real.exp (-3 * Real.pi) < 1 / 16 := by
    have hlt := Real.exp_lt_exp.mpr
      (show -3 * Real.pi < -((4 : ℕ) * Real.log 2) by
        push_cast; linarith [Real.log_two_lt_d9, Real.pi_gt_three])
    rw [exp_neg_nat_mul_log_two 4] at hlt
    linarith
  exact ZLattice.gaussianMass_dual_sub_one_le_of_gap intLatticeReal 2 (by norm_num)
    1 (by norm_num) (fun _ hw => ZLattice.one_le_norm_of_mem_dualSubmodule_intLatticeReal hw)
    (1 / 2) (by norm_num) (by
      rw [finrank_self, pow_one, show -3 * Real.pi * (2 : ℝ) ^ 2 * 1 ^ 2 / 4 = -3 * Real.pi by
        ring]
      linarith)

private theorem concrete_grid_err_le_half :
    ((2 : ℕ) : ℝ) *
      ((1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340 +
        (8 * (2 : ℕ) + 24 : ℝ) / (2 : ℝ) ^ 10 +
        (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) * (2 * Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2))) ≤
      1 / 2 := by
  have ht1 : (1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340 ≤ 1 / 8 := by
    have hbase : 1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ)) ≤ Real.exp (-1 / 160) := by
      have := Real.add_one_le_exp (-1 / 160 : ℝ); push_cast; linarith
    have hpow := pow_le_pow_left₀ (by norm_num) hbase 340
    rw [← Real.exp_nat_mul] at hpow
    have hlt := Real.exp_lt_exp.mpr
      (show (340 : ℕ) * (-1 / 160 : ℝ) < -((3 : ℕ) * Real.log 2) by
        push_cast; linarith [Real.log_two_lt_d9])
    rw [exp_neg_nat_mul_log_two 3] at hlt
    exact hpow.trans (hlt.le.trans (by norm_num))
  have ht2 : (8 * (2 : ℕ) + 24 : ℝ) / (2 : ℝ) ^ 10 ≤ 1 / 16 := by norm_num
  have ht3 : (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) *
      (2 * Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2)) ≤ 1 / 16 := by
    have hlt := Real.exp_lt_exp.mpr
      (show -Real.pi * ((2 : ℕ) : ℝ) ^ 2 < -((7 : ℕ) * Real.log 2) by
        push_cast; linarith [Real.log_two_lt_d9, Real.pi_gt_three])
    rw [exp_neg_nat_mul_log_two 7] at hlt
    norm_num at hlt ⊢; linarith
  have hsum := (add_le_add (add_le_add ht1 ht2) ht3).trans
    (by norm_num : (1 / 8 : ℝ) + 1 / 16 + 1 / 16 ≤ 1 / 4)
  exact (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ ((2 : ℕ) : ℝ))).trans
    (by norm_num)

private def concreteGridInput : GridSampleInput :=
  { dim := 2, modulus := 2, basis := testBTab, sSq := 1, target := [1 / 3, -1 / 2],
    tail := 2, prec := 10, maxTrials := 340 }

example :
    let tVec : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 fun i : Fin 2 => (concreteGridInput.target.getD i.val 0 : ℝ)
    CloseTo ((ProbComp.eval (sampleGridGaussian concreteGridInput)).map (decodeGridPair testB 2))
      (idealGridSample testB testB_det_ne_zero 2 (by norm_num) 1 (by norm_num) tVec)
      (ENNReal.ofReal (1 / 2)) ∧
    (∀ p ∈ (ProbComp.eval (sampleGridGaussian concreteGridInput)).support,
      ∃ gy : GridRep testB 2 × intLattice testB,
        p = gridPairToLists gy ∧ decodeGridPair testB 2 p = gy) := by
  intro tVec
  refine ⟨?_, fun p hp => mem_support_sampleGridGaussian_exists_gridRep concreteGridInput testB
    rfl rfl testBTab_entry testB_det_ne_zero (by decide) hp⟩
  have hη : ZLattice.smoothingParameter intLatticeReal (1 / 2) ≤ 2 :=
    ZLattice.smoothingParameter_le_of_dual_mass_le intLatticeReal (by norm_num) dual_small_two
  have hsqrt : Real.sqrt ((concreteGridInput.sSq : ℚ) : ℝ) = 1 := by simp [concreteGridInput]
  have hqs : (concreteGridInput.modulus : ℝ) * Real.sqrt ((concreteGridInput.sSq : ℚ) : ℝ) = 2 := by
    rw [hsqrt]; simp [concreteGridInput]
  have h := closeTo_eval_sampleGridGaussian_idealGridSample_of_smoothingParameter_le
    concreteGridInput testB rfl rfl testBTab_entry testB_det_ne_zero
    (by decide : (0 : ℚ) < 1) (by decide : 0 < 2)
    (by rw [hqs]; norm_num) (by decide : 1 ≤ 2)
    (ε := 1 / 2) (by norm_num) (by norm_num) (by rw [hqs]; exact hη)
    (by decide : 8 * (2 * 2 + 6) ≤ 2 ^ 10)
  have htarget_eq :
      idealGridSample testB testB_det_ne_zero concreteGridInput.modulus (by decide)
        (Real.sqrt ((concreteGridInput.sSq : ℚ) : ℝ)) (by positivity) tVec =
      idealGridSample testB testB_det_ne_zero 2 (by norm_num) 1 (by norm_num) tVec := by
    change idealGridSample testB testB_det_ne_zero 2 (by decide)
      (Real.sqrt ((concreteGridInput.sSq : ℚ) : ℝ)) (by positivity) tVec = _
    congr 1
  have h' : CloseTo
      ((ProbComp.eval (sampleGridGaussian concreteGridInput)).map
        (decodeGridPair testB concreteGridInput.modulus))
      (idealGridSample testB testB_det_ne_zero concreteGridInput.modulus (by decide)
        (Real.sqrt ((concreteGridInput.sSq : ℚ) : ℝ)) (by positivity) tVec)
      (ENNReal.ofReal ((2 : ℕ) *
        ((1 - 1 / (16 * (2 * (2 : ℕ) + 6 : ℝ))) ^ 340
          + (8 * (2 : ℕ) + 24 : ℝ) / (2 : ℝ) ^ 10
          + (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) *
            (2 * Real.exp (-Real.pi * ((2 : ℕ) : ℝ) ^ 2))))) := h
  rw [htarget_eq] at h'
  exact h'.mono (ENNReal.ofReal_le_ofReal concrete_grid_err_le_half)

/-! ### 4. Strict-PPT runtime certificates -/

example : IsPPTOn GridSampleInput.enc
    (Turing.MultiTapeTM.encPair
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin)
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin))
    sampleGridGaussian :=
  isPPTOn_sampleGridGaussian

example : IsPPTOn QuotientSampleInput.enc
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin)
    sampleQuotientModS :=
  isPPTOn_sampleQuotientModS

end CslibFrontierTests.Crypto.SISMR07Samplers
