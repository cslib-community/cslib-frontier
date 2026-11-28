/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.SpectralCut
public import CslibFrontier.Probability.PMF
import CslibFrontier.Foundations.Quantum.Orthogonalization

/-!
# The projectivity defect on spectral cuts

Compression of a measurement creates a defect equal to the mass lost across the cut,
in addition to the original defect on the retained coordinates. This is the defect
estimate used to round the compressed effects in [Vidick, Theorem 3.1][Vidick2022].
-/

public section

open Matrix Finset
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

namespace Cslib.Quantum.Measurement

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

local notation "Cuts" => {s : Finset ι // Finset.Nonempty s}

private abbrev CutBasis (s : Finset ι) := {i : ι // i ∈ s}

private abbrev cutEmbedding (s : Finset ι) : CutBasis s ↪ ι := Function.Embedding.subtype (· ∈ s)

private noncomputable def squareMass (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) : ℝ :=
  ∑ a, ‖M.effect a i j‖ ^ 2

private theorem squareMass_comm (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) :
    squareMass M i j = squareMass M j i := by
  simp only [squareMass, M.norm_effect_entry_swap _ i j]

private theorem squareMass_nonneg (M : Measurement α (Matrix ι ι ℂ)) (i j : ι) :
    0 ≤ squareMass M i j := sum_nonneg fun a _ => sq_nonneg ‖M.effect a i j‖

private theorem sum_squareMass_col_le_one (M : Measurement α (Matrix ι ι ℂ)) (j : ι) :
    ∑ i, squareMass M i j ≤ 1 := by
  simp_rw [squareMass_comm M _ j]
  unfold squareMass
  rw [sum_comm]
  exact M.sum_norm_effect_row_sq_le_one j

private noncomputable def leakage (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) : ℝ :=
  ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), squareMass M i j

private theorem leakage_eq_commutator (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) :
    let P := diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ a, ‖M.effect a * P - P * M.effect a‖ ^ 2) = 2 * leakage M s := by
  intro P
  have hent (a : α) (i j : ι) :
      ‖(M.effect a * P - P * M.effect a) i j‖ ^ 2 =
        (if i ∈ s ∧ j ∉ s then ‖M.effect a i j‖ ^ 2 else 0) +
        (if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0) := by
    change ‖(M.effect a * P) i j - (P * M.effect a) i j‖ ^ 2 = _
    dsimp only [P]
    rw [mul_diagonal, diagonal_mul]
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [hi, hj]
  have hsplit (a : α) :
      ‖M.effect a * P - P * M.effect a‖ ^ 2 =
        2 * ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum]
    simp_rw [hent, sum_add_distrib]
    have hswap :
        (∑ i, ∑ j, if i ∈ s ∧ j ∉ s then ‖M.effect a i j‖ ^ 2 else 0) =
          ∑ j, ∑ i, if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0 := by
      refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
      rw [M.norm_effect_entry_swap a j i]
    rw [hswap, sum_comm (f := fun i j => if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0)]
    have hf :
        (∑ j, ∑ i, if j ∈ s ∧ i ∉ s then ‖M.effect a i j‖ ^ 2 else 0) =
          ∑ j ∈ s, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2 := by
      rw [← show (univ.filter (· ∈ s) : Finset ι) = s by ext; simp, sum_filter]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_filter]
      by_cases hj : j ∈ s <;> simp [hj]
    rw [hf]
    ring
  simp_rw [hsplit, ← mul_sum]
  congr 1
  unfold leakage squareMass
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_comm

omit [DecidableEq ι] in
private theorem sum_width_slice (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (f : ι → ℝ) :
    (∑ s : Cuts, diagonalCutWidth d s * ∑ j ∈ s.val, f j) = ∑ j, d j * f j := by
  classical
  calc
    _ = ∑ s : Cuts, ∑ j, (diagonalCutWidth d s * (if j ∈ s.val then 1 else 0)) * f j := by
      refine sum_congr rfl fun s _ => ?_
      rw [← show univ.filter (· ∈ s.val) = s.val by ext; simp, sum_filter, mul_sum]
      exact sum_congr rfl fun j _ => by by_cases hj : j ∈ s.val <;> simp [hj]
    _ = _ := by
      rw [sum_comm]
      simp_rw [← sum_mul, sum_diagonalCutWidth_mem d _ (hd _)]

private theorem weighted_original_defect_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * squareMass M i j) :
    (∑ j, d j * (1 - ∑ i, squareMass M i j)) ≤ δ := by
  have hamgm (i j : ι) : Real.sqrt (d i) * Real.sqrt (d j) ≤ (d i + d j) / 2 := by
    nlinarith [Real.sq_sqrt (hd i), Real.sq_sqrt (hd j),
      sq_nonneg (Real.sqrt (d i) - Real.sqrt (d j))]
  have hsum : (∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * squareMass M i j) ≤
      ∑ j, d j * ∑ i, squareMass M i j := by
    calc
      _ ≤ ∑ i, ∑ j, ((d i + d j) / 2) * squareMass M i j :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hamgm i j) (squareMass_nonneg M i j)
      _ = _ := by
        simp_rw [div_mul_eq_mul_div, ← sum_div, add_mul, sum_add_distrib]
        have hsym : (∑ i, ∑ j, d i * squareMass M i j) =
            ∑ j, ∑ i, d j * squareMass M i j := by
          exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by
            rw [squareMass_comm M j i]
        rw [hsym, sum_comm (f := fun i j => d j * squareMass M i j)]
        simp only [← mul_sum]
        ring
  simp_rw [mul_sub, mul_one, sum_sub_distrib]
  rw [htrace]
  linarith

private theorem cut_defect_eq (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι) :
    (s.card : ℝ) - ∑ a, ‖(M.principalSubmatrix (cutEmbedding s)).effect a‖ ^ 2 =
      (∑ j ∈ s, (1 - ∑ i, squareMass M i j)) + leakage M s := by
  simp_rw [frobenius_norm_sq_eq_sum, principalSubmatrix_effect_apply]
  change (s.card : ℝ) - (∑ a, ∑ i : CutBasis s, ∑ j : CutBasis s,
    ‖M.effect a i.val j.val‖ ^ 2) = _
  have hmass : (∑ a, ∑ i : CutBasis s, ∑ j : CutBasis s, ‖M.effect a i.val j.val‖ ^ 2) =
      ∑ j ∈ s, ∑ i ∈ s, squareMass M i j := by
    rw [sum_comm]
    simp_rw [sum_comm (f := fun a (j : CutBasis s) => ‖M.effect a _ j.val‖ ^ 2)]
    rw [sum_comm]
    rw [Finset.sum_subtype (F := inferInstanceAs (Fintype (CutBasis s))) s (fun _ => Iff.rfl)]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.sum_subtype (F := inferInstanceAs (Fintype (CutBasis s))) s (fun _ => Iff.rfl)]
    simp only [squareMass]
  rw [hmass]
  unfold leakage
  rw [← sum_add_distrib]
  change (s.card : ℝ) - _ = _
  rw [show (s.card : ℝ) = ∑ _j ∈ s, (1 : ℝ) by simp, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hsplit := sum_filter_add_sum_filter_not univ (· ∈ s) (fun i => squareMass M i j)
  rw [show univ.filter (· ∈ s) = s by ext; simp] at hsplit
  linarith

private theorem sum_width_leakage_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * squareMass M i j) :
    (∑ s : Cuts, diagonalCutWidth d s * leakage M s.val) ≤ Real.sqrt (2 * δ) := by
  have h := M.sum_diagonalCutWidth_norm_commutator_sq_le d hd htrace δ hagree
  simp_rw [leakage_eq_commutator, mul_left_comm _ (2 : ℝ), ← mul_sum] at h
  linarith

/-- Width-weighted defect of the compressed POVMs. The defect on each cut is scaled by its
dimension, so this is the average normalized-trace defect with the spectral probability weights. -/
theorem sum_width_compression_defect_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) *
      ∑ a, ‖M.effect a i j‖ ^ 2) :
    (∑ s : Cuts, diagonalCutWidth d s *
      ((s.val.card : ℝ) -
        ∑ a, ‖(M.principalSubmatrix (Function.Embedding.subtype (· ∈ s.val))).effect a‖ ^ 2)) ≤
      δ + Real.sqrt (2 * δ) := by
  change (∑ s : Cuts, diagonalCutWidth d s * ((s.val.card : ℝ) -
    ∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a‖ ^ 2)) ≤ _
  simp_rw [cut_defect_eq, mul_add, sum_add_distrib]
  rw [sum_width_slice d hd]
  have h₁ := weighted_original_defect_le M d hd htrace δ hagree
  exact add_le_add h₁ (sum_width_leakage_le M d hd htrace δ hagree)

/-- Squared error on the columns kept by a cut, where the smaller matrix is extended by zero. -/
@[expose] noncomputable def cutColumnError (s : Finset ι) (A : Matrix ι ι ℂ)
    (B : Matrix {i : ι // i ∈ s} {i : ι // i ∈ s} ℂ) : ℝ :=
  ∑ j : {i : ι // i ∈ s}, ∑ i, ‖A i j.val - if hi : i ∈ s then B ⟨i, hi⟩ j else 0‖ ^ 2

private theorem sum_cutColumnError_eq (M : Measurement α (Matrix ι ι ℂ)) (s : Finset ι)
    (R : Measurement α (Matrix (CutBasis s) (CutBasis s) ℂ)) :
    (∑ a, cutColumnError s (M.effect a) (R.effect a)) =
      (∑ a, ‖(M.principalSubmatrix (cutEmbedding s)).effect a - R.effect a‖ ^ 2) +
        leakage M s := by
  have hsplit (a : α) (j : CutBasis s) :
      (∑ i, ‖M.effect a i j.val -
        if hi : i ∈ s then R.effect a ⟨i, hi⟩ j else 0‖ ^ 2) =
        (∑ i : CutBasis s, ‖M.effect a i.val j.val - R.effect a i j‖ ^ 2) +
          ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j.val‖ ^ 2 := by
    rw [← sum_filter_add_sum_filter_not univ (· ∈ s)]
    congr 1
    · let f (i : ι) :=
        ‖M.effect a i j.val - if hi : i ∈ s then R.effect a ⟨i, hi⟩ j else 0‖ ^ 2
      calc
        _ = ∑ i ∈ s, f i := sum_congr (by ext; simp) fun _ _ => rfl
        _ = ∑ i : CutBasis s, f i.val := (Finset.sum_coe_sort s f).symm
        _ = _ := sum_congr rfl fun i _ => by simp [f, i.property]
    · exact sum_congr rfl fun i hi => by simp [(mem_filter.mp hi).2]
  unfold cutColumnError
  simp_rw [hsplit, sum_add_distrib, frobenius_norm_sq_eq_sum]
  congr 1
  · refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
      change ‖M.effect a i.val j.val - R.effect a i j‖ ^ 2 =
        ‖(M.principalSubmatrix (cutEmbedding s)).effect a i j - R.effect a i j‖ ^ 2
      rw [principalSubmatrix_effect_apply]
      rfl
  · unfold leakage squareMass
    rw [sum_comm]
    calc
      _ = ∑ j ∈ s, ∑ a, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2 :=
        Finset.sum_coe_sort s (fun j => ∑ a, ∑ i ∈ univ.filter (· ∉ s), ‖M.effect a i j‖ ^ 2)
      _ = _ := sum_congr rfl fun j _ => sum_comm

private theorem exists_cut_rounding (M : Measurement α (Matrix ι ι ℂ))
    (s : Cuts) :
    ∃ R : Measurement α (Matrix (CutBasis s.val) (CutBasis s.val) ℂ),
      R.IsProjective ∧
        (∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a - R.effect a‖ ^ 2) ≤
          9 * ((s.val.card : ℝ) -
            ∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a‖ ^ 2) := by
  have : Nonempty (CutBasis s.val) := by
    obtain ⟨i, hi⟩ := s.property
    exact ⟨⟨i, hi⟩⟩
  let φ : AlgState (Matrix (CutBasis s.val) (CutBasis s.val) ℂ) :=
    AlgState.normalizedMatrixTrace
  let N := M.principalSubmatrix (cutEmbedding s.val)
  obtain ⟨R, hR, hr⟩ := exists_isProjective_sum_norm_sub_sq_le φ N
  refine ⟨R, hR, ?_⟩
  have hnorm (A : Matrix (CutBasis s.val) (CutBasis s.val) ℂ) :
      φ.norm A ^ 2 = ‖A‖ ^ 2 / (s.val.card : ℝ) := by
    simpa only [Fintype.card_coe] using AlgState.norm_sq_normalizedMatrixTrace A
  have htrace (a : α) : (φ (N.effect a * N.effect a)).re =
      ‖N.effect a‖ ^ 2 / (s.val.card : ℝ) := by
    have hsa := (Matrix.nonneg_iff_posSemidef.mp (N.nonneg a)).isHermitian.isSelfAdjoint
    simpa only [AlgState.norm_sq, hsa.star_eq] using hnorm (N.effect a)
  simp_rw [hnorm, htrace, ← sum_div] at hr
  have hc : 0 < (s.val.card : ℝ) := by exact_mod_cast card_pos.mpr s.property
  rw [div_le_iff₀ hc] at hr
  convert hr using 1
  field_simp
  ring

/-- The finite projective rounding estimate in the Schmidt basis for one measurement. -/
theorem exists_projective_cutColumnError_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) *
      ∑ a, ‖M.effect a i j‖ ^ 2) :
    ∃ R : (s : Cuts) → Measurement α
      (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ),
      (∀ s, (R s).IsProjective) ∧
      (∑ s : Cuts, diagonalCutWidth d s *
        ∑ a, cutColumnError s.val (M.effect a) ((R s).effect a)) ≤
        9 * δ + 10 * Real.sqrt (2 * δ) := by
  classical
  choose R hR hb using exists_cut_rounding M
  refine ⟨R, hR, ?_⟩
  simp_rw [sum_cutColumnError_eq, mul_add, sum_add_distrib]
  have hdef := M.sum_width_compression_defect_le d hd htrace δ hagree
  have hleak := sum_width_leakage_le M d hd htrace δ hagree
  have hround :
      (∑ s : Cuts, diagonalCutWidth d s *
        ∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a - (R s).effect a‖ ^ 2) ≤
        9 * (δ + Real.sqrt (2 * δ)) := by
    calc
      _ ≤ ∑ s : Cuts, diagonalCutWidth d s * (9 * ((s.val.card : ℝ) -
          ∑ a, ‖(M.principalSubmatrix (cutEmbedding s.val)).effect a‖ ^ 2)) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hb s) (diagonalCutWidth_nonneg d s)
      _ ≤ _ := by
        simp_rw [mul_left_comm _ (9 : ℝ), ← mul_sum]
        exact mul_le_mul_of_nonneg_left hdef (by norm_num)
  linarith

/-- Agreement with the transposed measurement on a Schmidt-diagonal unit state. -/
@[expose] noncomputable def schmidtAgreement (M : Measurement α (Matrix ι ι ℂ)) (d : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * ∑ a, ‖M.effect a i j‖ ^ 2

theorem schmidtAgreement_le_one (M : Measurement α (Matrix ι ι ℂ)) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) : M.schmidtAgreement d ≤ 1 := by
  have hdef := weighted_original_defect_le M d hd htrace (1 - M.schmidtAgreement d)
    (by rw [sub_sub_cancel]; unfold schmidtAgreement squareMass; rfl)
  have hn : 0 ≤ ∑ j, d j * (1 - ∑ i, squareMass M i j) :=
    sum_nonneg fun j _ => mul_nonneg (hd j) (sub_nonneg.mpr (sum_squareMass_col_le_one M j))
  exact sub_nonneg.mp (hn.trans hdef)

/-- Rounding over a whole question distribution uses the same cuts and their weights
for every question. -/
theorem exists_projective_cutColumnError_average_le {X : Type*} [Fintype X]
    (M : X → Measurement α (Matrix ι ι ℂ)) (ν : PMF X)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) :
    let δ := ∑ x, (ν x).toReal * (1 - (M x).schmidtAgreement d)
    ∃ R : X → (s : Cuts) → Measurement α
      (Matrix {i : ι // i ∈ s.val} {i : ι // i ∈ s.val} ℂ),
      (∀ x s, (R x s).IsProjective) ∧
      (∑ x, (ν x).toReal * ∑ s : Cuts, diagonalCutWidth d s *
        ∑ a, cutColumnError s.val ((M x).effect a) ((R x s).effect a)) ≤
        9 * δ + 10 * Real.sqrt (2 * δ) := by
  classical
  intro δ
  let gap (x : X) := 1 - (M x).schmidtAgreement d
  have hgap (x : X) : 0 ≤ gap x :=
    sub_nonneg.mpr ((M x).schmidtAgreement_le_one d hd htrace)
  have hround (x : X) := (M x).exists_projective_cutColumnError_le d hd htrace (gap x) (by
    change 1 - (1 - (M x).schmidtAgreement d) ≤ _
    rw [sub_sub_cancel]
    unfold schmidtAgreement
    rfl)
  choose R hR hb using hround
  refine ⟨R, hR, ?_⟩
  have havg : (∑ x, (ν x).toReal * Real.sqrt (2 * gap x)) ≤ Real.sqrt (2 * δ) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le (f := fun x => (ν x).toReal)
      (g := fun x => (ν x).toReal * (2 * gap x)) univ
      (fun _ => ENNReal.toReal_nonneg) (fun x => mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (by norm_num) (hgap x)))
    have he (x : X) : Real.sqrt ((ν x).toReal) * Real.sqrt ((ν x).toReal * (2 * gap x)) =
        (ν x).toReal * Real.sqrt (2 * gap x) := by
      rw [Real.sqrt_mul ENNReal.toReal_nonneg, ← mul_assoc,
        Real.mul_self_sqrt ENNReal.toReal_nonneg]
    have hsum : (∑ x, (ν x).toReal * (2 * gap x)) = 2 * δ := by
      simp_rw [mul_left_comm _ (2 : ℝ), ← mul_sum]
      rfl
    simpa only [he, Cslib.Probability.PMF.sum_toReal ν, Real.sqrt_one, one_mul, hsum] using hcs
  calc
    _ ≤ ∑ x, (ν x).toReal * (9 * gap x + 10 * Real.sqrt (2 * gap x)) :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x) ENNReal.toReal_nonneg
    _ = 9 * δ + 10 * ∑ x, (ν x).toReal * Real.sqrt (2 * gap x) := by
      simp_rw [mul_add, sum_add_distrib, mul_left_comm _ (9 : ℝ),
        mul_left_comm _ (10 : ℝ), ← mul_sum]
      rfl
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left havg (by norm_num : 0 ≤ (10 : ℝ)))

end Cslib.Quantum.Measurement
