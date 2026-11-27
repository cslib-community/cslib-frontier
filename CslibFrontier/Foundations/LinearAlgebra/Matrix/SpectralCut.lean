/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, finite-dimensional matrix spectral estimates)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Powerset

/-!
# Spectral cuts in a diagonal basis

For a nonnegative spectrum, the projection at a positive threshold keeps the coordinates
whose eigenvalues meet that threshold. Integrating its diagonal recovers the spectrum.
Integrating the squared Frobenius norm of its commutator with a matrix weights each squared
entry by the gap between the two eigenvalues. The cut weights are lengths of the intervals
on which the retained coordinate set is fixed. Their finite sum can replace integration
for any function of the cut that vanishes on the empty set.

These identities implement the diagonal-basis spectral-cut step of
[Vidick, §2.4 and §3.2][Vidick2022].
-/

public section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {ι : Type*}

/-- The squared Frobenius norm is the sum of the squared entry norms. -/
theorem frobenius_norm_sq_eq_sum {κ E : Type*} [Fintype ι] [Fintype κ]
    [SeminormedAddCommGroup E] (A : Matrix ι κ E) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The diagonal of a Gram matrix gives the squared column norm. -/
theorem re_star_mul_self_diag [Fintype ι] (A : Matrix ι ι ℂ) (i : ι) :
    ((star A * A) i i).re = ∑ j, ‖A j i‖ ^ 2 := by
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.star_apply]
  rw [mul_comm]
  simpa only [starRingEnd_apply, ← Complex.ofReal_pow, Complex.ofReal_re] using
    congrArg Complex.re (Complex.mul_conj' (A j i))

section Projection

variable [DecidableEq ι]

/-- The diagonal projection keeping the eigenvalues at least `t` for a positive threshold. -/
noncomputable def diagonalCut (d : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  diagonal fun i => (Ioc 0 (d i)).indicator (fun _ => (1 : ℂ)) t

@[simp] theorem diagonalCut_apply_diag (d : ι → ℝ) (t : ℝ) (i : ι) :
    diagonalCut d t i i = (Ioc 0 (d i)).indicator (fun _ => (1 : ℂ)) t := by
  simp [diagonalCut]

/-- The integral of the diagonal of the cut projection recovers each eigenvalue. -/
theorem integral_diagonalCut_apply_diag (d : ι → ℝ) (i : ι) (hi : 0 ≤ d i) :
    ∫ t : ℝ, diagonalCut d t i i = (d i : ℂ) := by
  simp only [diagonalCut_apply_diag, integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc_of_le hi, sub_zero, Complex.real_smul, mul_one]

variable [Fintype ι]

@[simp] theorem diagonalCut_mul_self (d : ι → ℝ) (t : ℝ) :
    diagonalCut d t * diagonalCut d t = diagonalCut d t := by
  classical
  rw [diagonalCut, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : t ∈ Ioc 0 (d i) <;> simp [indicator, hi]

private theorem commutator_cut_entry (d : ι → ℝ) (A : Matrix ι ι ℂ) (t : ℝ) (i j : ι)
    (hi : 0 ≤ d i) (hj : 0 ≤ d j) :
    ‖(A * diagonalCut d t - diagonalCut d t * A) i j‖ ^ 2 =
      (Ioc (min (d i) (d j)) (max (d i) (d j))).indicator (fun _ => ‖A i j‖ ^ 2) t := by
  change ‖(A * diagonalCut d t) i j - (diagonalCut d t * A) i j‖ ^ 2 = _
  rw [diagonalCut, mul_diagonal, diagonal_mul]
  by_cases hti : t ∈ Ioc 0 (d i) <;> by_cases htj : t ∈ Ioc 0 (d j)
  · have hout : t ∉ Ioc (min (d i) (d j)) (max (d i) (d j)) :=
      fun h => (not_lt_of_ge (le_min hti.2 htj.2)) h.1
    simp [indicator, hti, htj, hout]
  · have hjt : d j < t := lt_of_not_ge fun h => htj ⟨hti.1, h⟩
    have hji := hjt.le.trans hti.2
    simp [indicator, hti, htj, min_eq_right hji, max_eq_left hji, hjt, hti.2]
  · have hit : d i < t := lt_of_not_ge fun h => hti ⟨htj.1, h⟩
    have hij := hit.le.trans htj.2
    simp [indicator, hti, htj, min_eq_left hij, max_eq_right hij, hit, htj.2]
  · have hout : t ∉ Ioc (min (d i) (d j)) (max (d i) (d j)) := by
      intro h
      have ht : 0 < t := (le_min hi hj).trans_lt h.1
      exact (le_max_iff.mp h.2).elim (fun h' => hti ⟨ht, h'⟩) fun h' => htj ⟨ht, h'⟩
    simp [indicator, hti, htj, hout]

/-- The integrated squared commutator with the cuts is a sum weighted by the spectral gaps. -/
theorem integral_norm_commutator_diagonalCut_sq (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (A : Matrix ι ι ℂ) :
    ∫ t : ℝ, ‖A * diagonalCut d t - diagonalCut d t * A‖ ^ 2 =
      ∑ i, ∑ j, |d i - d j| * ‖A i j‖ ^ 2 := by
  let f (i j : ι) := (Ioc (min (d i) (d j)) (max (d i) (d j))).indicator
    (fun _ => ‖A i j‖ ^ 2)
  have hf (i j : ι) : Integrable (f i j) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    exact integrableOn_const (hs := by simp [Real.volume_Ioc])
  simp_rw [frobenius_norm_sq_eq_sum, commutator_cut_entry d A _ _ _ (hd _) (hd _)]
  change ∫ t : ℝ, (∑ i, ∑ j, f i j t) = _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hf i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [f, integral_indicator_const _ measurableSet_Ioc,
    Real.volume_real_Ioc_of_le inf_le_sup, smul_eq_mul, max_sub_min_eq_abs,
    abs_sub_comm (d j) (d i)]

/-- The cut commutator bound for a weighted family of matrices. The two factors are the
commutator and anticommutator energies at the square root of the spectrum. -/
theorem sum_integral_norm_commutator_diagonalCut_sq_le {α : Type*} [Fintype α]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : α → Matrix ι ι ℂ) :
    let D := diagonal fun i => (Real.sqrt (d i) : ℂ)
    (∑ a, w a * ∫ t : ℝ, ‖A a * diagonalCut d t - diagonalCut d t * A a‖ ^ 2) ≤
      Real.sqrt (∑ a, w a * ‖A a * D - D * A a‖ ^ 2) *
        Real.sqrt (∑ a, w a * ‖A a * D + D * A a‖ ^ 2) := by
  intro D
  let f (a : α) (i j : ι) := Real.sqrt (w a) * (|Real.sqrt (d j) - Real.sqrt (d i)| * ‖A a i j‖)
  let g (a : α) (i j : ι) := Real.sqrt (w a) * ((Real.sqrt (d j) + Real.sqrt (d i)) * ‖A a i j‖)
  have hgap (i j : ι) : |d i - d j| =
      |Real.sqrt (d j) - Real.sqrt (d i)| * (Real.sqrt (d j) + Real.sqrt (d i)) := by
    rw [abs_sub_comm (d i) (d j), ← abs_of_nonneg (by positivity :
      0 ≤ Real.sqrt (d j) + Real.sqrt (d i)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hd i), Real.sq_sqrt (hd j)]
  have hf (a : α) (i j : ι) : f a i j ^ 2 = w a * ‖(A a * D - D * A a) i j‖ ^ 2 := by
    change _ = w a * ‖(A a * D) i j - (D * A a) i j‖ ^ 2
    rw [show (A a * D) i j - (D * A a) i j =
        ((Real.sqrt (d j) - Real.sqrt (d i) : ℝ) : ℂ) * A a i j by
      simp only [D, mul_diagonal, diagonal_mul, Complex.ofReal_sub]
      ring]
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.sq_sqrt (hw a), mul_pow]
  have hg (a : α) (i j : ι) : g a i j ^ 2 = w a * ‖(A a * D + D * A a) i j‖ ^ 2 := by
    change _ = w a * ‖(A a * D) i j + (D * A a) i j‖ ^ 2
    rw [show (A a * D) i j + (D * A a) i j =
        ((Real.sqrt (d j) + Real.sqrt (d i) : ℝ) : ℂ) * A a i j by
      simp only [D, mul_diagonal, diagonal_mul, Complex.ofReal_add]
      ring]
    simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.sqrt (d j) + Real.sqrt (d i)), Real.sq_sqrt (hw a), mul_pow]
  have hfg (a : α) (i j : ι) : f a i j * g a i j =
      w a * (|d i - d j| * ‖A a i j‖ ^ 2) := by
    rw [hgap]
    dsimp only [f, g]
    linear_combination (|Real.sqrt (d j) - Real.sqrt (d i)| *
      (Real.sqrt (d j) + Real.sqrt (d i)) * ‖A a i j‖ ^ 2) * Real.sq_sqrt (hw a)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (α × ι × ι))
    (fun p => f p.1 p.2.1 p.2.2) (fun p => g p.1 p.2.1 p.2.2)
  simpa only [Fintype.sum_prod_type, hfg, hf, hg, ← Finset.mul_sum, ← frobenius_norm_sq_eq_sum,
    integral_norm_commutator_diagonalCut_sq d hd] using hcs

end Projection

variable [Fintype ι]

/-- The coordinates kept by a spectral cut. -/
noncomputable def diagonalCutSupport (d : ι → ℝ) (t : ℝ) : Finset ι :=
  open Classical in Finset.univ.filter fun i => t ∈ Ioc 0 (d i)

@[simp] theorem mem_diagonalCutSupport (d : ι → ℝ) (t : ℝ) (i : ι) :
    i ∈ diagonalCutSupport d t ↔ t ∈ Ioc 0 (d i) := by
  classical
  simp [diagonalCutSupport]

theorem diagonalCut_eq_diagonal_support [DecidableEq ι] (d : ι → ℝ) (t : ℝ) :
    diagonalCut d t = diagonal fun i => if i ∈ diagonalCutSupport d t then 1 else 0 := by
  simp only [diagonalCut, mem_diagonalCutSupport, indicator]

private def cutFiber (d : ι → ℝ) (s : Finset ι) : Set ℝ :=
  {t | diagonalCutSupport d t = s}

private theorem measurableSet_cutFiber (d : ι → ℝ) (s : Finset ι) :
    MeasurableSet (cutFiber d s) := by
  classical
  have he : cutFiber d s = ⋂ i, if i ∈ s then Ioc 0 (d i) else (Ioc 0 (d i))ᶜ := by
    ext t
    simp only [cutFiber, Set.mem_ofPred_eq, Finset.ext_iff, mem_diagonalCutSupport, Set.mem_iInter]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [he]
  exact MeasurableSet.iInter fun i => by split_ifs <;> measurability

private theorem volume_cutFiber_ne_top (d : ι → ℝ) {s : Finset ι} (hs : s.Nonempty) :
    volume (cutFiber d s) ≠ ⊤ := by
  obtain ⟨i, hi⟩ := hs
  have hsub : cutFiber d s ⊆ Ioc 0 (d i) := by
    intro t ht
    rw [← mem_diagonalCutSupport]
    exact ht ▸ hi
  exact ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono hsub)

/-- The total length of positive thresholds that keep exactly the nonempty set `s`. -/
noncomputable def diagonalCutWidth (d : ι → ℝ) (s : {s : Finset ι // s.Nonempty}) : ℝ :=
  volume.real (cutFiber d s.val)

theorem diagonalCutWidth_nonneg (d : ι → ℝ) (s : {s : Finset ι // s.Nonempty}) :
    0 ≤ diagonalCutWidth d s :=
  ENNReal.toReal_nonneg

/-- Integrating a function of a cut is a finite weighted sum. The empty cut contributes zero. -/
theorem integral_diagonalCutSupport (d : ι → ℝ) (F : Finset ι → ℝ) (hF : F ∅ = 0) :
    ∫ t : ℝ, F (diagonalCutSupport d t) =
      ∑ s : {s : Finset ι // s.Nonempty}, diagonalCutWidth d s * F s.val := by
  let f (s : {s : Finset ι // s.Nonempty}) := (cutFiber d s.val).indicator (fun _ => F s.val)
  have hf (s : {s : Finset ι // s.Nonempty}) : Integrable (f s) :=
    (integrableOn_const (hs := volume_cutFiber_ne_top d s.property)).integrable_indicator
      (measurableSet_cutFiber d s.val)
  have he : (fun t => F (diagonalCutSupport d t)) = fun t => ∑ s, f s t := by
    funext t
    by_cases ht : (diagonalCutSupport d t).Nonempty
    · let s : {s : Finset ι // s.Nonempty} := ⟨diagonalCutSupport d t, ht⟩
      rw [Finset.sum_eq_single s]
      · simp [s, f, cutFiber]
      · intro u _ hu
        have hn : diagonalCutSupport d t ≠ u.val := fun h => hu (Subtype.ext h.symm)
        simp [f, cutFiber, hn]
      · exact fun h => (h (Finset.mem_univ _)).elim
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht, hF]
      symm
      apply Finset.sum_eq_zero
      intro s _
      have hn : diagonalCutSupport d t ≠ s.val := fun he => ht (he ▸ s.property)
      simp [f, cutFiber, hn]
  rw [he, integral_finsetSum _ (fun s _ => hf s)]
  simp only [f, integral_indicator_const _ (measurableSet_cutFiber d _), diagonalCutWidth,
    smul_eq_mul]

/-- The widths of the cuts containing a given coordinate sum to its eigenvalue. -/
theorem sum_diagonalCutWidth_mem [DecidableEq ι] (d : ι → ℝ) (i : ι) (hi : 0 ≤ d i) :
    (∑ s : {s : Finset ι // s.Nonempty}, diagonalCutWidth d s * (if i ∈ s.val then 1 else 0)) =
      d i := by
  rw [← integral_diagonalCutSupport d (fun s => if i ∈ s then 1 else 0) (by simp)]
  classical
  simp only [mem_diagonalCutSupport]
  calc
    _ = ∫ t : ℝ, (Ioc 0 (d i)).indicator (fun _ => (1 : ℝ)) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ Ioc 0 (d i) <;> simp [ht]
    _ = d i := by
      simp only [integral_indicator_const (1 : ℝ) measurableSet_Ioc,
        Real.volume_real_Ioc_of_le hi, sub_zero, smul_eq_mul, mul_one]

/-- Multiplying each cut width by its dimension gives weights summing to the spectral trace. -/
theorem sum_diagonalCutWidth_card (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ s : {s : Finset ι // s.Nonempty}, diagonalCutWidth d s * s.val.card) = ∑ i, d i := by
  classical
  have hcard (s : Finset ι) : (s.card : ℝ) = ∑ i, if i ∈ s then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_diagonalCutWidth_mem d i (hd i)

/-- The weighted sum of the coordinate projections recovers the original diagonal matrix. -/
theorem diagonal_eq_sum_diagonalCutWidth [DecidableEq ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    diagonal (fun i => (d i : ℂ)) =
      ∑ s : {s : Finset ι // s.Nonempty},
        diagonalCutWidth d s • diagonal (fun i => if i ∈ s.val then (1 : ℂ) else 0) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [diagonal_apply_eq, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one,
      Complex.ofReal_zero] using congrArg Complex.ofReal (sum_diagonalCutWidth_mem d i (hd i)).symm
  · simp [Matrix.sum_apply, diagonal_apply_ne _ hij]

/-- The commutator estimate as a finite sum, with one term per nonempty retained coordinate set. -/
theorem sum_diagonalCutWidth_norm_commutator_sq_le [DecidableEq ι] {α : Type*} [Fintype α]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : α → Matrix ι ι ℂ) :
    let D := diagonal fun i => (Real.sqrt (d i) : ℂ)
    let P := fun s : Finset ι => diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ s : {s : Finset ι // s.Nonempty},
        diagonalCutWidth d s * ∑ a, w a * ‖A a * P s.val - P s.val * A a‖ ^ 2) ≤
      Real.sqrt (∑ a, w a * ‖A a * D - D * A a‖ ^ 2) *
        Real.sqrt (∑ a, w a * ‖A a * D + D * A a‖ ^ 2) := by
  intro D P
  have he (a : α) :
      ∑ s : {s : Finset ι // s.Nonempty},
        diagonalCutWidth d s * ‖A a * P s.val - P s.val * A a‖ ^ 2 =
      ∫ t : ℝ, ‖A a * diagonalCut d t - diagonalCut d t * A a‖ ^ 2 := by
    rw [← integral_diagonalCutSupport d (fun s => ‖A a * P s - P s * A a‖ ^ 2)
      (by simp [P])]
    simp only [P, ← diagonalCut_eq_diagonal_support]
  simp_rw [Finset.mul_sum, mul_left_comm (diagonalCutWidth d _) (w _)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, he]
  exact sum_integral_norm_commutator_diagonalCut_sq_le d hd w hw A

/-- For a matrix family of bounded row and column square mass, a lower bound on its
geometric-mean-weighted square mass bounds the average cut commutator. For measurements in
a Schmidt basis, the geometric-mean-weighted mass is the diagonal answer agreement. -/
theorem sum_diagonalCutWidth_norm_commutator_sq_le_of_agreement
    [DecidableEq ι] {α : Type*} [Fintype α]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (A : α → Matrix ι ι ℂ) (δ : ℝ) :
    let N := fun i j => ∑ a, w a * ‖A a i j‖ ^ 2
    (∀ i, ∑ j, N i j ≤ 1) →
    (∀ j, ∑ i, N i j ≤ 1) →
    (∑ i, d i) - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * N i j →
    let P := fun s : Finset ι => diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ s : {s : Finset ι // s.Nonempty},
        diagonalCutWidth d s * ∑ a, w a * ‖A a * P s.val - P s.val * A a‖ ^ 2) ≤
      Real.sqrt (2 * δ) * Real.sqrt (4 * ∑ i, d i) := by
  intro N hrow hcol hagree P
  let D := diagonal fun i => (Real.sqrt (d i) : ℂ)
  have hN (i j : ι) : 0 ≤ N i j :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
  have henergy (r : ℝ) :
      ∑ a, w a * ‖A a * D + r • (D * A a)‖ ^ 2 =
        ∑ i, ∑ j, (Real.sqrt (d j) + r * Real.sqrt (d i)) ^ 2 * N i j := by
    have hentry (a : α) (i j : ι) :
        (A a * D + r • (D * A a)) i j =
          ((Real.sqrt (d j) + r * Real.sqrt (d i) : ℝ) : ℂ) * A a i j := by
      change (A a * D) i j + (r • (D * A a)) i j = _
      simp only [D, Matrix.smul_apply, mul_diagonal, diagonal_mul, Complex.real_smul,
        Complex.ofReal_add, Complex.ofReal_mul]
      ring
    calc
      _ = ∑ a, ∑ i, ∑ j, (Real.sqrt (d j) + r * Real.sqrt (d i)) ^ 2 *
          (w a * ‖A a i j‖ ^ 2) := by
        simp only [frobenius_norm_sq_eq_sum, hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          sq_abs, mul_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, N]
  have hmass : ∑ i, ∑ j, (d j + d i) * N i j ≤ 2 * ∑ i, d i := by
    have hr : ∑ i, ∑ j, d i * N i j ≤ ∑ i, d i := by
      simp only [← Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (mul_le_mul_of_nonneg_left (hrow i) (hd i)).trans_eq
        (mul_one (d i))
    have hc : ∑ i, ∑ j, d j * N i j ≤ ∑ j, d j := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (mul_le_mul_of_nonneg_left (hcol j) (hd j)).trans_eq
        (mul_one (d j))
    simp only [add_mul, Finset.sum_add_distrib]
    linarith
  have hminus : ∑ a, w a * ‖A a * D - D * A a‖ ^ 2 ≤ 2 * δ := by
    rw [sub_eq_add_neg] at hagree
    simp only [sub_eq_add_neg, ← neg_one_smul ℝ (D * A _), henergy, neg_one_mul]
    have he (i j : ι) : (Real.sqrt (d j) + -Real.sqrt (d i)) ^ 2 * N i j =
        (d j + d i) * N i j - 2 * ((Real.sqrt (d i) * Real.sqrt (d j)) * N i j) := by
      rw [show (Real.sqrt (d j) + -Real.sqrt (d i)) ^ 2 =
          d j + d i - 2 * Real.sqrt (d i) * Real.sqrt (d j) by
        nlinarith [Real.sq_sqrt (hd i), Real.sq_sqrt (hd j)]]
      ring
    simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hplus : ∑ a, w a * ‖A a * D + D * A a‖ ^ 2 ≤ 4 * ∑ i, d i := by
    have he (i j : ι) : (Real.sqrt (d j) + Real.sqrt (d i)) ^ 2 ≤ 2 * (d j + d i) := by
      nlinarith [Real.sq_sqrt (hd i), Real.sq_sqrt (hd j),
        sq_nonneg (Real.sqrt (d j) - Real.sqrt (d i))]
    calc
      _ = ∑ i, ∑ j, (Real.sqrt (d j) + Real.sqrt (d i)) ^ 2 * N i j := by
        simpa only [one_smul, one_mul] using henergy 1
      _ ≤ ∑ i, ∑ j, (2 * (d j + d i)) * N i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (he i j) (hN i j)
      _ ≤ _ := by simp only [mul_assoc, ← Finset.mul_sum]; linarith
  exact (sum_diagonalCutWidth_norm_commutator_sq_le d hd w hw A).trans
    (mul_le_mul (Real.sqrt_le_sqrt hminus) (Real.sqrt_le_sqrt hplus)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Matrix
