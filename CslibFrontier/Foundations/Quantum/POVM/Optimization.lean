/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Foundations.Quantum.Algebra.Measurement

/-!
# Optimization over finite POVMs

A linear score on the set of finite positive operator valued measurements
attains its maximum. For positive matrix objectives the maximum has a common
operator majorant as a dual certificate, as in [JNVWY2020LowIndividualDegree, Lemma 9.2].

## Main results

* `Cslib.Quantum.POVM.sum_trace_mul_le_trace_of_le`: weak duality for positive effects.
* `Cslib.Quantum.POVM.exists_optimal_trace_certificate`: a maximizing POVM, a positive
  majorant of the objective matrices and complementary slackness.
-/

public section

namespace Cslib.Quantum.POVM

open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]

private theorem exists_max_trace (H : A → Matrix ι ι ℂ) [Nonempty A] :
    ∃ T : POVM A ι, ∀ S : POVM A ι,
      ∑ a, ((S.effect a * H a).trace).re ≤ ∑ a, ((T.effect a * H a).trace).re := by
  classical
  let feasible : Set (A → Matrix ι ι ℂ) :=
    {E | (∀ a, 0 ≤ E a) ∧ ∑ a, E a = 1}
  have hclosed : IsClosed feasible := by
    change IsClosed ({E : A → Matrix ι ι ℂ | ∀ a, 0 ≤ E a} ∩
      {E : A → Matrix ι ι ℂ | ∑ a, E a = 1})
    have hsum : Continuous (fun E : A → Matrix ι ι ℂ => ∑ a, E a) := by fun_prop
    rw [Set.ofPred_forall]
    refine (isClosed_iInter fun a => ?_).inter (isClosed_eq hsum continuous_const)
    exact isClosed_le continuous_const (continuous_apply a)
  have hcompact : IsCompact feasible := by
    refine (isCompact_univ_pi fun _ : A =>
      isCompact_closedBall (0 : Matrix ι ι ℂ) 1).of_isClosed_subset hclosed ?_
    intro E hE a _
    let T : POVM A ι := ⟨E, fun a => (hE.1 a).posSemidef, hE.2⟩
    apply mem_closedBall_zero_iff.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hE.1 a)).mpr
    simpa only [toMeasurement_effect, T] using T.toMeasurement.effect_le_one a
  let a₀ : A := Classical.choice inferInstance
  have hnonempty : feasible.Nonempty :=
    ⟨(POVM.const a₀).effect, fun a => ((POVM.const a₀).posSemidef a).nonneg,
      (POVM.const a₀).sum_effect⟩
  obtain ⟨E, hE, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (f := fun E => ∑ a, ((E a * H a).trace).re) (by unfold Matrix.trace; fun_prop)
  exact ⟨⟨E, fun a => (hE.1 a).posSemidef, hE.2⟩, fun S =>
    hmax (show S.effect ∈ feasible from ⟨fun a => (S.posSemidef a).nonneg, S.sum_effect⟩)⟩

private theorem linear_nonpos_of_quadratic {b c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t, 0 < t → t ≤ δ → t * b + t ^ 2 * c ≤ 0) : b ≤ 0 := by
  by_contra! hb
  let t := min δ (b / (2 * (|c| + 1)))
  have ht : 0 < t := lt_min hδ (div_pos hb (by positivity))
  have htc : t * (2 * (|c| + 1)) ≤ b :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hsign : b + t * c ≤ 0 := by
    apply nonpos_of_mul_nonpos_right _ ht
    nlinarith only [h t ht (min_le_left _ _)]
  have hlower := mul_le_mul_of_nonneg_left (neg_abs_le c) ht.le
  nlinarith only [hsign, htc, hlower, ht, hb]

private theorem sandwich_sub_smul (P X : Matrix ι ι ℂ) (t : ℝ) :
    (1 - t • P) * X * (1 - t • P) =
      X - t • (P * X + X * P) + t ^ 2 • (P * X * P) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  module

private theorem exists_variation [DecidableEq A] (T : POVM A ι) (j : A) {P : Matrix ι ι ℂ}
    (hP : P.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (htP : t * ‖P‖ ≤ 1) :
    ∃ V : POVM A ι, ∀ a, V.effect a =
      (1 - t • P) * T.effect a * (1 - t • P) +
        if a = j then 1 - (1 - t • P) * (1 - t • P) else 0 := by
  classical
  let B : Matrix ι ι ℂ := 1 - t • P
  have hnonneg : 0 ≤ t • P := (hP.smul ht).nonneg
  have hB : 0 ≤ B := by
    apply sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).mp _)
    simpa only [norm_smul, Real.norm_of_nonneg ht] using htP
  have hB₁ : 0 ≤ 1 - B := by simpa [B] using hnonneg
  have hB₂ : B * B ≤ B := by
    apply sub_nonneg.mp
    simpa only [mul_sub, mul_one] using
      (Commute.one_right B |>.sub_right (Commute.refl B)).mul_nonneg hB hB₁
  have hrem : 0 ≤ 1 - B * B := sub_nonneg.mpr (hB₂.trans (sub_nonneg.mp hB₁))
  refine ⟨{ effect a := B * T.effect a * B + if a = j then 1 - B * B else 0
            posSemidef a := ?_
            sum_effect := ?_ }, fun a => rfl⟩
  · apply PosSemidef.add
    · simpa only [hB.posSemidef.isHermitian.eq] using
        (T.posSemidef a).mul_mul_conjTranspose_same B
    · split_ifs
      · exact hrem.posSemidef
      · exact PosSemidef.zero
  · rw [sum_add_distrib, ← sum_mul, ← mul_sum, T.sum_effect, mul_one]
    simp

/-- A maximum of the trace objective gives a dual majorant by varying the POVM. -/
private theorem majorant_of_max (H : A → Matrix ι ι ℂ) (hH : ∀ a, (H a).IsHermitian)
    (T : POVM A ι) (hmax : ∀ S : POVM A ι,
      ∑ a, ((S.effect a * H a).trace).re ≤ ∑ a, ((T.effect a * H a).trace).re) :
    ∀ j, H j ≤ (1 / 2 : ℝ) • ∑ a, (T.effect a * H a + H a * T.effect a) := by
  classical
  let Z := (1 / 2 : ℝ) • ∑ a, (T.effect a * H a + H a * T.effect a)
  have hZ : Z.IsHermitian := by
    change star Z = Z
    simp only [Z, star_smul, star_trivial, star_sum, star_add, star_mul,
      star_eq_conjTranspose, (T.posSemidef _).isHermitian.eq, (hH _).eq, add_comm]
  intro j
  apply Matrix.le_iff.mpr
  apply (posSemidef_iff_dotProduct_mulVec).mpr
  refine ⟨hZ.sub (hH j), fun v => ?_⟩
  let P := vecMulVec v (star v)
  have hP : P.PosSemidef := posSemidef_vecMulVec_self_star v
  let δ : ℝ := (‖P‖ + 1)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by positivity)
  let c : ℝ := (∑ a, ((P * T.effect a * P * H a).trace).re) -
    ((P * P * H j).trace).re
  have hlin :
      (∑ a, (((P * T.effect a + T.effect a * P) * H a).trace).re) =
        2 * ((P * Z).trace).re := by
    simp only [Z, mul_smul_comm, trace_smul, Complex.smul_re, smul_eq_mul, ← mul_assoc]
    norm_num
    rw [mul_sum, trace_sum, Complex.re_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [add_mul, mul_add, trace_add, Complex.add_re, mul_assoc]
    rw [trace_mul_comm (T.effect a) (P * H a), mul_assoc]
  have hb : 2 * (((P * H j).trace).re - ((P * Z).trace).re) ≤ 0 := by
    apply linear_nonpos_of_quadratic hδ (c := c)
    intro t ht htd
    have htP : t * ‖P‖ ≤ 1 := by
      have h := (le_div_iff₀ (by positivity : 0 < ‖P‖ + 1)).mp
        (show t ≤ 1 / (‖P‖ + 1) by simpa only [one_div] using htd)
      nlinarith only [h, ht]
    obtain ⟨V, hV⟩ := exists_variation T j hP ht.le htP
    have hV' (a : A) :
        V.effect a = T.effect a - t • (P * T.effect a + T.effect a * P) +
          t ^ 2 • (P * T.effect a * P) +
          if a = j then (2 * t) • P - t ^ 2 • (P * P) else 0 := by
      have hBsq := sandwich_sub_smul P 1 t
      simp only [mul_one, one_mul] at hBsq
      rw [hV, sandwich_sub_smul, hBsq]
      congr 1
      split_ifs
      · module
      · rfl
    have hscore := hmax V
    simp only [hV', add_mul, sub_mul, smul_mul_assoc, trace_add, trace_sub, trace_smul,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul, sum_add_distrib,
      sum_sub_distrib, ← mul_sum] at hscore
    have hm :
        (∑ a, (((if a = j then (2 * t) • P - t ^ 2 • (P * P) else 0) * H a).trace).re) =
          (2 * t) * ((P * H j).trace).re - t ^ 2 * ((P * P * H j).trace).re := by
      rw [sum_eq_single_of_mem j (mem_univ j)]
      · simp only [ite_true, sub_mul, smul_mul_assoc, trace_sub, trace_smul,
          Complex.smul_re, Complex.sub_re, smul_eq_mul]
      · intro a _ hne
        simp [hne]
    simp only [add_mul, trace_add, Complex.add_re, sum_add_distrib] at hlin
    rw [hm, hlin] at hscore
    dsimp [c]
    linarith only [hscore]
  have ht : 0 ≤ ((P * (Z - H j)).trace).re := by
    rw [mul_sub, trace_sub, Complex.sub_re]
    linarith only [hb]
  rw [trace_mul_comm, show P = vecMulVec v (star v) from rfl, mul_vecMulVec, trace_vecMulVec,
    dotProduct_comm] at ht
  refine Complex.nonneg_iff.mpr ⟨ht, ?_⟩
  have hi := congrArg Complex.im ((hZ.sub (hH j)).star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith only [hi]

/-- Weak duality for the trace objective. A common positive majorant bounds the score
even for positive effects whose sum is only bounded by the identity. -/
theorem sum_trace_mul_le_trace_of_le (E H : A → Matrix ι ι ℂ) (Z : Matrix ι ι ℂ)
    (hE : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a ≤ 1)
    (hZ : Z.PosSemidef) (hle : ∀ a, H a ≤ Z) :
    ∑ a, (E a * H a).trace ≤ Z.trace := by
  calc
    _ ≤ ∑ a, (E a * Z).trace := sum_le_sum fun a _ => by
      simpa only [mul_sub, trace_sub, sub_nonneg] using
        (hE a).trace_mul_nonneg (Matrix.le_iff.mp (hle a))
    _ ≤ _ := by
      simpa only [sub_mul, one_mul, trace_sub, sum_mul, trace_sum, sub_nonneg] using
        (Matrix.le_iff.mp hsum).trace_mul_nonneg hZ

/-- A positive matrix objective has an optimal POVM and a common positive majorant (Z).
Every effect annihilates its slack, and the objective value is the trace of (Z). -/
theorem exists_optimal_trace_certificate [Nonempty A] (H : A → Matrix ι ι ℂ)
    (hH : ∀ a, (H a).PosSemidef) :
    ∃ (T : POVM A ι) (Z : Matrix ι ι ℂ),
      Z.PosSemidef ∧ (∀ a, H a ≤ Z) ∧ (∀ a, T.effect a * Z = T.effect a * H a) ∧
        (∑ a, (T.effect a * H a).trace) = Z.trace := by
  obtain ⟨T, hmax⟩ := exists_max_trace H
  let Z := (1 / 2 : ℝ) • ∑ a, (T.effect a * H a + H a * T.effect a)
  have hle : ∀ a, H a ≤ Z := majorant_of_max H (fun a => (hH a).isHermitian) T hmax
  have htrace : Z.trace = ∑ a, (T.effect a * H a).trace := by
    simp only [Z, trace_smul, trace_sum, trace_add, trace_mul_comm (H _) (T.effect _)]
    rw [sum_add_distrib, ← two_smul ℝ, smul_smul]
    norm_num
  have hslack (a : A) : 0 ≤ (T.effect a * (Z - H a)).trace :=
    (T.posSemidef a).trace_mul_nonneg (Matrix.le_iff.mp (hle a))
  have hsum : ∑ a, (T.effect a * (Z - H a)).trace.re = 0 := by
    rw [← Complex.re_sum, ← trace_sum]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, T.sum_effect, one_mul, trace_sub,
      htrace, trace_sum, sub_self, Complex.zero_re]
  have hzero (a : A) : (T.effect a * (Z - H a)).trace = 0 := by
    have h := Complex.nonneg_iff.mp (hslack a)
    have hr := (sum_eq_zero_iff_of_nonneg (fun b _ => (Complex.nonneg_iff.mp (hslack b)).1)).mp
      hsum a (mem_univ a)
    exact Complex.ext hr h.2.symm
  have hcomp (a : A) : T.effect a * Z = T.effect a * H a := by
    have h := ((T.posSemidef a).trace_mul_eq_zero_iff (Matrix.le_iff.mp (hle a))).mp (hzero a)
    exact sub_eq_zero.mp (by rwa [← mul_sub])
  let a₀ : A := Classical.choice inferInstance
  exact ⟨T, Z, ((hH a₀).nonneg.trans (hle a₀)).posSemidef, hle, hcomp, htrace.symm⟩

end Cslib.Quantum.POVM
