/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronousReduction
import CslibFrontier.Computability.PCP.TwoProverGame.Naimark
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Foundations.Quantum.Algebra.DensityState
import CslibFrontier.Foundations.Quantum.DensityMatrix.Linear
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import CslibFrontier.Foundations.Quantum.POVM.Density
import CslibFrontier.Foundations.Quantum.POVM.DirectSum
import Mathlib.Logic.Equiv.Set
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementDistance
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Correlation estimates for almost-synchronous strategies

Moving a projective measurement to Bob's space changes the joint probabilities by at most
twice the state-dependent distance to its replacement. With Bob's original measurement as
the replacement, consistency bounds the average error by the diagonal synchrony defect.

The resulting sequential weights are linear in Bob's reduced density. When that density
is decomposed into components and the rounded projections commute with their component
densities, their mixture of product weights can be compared to the sequential weights.
Applying these estimates to the spectral rounding of Bob's system and preserving the input
correlation by Naimark dilation gives the finite form of [Vidick, Corollary 3.3][Vidick2022].
-/

public section

open Cslib.Quantum Matrix Finset
open scoped MatrixOrder Kronecker

namespace Cslib.PCP.QuantumStrategy

variable {ι κ X Y A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype A] [Fintype B]

/-- Replacing Alice's projective measurement by operators on Bob's space changes the joint
weights by at most twice the state-dependent distance between the two families. -/
theorem sum_abs_prob_sub_re_apply_conjugation_le (S : QuantumStrategy X Y A B ι κ)
    (x : X) (y : Y) (N : POVM A κ)
    (hP : ∀ a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ a, ∑ b, |S.prob x y a b -
        (S.toCommuting.state ((1 ⊗ₖ N.effect a) * (S.toCommuting.bob y).effect b *
          (1 ⊗ₖ N.effect a))).re|) ≤
      2 * √(∑ a, S.toCommuting.state.norm
        ((S.toCommuting.alice x).effect a - 1 ⊗ₖ N.effect a) ^ 2) := by
  have hproj : (S.toCommuting.alice x).IsProjective := by
    intro a
    change ((S.alice x).effect a ⊗ₖ (1 : Matrix κ κ ℂ)) *
      ((S.alice x).effect a ⊗ₖ 1) = (S.alice x).effect a ⊗ₖ 1
    rw [← Matrix.mul_kronecker_mul, hP a, Matrix.one_mul]
  simp_rw [← S.prob_toCommuting]
  exact (S.toCommuting.bob y).sum_abs_re_apply_effect_mul_sub_conjugation_le
    S.toCommuting.state (S.toCommuting.alice x) (rightMeasurement N) hproj
    (S.toCommuting.commute x y)

/-- The averaged switching error depends on the first marginal of the joint question law.
The replacement may be a POVM on a space of different dimension from Alice's. -/
theorem sum_abs_prob_sub_re_apply_conjugation_le_of_questions [Fintype X] [Fintype Y]
    (S : QuantumStrategy X Y A B ι κ) (N : X → POVM A κ) (μ : PMF (X × Y))
    (hP : ∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b, |S.prob q.1 q.2 a b -
        (S.toCommuting.state ((1 ⊗ₖ (N q.1).effect a) * (S.toCommuting.bob q.2).effect b *
          (1 ⊗ₖ (N q.1).effect a))).re|) ≤
      2 * √(∑ x, ((μ.map Prod.fst) x).toReal * ∑ a, S.toCommuting.state.norm
        ((S.toCommuting.alice x).effect a - 1 ⊗ₖ (N x).effect a) ^ 2) := by
  let E (x : X) := ∑ a, S.toCommuting.state.norm
    ((S.toCommuting.alice x).effect a - 1 ⊗ₖ (N x).effect a) ^ 2
  calc
    _ ≤ ∑ q : X × Y, (μ q).toReal * (2 * √(E q.1)) :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
        (S.sum_abs_prob_sub_re_apply_conjugation_le q.1 q.2 (N q.1) (hP q.1))
        ENNReal.toReal_nonneg
    _ = 2 * ∑ q : X × Y, (μ q).toReal * √(E q.1) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => mul_left_comm _ _ _
    _ = 2 * ∑ x, ((μ.map Prod.fst) x).toReal * √(E x) :=
      congrArg (2 * ·) (Cslib.Probability.PMF.sum_map_mul μ Prod.fst (fun x => √(E x))).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [smul_eq_mul, E] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
        (t := univ) (w := fun x => ((μ.map Prod.fst) x).toReal) (p := E)
        (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal _)
        (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

/-- A sequential weight on Bob's system depends only on his reduced density matrix. -/
theorem bob_conjugation_eq_trace (S : QuantumStrategy X Y A B ι κ)
    (N : POVM A κ) (y : Y) (a : A) (b : B) :
    S.toCommuting.state ((1 ⊗ₖ N.effect a) * (S.toCommuting.bob y).effect b *
      (1 ⊗ₖ N.effect a)) =
      ((N.effect a * (S.bob y).effect b * N.effect a) *
        partialTraceLeft (pureState S.state)).trace := by
  change AlgState.vector S.state S.norm_state ((1 ⊗ₖ N.effect a) *
    (1 ⊗ₖ (S.bob y).effect b) * (1 ⊗ₖ N.effect a)) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
    AlgState.vector_apply, ← trace_mul_pureState, trace_mul_partialTraceLeft]

/-- A nearly synchronous strategy with projective Alice measurements is close to the
sequential experiment that applies Bob's measurements for the two questions on his system.
The loss depends only on the synchrony defect under Alice's marginal. -/
theorem sum_abs_prob_sub_bob_sequential_le [Fintype X] (S : QuantumStrategy X X A A ι κ)
    (μ : PMF (X × X))
    (hP : ∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b, |S.prob q.1 q.2 a b -
        (((S.bob q.1).effect a * (S.bob q.2).effect b * (S.bob q.1).effect a) *
          partialTraceLeft (pureState S.state)).trace.re|) ≤
      2 * √(2 * S.synchronyDefect (μ.map Prod.fst)) := by
  have h := S.sum_abs_prob_sub_re_apply_conjugation_le_of_questions S.bob μ hP
  simp only [bob_conjugation_eq_trace] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  rw [synchronyDefect_eq_sum, mul_sum]
  refine sum_le_sum fun x _ => ?_
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have hagree : Measurement.agreement S.toCommuting.state
      (S.toCommuting.alice x) (S.toCommuting.bob x) = ∑ a, S.prob x x a a := by
    unfold Measurement.agreement
    exact sum_congr rfl fun a _ => S.prob_toCommuting x x a a
  have hcons := Measurement.sum_norm_sub_sq_le S.toCommuting.state
    (S.toCommuting.alice x) (S.toCommuting.bob x) (fun a => S.toCommuting.commute x x a a)
  rw [hagree] at hcons
  exact hcons.trans_eq (by ring)

open scoped ComplexOrder in
/-- Bound the error of replacing sequential weights by a mixture of product weights
on invariant density components. The two question coordinates have the same marginal. -/
theorem sum_abs_sequential_sub_mixture_le {σ : Type*} [Fintype σ] [Fintype X]
    (P : X → POVM A κ) (Q : σ → X → POVM A κ)
    (ρ : σ → Matrix κ κ ℂ) (hρ : ∀ s, IsDensityMatrix (ρ s))
    (p : PMF σ) (μ : PMF (X × X)) (hμ : μ.map Prod.snd = μ.map Prod.fst)
    (hP : ∀ x, (P x).toMeasurement.IsProjective)
    (hQ : ∀ s x, (Q s x).toMeasurement.IsProjective)
    (hc : ∀ s x a, Commute ((Q s x).effect a) (ρ s)) :
    (∑ q, (μ q).toReal * ∑ a, ∑ b,
      |(((P q.1).effect a * (P q.2).effect b * (P q.1).effect a) *
          (∑ s, (p s).toReal • ρ s)).trace.re -
        ∑ s, (p s).toReal * (((Q s q.1).effect a * (Q s q.2).effect b) * ρ s).trace.re|) ≤
      4 * √(∑ x, ((μ.map Prod.fst) x).toReal * ∑ s, (p s).toReal * ∑ a,
        (((P x).effect a - (Q s x).effect a) * ((P x).effect a - (Q s x).effect a) *
          ρ s).trace.re) := by
  let E (x : X) (s : σ) := ∑ a, (((P x).effect a - (Q s x).effect a) *
    ((P x).effect a - (Q s x).effect a) * ρ s).trace.re
  have hE (x : X) (s : σ) : 0 ≤ E x s := by
    refine sum_nonneg fun a _ => ?_
    let D := (P x).effect a - (Q s x).effect a
    have hs : star D = D :=
      (((P x).posSemidef a).isHermitian.sub ((Q s x).posSemidef a).isHermitian).eq
    simpa only [AlgState.norm_sq, AlgState.ofDensityMatrix_apply, hs] using
      sq_nonneg ((AlgState.ofDensityMatrix (ρ s) (hρ s)).norm D)
  let M := μ.map Prod.fst
  let V (x : X) := ∑ s, (p s).toReal * √(E x s)
  let W (x : X) := ∑ s, (p s).toReal * E x s
  have hV (x : X) : V x ≤ √(W x) := by
    simpa only [smul_eq_mul, V, W] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      (t := univ) (w := fun s => (p s).toReal) (p := E x)
      (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal p) (fun s _ => hE x s)
  have hW : (∑ x, (M x).toReal * √(W x)) ≤ √(∑ x, (M x).toReal * W x) := by
    simpa only [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
      (t := univ) (w := fun x => (M x).toReal) (p := W)
      (fun _ _ => ENNReal.toReal_nonneg) (Cslib.Probability.PMF.sum_toReal M)
      (fun x _ => sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg (hE x s))
  have hrow (x y : X) :
      (∑ a, ∑ b,
        |(((P x).effect a * (P y).effect b * (P x).effect a) *
            (∑ s, (p s).toReal • ρ s)).trace.re -
          ∑ s, (p s).toReal * (((Q s x).effect a * (Q s y).effect b) * ρ s).trace.re|) ≤
        2 * (V x + V y) := by
    let L (s : σ) (a b : A) := (((P x).effect a * (P y).effect b * (P x).effect a) * ρ s).trace.re
    let R (s : σ) (a b : A) := (((Q s x).effect a * (Q s y).effect b) * ρ s).trace.re
    have hsplit (a b : A) :
        |(((P x).effect a * (P y).effect b * (P x).effect a) *
            (∑ s, (p s).toReal • ρ s)).trace.re - ∑ s, (p s).toReal * R s a b| ≤
          ∑ s, (p s).toReal * |L s a b - R s a b| := by
      simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Complex.re_sum,
        Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, ← sum_sub_distrib, ← mul_sub]
      simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
        abs_sum_le_sum_abs (fun s => (p s).toReal * (L s a b - R s a b)) univ
    calc
      _ ≤ ∑ a, ∑ b, ∑ s, (p s).toReal * |L s a b - R s a b| :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hsplit a b
      _ = ∑ s, (p s).toReal * ∑ a, ∑ b, |L s a b - R s a b| := by
        calc
          _ = ∑ a, ∑ s, ∑ b, (p s).toReal * |L s a b - R s a b| :=
            sum_congr rfl fun _ _ => sum_comm
          _ = ∑ s, ∑ a, ∑ b, (p s).toReal * |L s a b - R s a b| := sum_comm
          _ = _ := by simp only [mul_sum]
      _ ≤ ∑ s, (p s).toReal * (2 * √(E x s) + 2 * √(E y s)) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (POVM.sum_abs_trace_sequential_sub_product_le (hρ s) (P x) (P y) (Q s x) (Q s y)
            (hQ s x) (hP y) (hQ s y) (hc s x)) ENNReal.toReal_nonneg
      _ = _ := by simp only [V, mul_add, mul_sum, sum_add_distrib, mul_left_comm _ (2 : ℝ)]
  calc
    _ ≤ ∑ q : X × X, (μ q).toReal * (2 * (V q.1 + V q.2)) :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hrow q.1 q.2) ENNReal.toReal_nonneg
    _ = 4 * ∑ x, (M x).toReal * V x := by
      simp only [mul_left_comm _ (2 : ℝ), ← mul_sum, mul_add, sum_add_distrib]
      rw [← Cslib.Probability.PMF.sum_map_mul μ Prod.fst V,
        ← Cslib.Probability.PMF.sum_map_mul μ Prod.snd V, hμ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hV x) ENNReal.toReal_nonneg).trans hW

section Cut

open scoped ComplexOrder

local notation "Cuts" => {s : Finset κ // Finset.Nonempty s}

private abbrev cutEquiv (s : Finset κ) := Equiv.Set.sumCompl (s : Set κ)

private noncomputable def cutLift [DecidableEq A] (s : Finset κ) (a₀ : A)
    (M : POVM A {i : κ // i ∈ s}) : POVM A κ :=
  (M.directSum (POVM.const a₀)).reindex (cutEquiv s)

private theorem cutLift_projective [DecidableEq A] (s : Finset κ) (a₀ : A)
    (M : POVM A {i : κ // i ∈ s}) (hM : M.toMeasurement.IsProjective) :
    (cutLift s a₀ M).toMeasurement.IsProjective := by
  intro a
  let N : POVM A ((s : Set κ)ᶜ : Set κ) := POVM.const a₀
  let L := reindexAlgEquiv ℂ ℂ (cutEquiv s)
  change L ((M.directSum N).effect a) * L ((M.directSum N).effect a) =
    L ((M.directSum N).effect a)
  rw [← map_mul, (M.directSum_effect_mul_self N a) (hM a)]
  dsimp only [N, POVM.const]
  split_ifs <;> simp

private theorem cutLift_effect [DecidableEq A] (s : Finset κ) (a₀ : A)
    (M : POVM A s) (a : A) :
    (cutLift s a₀ M).effect a = reindexAlgEquiv ℂ ℂ (cutEquiv s)
      (fromBlocks (M.effect a) 0 0 ((POVM.const a₀).effect a)) := by
  unfold cutLift
  change reindexAlgEquiv ℂ ℂ (cutEquiv s) ((M.directSum (POVM.const a₀)).effect a) = _
  rw [POVM.directSum_effect]

private theorem extendCutMatrix_eq_reindex (s : Finset κ) (M : Matrix s s ℂ) :
    extendCutMatrix s M = reindexAlgEquiv ℂ ℂ (cutEquiv s) (fromBlocks M 0 0 0) := by
  let e := cutEquiv s
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  change extendCutMatrix s M (e i) (e j) = fromBlocks M 0 0 0 (e.symm (e i)) (e.symm (e j))
  rw [e.symm_apply_apply, e.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    change extendCutMatrix s M (i : κ) (j : κ) = _
  · simp [extendCutMatrix, show (i : κ) ∈ s from i.property,
      show (j : κ) ∈ s from j.property]
  · simp [extendCutMatrix, show (i : κ) ∈ s from i.property,
      show (j : κ) ∉ s from j.property]
  · simp [extendCutMatrix, show (i : κ) ∉ s from i.property]
  · simp [extendCutMatrix, show (i : κ) ∉ s from i.property]

private theorem spectralCutDensity_eq_reindex (s : Cuts) :
    spectralCutDensity s = ((s.val.card : ℝ)⁻¹) •
      reindexAlgEquiv ℂ ℂ (cutEquiv s.val) (fromBlocks (1 : Matrix s.val s.val ℂ) 0 0 0) := by
  unfold spectralCutDensity
  congr 1
  rw [← extendCutMatrix_eq_reindex]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ s.val <;> simp [extendCutMatrix, hi]
  · by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val <;>
      simp [extendCutMatrix, hi, hj, Subtype.ext_iff, hij]

private theorem cutLift_mul_density [DecidableEq A] (s : Cuts) (a₀ : A)
    (M : POVM A s.val) (a : A) :
    (cutLift s.val a₀ M).effect a * spectralCutDensity s =
      (s.val.card : ℝ)⁻¹ • extendCutMatrix s.val (M.effect a) := by
  let L := reindexAlgEquiv ℂ ℂ (cutEquiv s.val)
  rw [spectralCutDensity_eq_reindex, Matrix.mul_smul, extendCutMatrix_eq_reindex, cutLift_effect]
  change (s.val.card : ℝ)⁻¹ •
    (L (fromBlocks (M.effect a) 0 0 ((POVM.const a₀).effect a)) * L (fromBlocks 1 0 0 0)) =
      (s.val.card : ℝ)⁻¹ • L (fromBlocks (M.effect a) 0 0 0)
  rw [← map_mul, fromBlocks_multiply]
  simp [Matrix.mul_zero]

private theorem density_mul_cutLift [DecidableEq A] (s : Cuts) (a₀ : A)
    (M : POVM A s.val) (a : A) :
    spectralCutDensity s * (cutLift s.val a₀ M).effect a =
      (s.val.card : ℝ)⁻¹ • extendCutMatrix s.val (M.effect a) := by
  let L := reindexAlgEquiv ℂ ℂ (cutEquiv s.val)
  rw [spectralCutDensity_eq_reindex, Matrix.smul_mul, extendCutMatrix_eq_reindex, cutLift_effect]
  change (s.val.card : ℝ)⁻¹ •
    (L (fromBlocks 1 0 0 0) * L (fromBlocks (M.effect a) 0 0 ((POVM.const a₀).effect a))) =
      (s.val.card : ℝ)⁻¹ • L (fromBlocks (M.effect a) 0 0 0)
  rw [← map_mul, fromBlocks_multiply]
  simp [Matrix.mul_zero, Matrix.zero_mul]

private theorem trace_extendCutMatrix (s : Finset κ) (B : Matrix s s ℂ) :
    (extendCutMatrix s B).trace = B.trace := by
  let e := cutEquiv s
  rw [extendCutMatrix_eq_reindex]
  change (∑ i, fromBlocks B 0 0 0 (e.symm i) (e.symm i)) = B.trace
  rw [Equiv.sum_comp e.symm (fun i => fromBlocks B 0 0 0 i i)]
  simp [Fintype.sum_sum_type, Matrix.trace, diag_apply]

private theorem cutLift_mul_extend [DecidableEq A] (s : Finset κ) (a₀ : A)
    (M : POVM A s) (a : A) (B : Matrix s s ℂ) :
    (cutLift s a₀ M).effect a * extendCutMatrix s B = extendCutMatrix s (M.effect a * B) := by
  rw [cutLift_effect, extendCutMatrix_eq_reindex, extendCutMatrix_eq_reindex, ← map_mul,
    fromBlocks_multiply]
  simp [Matrix.zero_mul, Matrix.mul_zero]

private theorem extendCutMatrix_mul_density (s : Cuts) (B : Matrix s.val s.val ℂ) :
    extendCutMatrix s.val B * spectralCutDensity s =
      (s.val.card : ℝ)⁻¹ • extendCutMatrix s.val B := by
  rw [spectralCutDensity_eq_reindex, Matrix.mul_smul, extendCutMatrix_eq_reindex, ← map_mul,
    fromBlocks_multiply]
  simp [Matrix.mul_zero]

private theorem density_mul_extendCutMatrix (s : Cuts) (B : Matrix s.val s.val ℂ) :
    spectralCutDensity s * extendCutMatrix s.val B =
      (s.val.card : ℝ)⁻¹ • extendCutMatrix s.val B := by
  rw [spectralCutDensity_eq_reindex, Matrix.smul_mul, extendCutMatrix_eq_reindex, ← map_mul,
    fromBlocks_multiply]
  simp [Matrix.zero_mul, Matrix.mul_zero]

private theorem cutLift_product_trace [DecidableEq A] (s : Cuts) (a₀ : A)
    (M N : POVM A s.val) (a b : A) :
    (((cutLift s.val a₀ M).effect a * (cutLift s.val a₀ N).effect b) *
      spectralCutDensity s).trace.re =
      (s.val.card : ℝ)⁻¹ * (M.effect a * N.effect b).trace.re := by
  rw [Matrix.mul_assoc, cutLift_mul_density, Matrix.mul_smul, cutLift_mul_extend,
    Matrix.trace_smul, trace_extendCutMatrix, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem cutLift_error_trace [DecidableEq A] (s : Cuts) (a₀ : A)
    (M : POVM A s.val) (a : A) (P : Matrix κ κ ℂ) :
    let E := P - (cutLift s.val a₀ M).effect a
    let F := P - extendCutMatrix s.val (M.effect a)
    (E * E * spectralCutDensity s).trace = (F * F * spectralCutDensity s).trace := by
  intro E F
  let ρ := spectralCutDensity s
  have hright : E * ρ = F * ρ := by
    dsimp only [E, F, ρ]
    rw [Matrix.sub_mul, Matrix.sub_mul, cutLift_mul_density, extendCutMatrix_mul_density]
  have hleft : ρ * E = ρ * F := by
    dsimp only [E, F, ρ]
    rw [Matrix.mul_sub, Matrix.mul_sub, density_mul_cutLift, density_mul_extendCutMatrix]
  change (E * E * ρ).trace = (F * F * ρ).trace
  rw [Matrix.mul_assoc, hright, Matrix.trace_mul_comm E, Matrix.mul_assoc F, hleft,
    ← Matrix.mul_assoc F]
  exact Matrix.trace_mul_cycle F ρ F

private theorem exists_lifted_cut_measurements (s : Cuts) (a₀ : A)
    (M : X → POVM A s.val) (hM : ∀ x, (M x).toMeasurement.IsProjective)
    (U : Matrix κ κ ℂ) (hU : U ∈ unitaryGroup κ ℂ) :
    let ρ := U * spectralCutDensity s * Uᴴ
    ∃ L : X → POVM A κ,
      (∀ x, (L x).toMeasurement.IsProjective) ∧
      (∀ x a, Commute ((L x).effect a) ρ) ∧
      (∀ x y a b, (((L x).effect a * (L y).effect b) * ρ).trace.re =
        (s.val.card : ℝ)⁻¹ * ((M x).effect a * (M y).effect b).trace.re) ∧
      ∀ x a (P : Matrix κ κ ℂ),
        let E := P - (L x).effect a
        let F := P - U * extendCutMatrix s.val ((M x).effect a) * Uᴴ
        (E * E * ρ).trace = (F * F * ρ).trace := by
  classical
  intro ρ
  let π := Unitary.conjStarAlgAut ℂ (Matrix κ κ ℂ) ⟨U, hU⟩
  have hπ (B : Matrix κ κ ℂ) : π B = U * B * Uᴴ := by
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have ht (B : Matrix κ κ ℂ) : (π B).trace = B.trace := by
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hUstar : Uᴴ ∈ unitaryGroup κ ℂ := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hU
  let Q (x : X) := (cutLift s.val a₀ (M x)).comap Uᴴ hUstar
  have hQ (x : X) (a : A) : (Q x).effect a = π ((cutLift s.val a₀ (M x)).effect a) := by
    rw [hπ]
    change Uᴴᴴ * (cutLift s.val a₀ (M x)).effect a * Uᴴ = _
    rw [conjTranspose_conjTranspose]
  have hρ : ρ = π (spectralCutDensity s) := (hπ _).symm
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro x a
    simp only [POVM.toMeasurement_effect, hQ, ← map_mul]
    exact congrArg π (cutLift_projective s.val a₀ (M x) (hM x) a)
  · intro x a
    change (Q x).effect a * ρ = ρ * (Q x).effect a
    rw [hQ, hρ, ← map_mul, ← map_mul, cutLift_mul_density, density_mul_cutLift]
  · intro x y a b
    rw [hQ, hQ, hρ, ← map_mul, ← map_mul, ht, cutLift_product_trace]
  · intro x a P
    obtain ⟨P', hP'⟩ := π.surjective P
    let B := (cutLift s.val a₀ (M x)).effect a
    let C := extendCutMatrix s.val ((M x).effect a)
    change ((P - (Q x).effect a) * (P - (Q x).effect a) * ρ).trace =
      ((P - U * C * Uᴴ) * (P - U * C * Uᴴ) * ρ).trace
    rw [← hP', hQ, hρ, ← hπ]
    change ((π P' - π B) * (π P' - π B) * π (spectralCutDensity s)).trace =
      ((π P' - π C) * (π P' - π C) * π (spectralCutDensity s)).trace
    simp only [← map_sub, ← map_mul, ht]
    exact cutLift_error_trace s a₀ (M x) a P'

private theorem nonempty_answers_of_marginal (S : QuantumStrategy X X A A ι κ)
    (ν : PMF X) : Nonempty A := by
  obtain ⟨x, _⟩ := ν.support_nonempty
  by_contra he
  let _ := not_nonempty_iff.mp he
  simpa using S.sum_prob x x

/-- A projective strategy is close in average joint answer probabilities to a mixture of
synchronous projective strategies on spectral cuts of the second system. The common question
marginal determines the synchrony defect, and the bound is independent of the dimensions and
answer count. -/
theorem exists_synchronous_cut_correlation_mixture [Fintype X]
    (S : QuantumStrategy X X A A ι κ) (ν : PMF X)
    (hP : ∀ x, (S.alice x).toMeasurement.IsProjective)
    (hR : ∀ x, (S.bob x).toMeasurement.IsProjective) :
    let δ := S.synchronyDefect ν
    ∃ (p : PMF Cuts) (T : (s : Cuts) → QuantumStrategy X X A A s.val s.val),
      (∀ s x, ((T s).alice x).toMeasurement.IsProjective) ∧
      (∀ s x, ((T s).bob x).toMeasurement.IsProjective) ∧
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∀ s x y a b, (T s).prob x y a b =
        (s.val.card : ℝ)⁻¹ *
          (((T s).alice x).effect a * ((T s).alice y).effect b).trace.re) ∧
      ∀ μ : PMF (X × X), μ.map Prod.fst = ν → μ.map Prod.snd = ν →
      (∑ q, (μ q).toReal * ∑ a, ∑ b,
        |S.prob q.1 q.2 a b - ∑ s, (p s).toReal * (T s).prob q.1 q.2 a b|) ≤
        2 * √(2 * δ) + 4 * √(18 * δ + 20 * √δ) := by
  classical
  intro δ
  obtain ⟨d, U, hU, hexists⟩ := S.exists_bob_projective_spectral_mixture
  obtain ⟨T, hTa, hTb, hsync, hprob, _, hw, hsum, hρ, herr⟩ := hexists ν
  let ρ (s : Cuts) := U * spectralCutDensity s * Uᴴ
  have hρs (s : Cuts) : IsDensityMatrix (ρ s) :=
    (spectralCutDensity_isDensityMatrix s).conj_unitary hU
  let p : PMF Cuts := PMF.ofFintype (fun s => ENNReal.ofReal (spectralCutWeight d s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s), hsum, ENNReal.ofReal_one])
  have hp (s : Cuts) : (p s).toReal = spectralCutWeight d s := by
    simp only [p, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw s)]
  let a₀ := Classical.choice (nonempty_answers_of_marginal S ν)
  choose L hL hLc hLp hLe using fun s =>
    exists_lifted_cut_measurements s a₀ (T s).alice (hTa s) U hU
  have hident (s : Cuts) (x y : X) (a b : A) :
      (((L s x).effect a * (L s y).effect b) * ρ s).trace.re = (T s).prob x y a b :=
    (hLp s x y a b).trans (hprob s x y a b).symm
  have hErrTerm (s : Cuts) (x : X) (a : A) :
      let E := (S.bob x).effect a - (L s x).effect a
      let F := (S.bob x).effect a - U * extendCutMatrix s.val (((T s).alice x).effect a) * Uᴴ
      (E * E * ρ s).trace.re = (F * F * ρ s).trace.re :=
    congrArg Complex.re (hLe s x a ((S.bob x).effect a))
  have hErr :
      (∑ x, (ν x).toReal * ∑ s, (p s).toReal * ∑ a,
        (((S.bob x).effect a - (L s x).effect a) * ((S.bob x).effect a - (L s x).effect a) *
          ρ s).trace.re) ≤ 18 * δ + 20 * √δ := by
    simp_rw [hp, hErrTerm]
    exact herr
  have hDensity : (∑ s, (p s).toReal • ρ s) = partialTraceLeft (pureState S.state) := by
    simp_rw [hp]
    exact hρ.symm
  refine ⟨p, T, hTa, hTb, hsync, hprob, ?_⟩
  intro μ hfst hsnd
  have hSpectral := sum_abs_sequential_sub_mixture_le S.bob L ρ hρs p μ
    (hsnd.trans hfst.symm) hR hL hLc
  simp_rw [hident] at hSpectral
  rw [hDensity, hfst] at hSpectral
  have hSwitch := S.sum_abs_prob_sub_bob_sequential_le μ hP
  rw [hfst] at hSwitch
  refine le_trans ?_ (add_le_add hSwitch
    (hSpectral.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hErr) (by norm_num))))
  simp only [← sum_add_distrib, ← mul_add]
  exact sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun _ _ => sum_le_sum fun _ _ => abs_sub_le _ _ _) ENNReal.toReal_nonneg

end Cut

section Dilation

open scoped ComplexOrder

local notation "DilatedCuts" => {s : Finset (κ × A) // Finset.Nonempty s}

/-- Vidick's correlation approximation [Vidick2022, Corollary 3.3, arXiv v3, pp. 12–13].
For a finite tensor strategy and a fixed question marginal, one finite convex mixture of
projective synchronous correlations approximates its joint answer probabilities for every
coupling of the marginal with itself.
The approximation is dimension- and answer-independent. Naimark dilation preserves the
probabilities exactly, so the measurements of the original strategy may be arbitrary POVMs. -/
theorem exists_synchronous_correlation_mixture [Fintype X] [DecidableEq A]
    (S : QuantumStrategy X X A A ι κ) (ν : PMF X) :
    let δ := S.synchronyDefect ν
    ∃ (p : PMF DilatedCuts) (T : (s : DilatedCuts) → QuantumStrategy X X A A s.val s.val),
      (∀ s x, ((T s).alice x).toMeasurement.IsProjective) ∧
      (∀ s x, ((T s).bob x).toMeasurement.IsProjective) ∧
      (∀ s x a b, a ≠ b → (T s).prob x x a b = 0) ∧
      (∀ s x y a b, (T s).prob x y a b =
        (s.val.card : ℝ)⁻¹ *
          (((T s).alice x).effect a * ((T s).alice y).effect b).trace.re) ∧
      ∀ μ : PMF (X × X), μ.map Prod.fst = ν → μ.map Prod.snd = ν →
      (∑ q, (μ q).toReal * ∑ a, ∑ b,
        |S.prob q.1 q.2 a b - ∑ s, (p s).toReal * (T s).prob q.1 q.2 a b|) ≤
        2 * √(2 * δ) + 4 * √(18 * δ + 20 * √δ) := by
  classical
  let a₀ := Classical.choice (nonempty_answers_of_marginal S ν)
  have h := (S.dilate a₀ a₀).exists_synchronous_cut_correlation_mixture ν
    (S.isProjective_alice_dilate a₀ a₀) (S.isProjective_bob_dilate a₀ a₀)
  simpa only [synchronyDefect_eq_sum, prob_dilate] using h

end Dilation

end Cslib.PCP.QuantumStrategy
