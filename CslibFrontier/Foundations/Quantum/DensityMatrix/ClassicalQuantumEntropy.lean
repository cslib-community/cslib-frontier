/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
public import CslibFrontier.Probability.Conditioning
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonal
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonalOrder
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Probability.Divergence
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Classical–quantum relative entropy

A classical–quantum state stores a probability-weighted quantum state in each diagonal block.
The support test is blockwise, and so is the functional calculus. This gives the relative-entropy
chain rule and the classical–quantum mutual information formula of
[Bavarian, Vidick and Yuen, Propositions 5.6–5.7][BavarianVidickYuen2022]
(arXiv:1509.07466v2, printed pp. 19–20), with natural logarithms.
Decomposing the divergence to a common reference into its mutual information and
marginal parts gives the case of Proposition 5.9 on printed p. 21 where the source
is classical–quantum and the classical reference marginal is diagonal.
Disintegrating a pair of labels then gives the two-label chain step used in
equation (27) on printed p. 21.

## Main definitions

* `classicalQuantumState`: the diagonal family of weighted conditional states.
* `mutualInformation`: quantum relative entropy to the product of the marginals.

## Main results

* `supportLE_classicalQuantumState_iff`: support compatibility on positive-mass labels.
* `relativeEntropy_classicalQuantumState`: the chain rule, including infinite divergence.
* `mutualInformation_classicalQuantumState`: the mean divergence from the quantum marginal.
* `sum_weighted_relativeEntropy_eq_mutualInformation_add`: decomposition for a common reference.
* `mutualInformation_le_relativeEntropy_classicalQuantumState_const`: the product-reference bound.
* `mutualInformation_classicalQuantumState_prod`: the conditional chain identity for two labels.
-/

public section

namespace Cslib.Quantum

open Matrix Finset InformationTheory
open scoped MatrixOrder ComplexOrder Kronecker

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

/-- A classical–quantum state with quantum coordinate first and classical label second. -/
@[expose] noncomputable def classicalQuantumState (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    Matrix (ι × X) (ι × X) ℂ :=
  blockDiagonal fun x => (p x).toReal • ρ x

/-- A probability-weighted block diagonal of density matrices is a density matrix. -/
theorem isDensityMatrix_classicalQuantumState (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) : IsDensityMatrix (classicalQuantumState p ρ) := by
  classical
  constructor
  · exact posSemidef_blockDiagonal fun x => (hρ x).posSemidef.smul ENNReal.toReal_nonneg
  · rw [classicalQuantumState, trace_blockDiagonal]
    simp only [trace_smul, (hρ _).trace_eq_one, Complex.real_smul, mul_one]
    exact_mod_cast Cslib.Probability.PMF.sum_toReal p

private theorem supportLE_blockDiagonal_iff (A B : X → Matrix ι ι ℂ) :
    SupportLE (blockDiagonal A) (blockDiagonal B) ↔ ∀ x, SupportLE (A x) (B x) := by
  constructor
  · intro h x v hv
    let w (i : ι × X) := if i.2 = x then v i.1 else 0
    have hw : blockDiagonal B *ᵥ w = 0 := by
      funext ⟨i, y⟩
      rw [blockDiagonal_mulVec_apply]
      by_cases hy : y = x
      · subst y
        simpa [w] using congrFun hv i
      · simp [w, hy, mulVec, dotProduct]
    funext i
    have := congrFun (h w hw) (i, x)
    simpa [blockDiagonal_mulVec_apply, w] using this
  · intro h w hw
    funext ⟨i, x⟩
    have hx : B x *ᵥ (fun j => w (j, x)) = 0 := by
      funext j
      simpa only [blockDiagonal_mulVec_apply, Pi.zero_apply] using congrFun hw (j, x)
    rw [blockDiagonal_mulVec_apply]
    exact congrFun (h x _ hx) i

private theorem supportLE_smul_iff {A B : Matrix ι ι ℂ} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    SupportLE (a • A) (b • B) ↔ SupportLE A B := by
  simp only [SupportLE, smul_mulVec, smul_eq_zero, ha, hb, false_or]

/-- Finite support compatibility for classical–quantum states. Blocks of zero source mass
impose no support condition. -/
theorem supportLE_classicalQuantumState_iff (p q : PMF X) {ρ σ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    SupportLE (classicalQuantumState p ρ) (classicalQuantumState q σ) ↔
      p.support ⊆ q.support ∧ ∀ x ∈ p.support, SupportLE (ρ x) (σ x) := by
  classical
  rw [classicalQuantumState, classicalQuantumState, supportLE_blockDiagonal_iff]
  constructor
  · intro h
    have hpq : p.support ⊆ q.support := by
      intro x hx
      by_contra hy
      have hq0 : q x = 0 := (q.apply_eq_zero_iff x).mpr hy
      have hp0 : (p x).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩
      have hz (v : ι → ℂ) : ρ x *ᵥ v = 0 := by
        have hx' := h x v (by simp [hq0])
        simpa only [smul_mulVec, smul_eq_zero, hp0, false_or] using hx'
      have hzero : ρ x = 0 := by
        ext i j
        change ρ x i j = 0
        simpa only [mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using
          congrFun (hz (Pi.single j 1)) i
      have ht := (hρ x).trace_eq_one
      rw [hzero, trace_zero] at ht
      exact zero_ne_one ht
    refine ⟨hpq, fun x hx => ?_⟩
    exact (supportLE_smul_iff (ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hpq hx, q.apply_ne_top x⟩)).mp (h x)
  · rintro ⟨hpq, h⟩ x
    by_cases hx : x ∈ p.support
    · exact (supportLE_smul_iff (ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩)
        (ENNReal.toReal_ne_zero.mpr ⟨hpq hx, q.apply_ne_top x⟩)).mpr (h x hx)
    · simp [SupportLE, (p.apply_eq_zero_iff x).mpr hx]


omit [Fintype ι] in
/-- The quantum marginal of a classical–quantum state is its probability-weighted mixture. -/
theorem partialTraceRight_classicalQuantumState (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    partialTraceRight (classicalQuantumState p ρ) = ∑ x, (p x).toReal • ρ x := by
  ext i j
  simp only [partialTraceRight_apply, classicalQuantumState, blockDiagonal_apply_eq,
    Matrix.sum_apply]

omit [Fintype X] in
/-- The classical marginal of a classical–quantum state is the diagonal of its probabilities. -/
theorem partialTraceLeft_classicalQuantumState (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    partialTraceLeft (classicalQuantumState p ρ) = diagonal fun x => ((p x).toReal : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst y
    rw [partialTraceLeft_apply, diagonal_apply_eq]
    simp only [classicalQuantumState, blockDiagonal_apply_eq]
    change ((p x).toReal • ρ x).trace = _
    rw [trace_smul, (hρ x).trace_eq_one, Complex.real_smul, mul_one]
  · simp [partialTraceLeft_apply, classicalQuantumState, blockDiagonal_apply, h]

variable [DecidableEq ι]

private theorem relativeEntropyReal_blockDiagonal (A B : X → Matrix ι ι ℂ)
    (hA : ∀ x, (A x).IsHermitian) (hB : ∀ x, (B x).IsHermitian) :
    relativeEntropyReal (blockDiagonal A) (blockDiagonal B) =
      ∑ x, relativeEntropyReal (A x) (B x) := by
  unfold relativeEntropyReal
  rw [cfc_blockDiagonal _ _ hA, cfc_blockDiagonal _ _ hB, ← blockDiagonal_sub,
    ← blockDiagonal_mul, trace_blockDiagonal, Complex.re_sum]
  rfl

omit [DecidableEq X] in
private theorem sum_weighted_relativeEntropy_eq_coe (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    {σ : X → Matrix ι ι ℂ} (hs : ∀ x ∈ p.support, SupportLE (ρ x) (σ x)) :
    (∑ x, ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) (σ x)) =
      ((∑ x, (p x).toReal * relativeEntropyReal (ρ x) (σ x) : ℝ) : WithTop ℝ) := by
  rw [WithTop.coe_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ p.support
  · rw [relativeEntropy_of_supportLE (hs x hx), WithTop.coe_mul]
  · simp [(p.apply_eq_zero_iff x).mpr hx]

omit [DecidableEq X] in
private theorem sum_weighted_relativeEntropy_eq_top (p : PMF X) {ρ σ : X → Matrix ι ι ℂ}
    (hs : ¬ ∀ x ∈ p.support, SupportLE (ρ x) (σ x)) :
    (∑ x, ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) (σ x)) = ⊤ := by
  push Not at hs
  obtain ⟨x, hx, hnx⟩ := hs
  refine WithTop.sum_eq_top.mpr ⟨x, mem_univ _, ?_⟩
  have hnz : ((p x).toReal : WithTop ℝ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩)
  rw [relativeEntropy_of_not_supportLE hnx, WithTop.mul_top hnz]

/-- For classical–quantum states, relative entropy splits into the classical KL divergence
and the average conditional quantum relative entropy. All terms are in nats, and zero
source mass contributes zero even when the corresponding block divergence is infinite. -/
theorem relativeEntropy_classicalQuantumState [MeasurableSpace X] [MeasurableSingletonClass X]
    (p q : PMF X) {ρ σ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x))
    (hσ : ∀ x, IsDensityMatrix (σ x)) :
    relativeEntropy (classicalQuantumState p ρ) (classicalQuantumState q σ) =
      (if klDiv p.toMeasure q.toMeasure = ⊤ then ⊤
        else ((klDiv p.toMeasure q.toMeasure).toReal : WithTop ℝ)) +
        ∑ x, ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) (σ x) := by
  classical
  let hiff := supportLE_classicalQuantumState_iff p q hρ (σ := σ)
  by_cases hs : p.support ⊆ q.support ∧ ∀ x ∈ p.support, SupportLE (ρ x) (σ x)
  · have hKL := Cslib.Probability.PMF.sum_mul_log_div_nonneg hs.1
    rw [relativeEntropy_of_supportLE (hiff.mpr hs), classicalQuantumState, classicalQuantumState,
      relativeEntropyReal_blockDiagonal _ _
        (fun x => ((hρ x).posSemidef.smul ENNReal.toReal_nonneg).isHermitian)
        (fun x => ((hσ x).posSemidef.smul ENNReal.toReal_nonneg).isHermitian),
      Cslib.Probability.PMF.klDiv_toMeasure_eq_ofReal hs.1]
    rw [ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hKL]
    have hblock (x : X) :
        relativeEntropyReal ((p x).toReal • ρ x) ((q x).toReal • σ x) =
          (p x).toReal *
            (Real.log ((p x).toReal / (q x).toReal) + relativeEntropyReal (ρ x) (σ x)) := by
      by_cases hx : x ∈ p.support
      · exact relativeEntropyReal_smul (hρ x) (hσ x) (hs.2 x hx)
          (ENNReal.toReal_pos hx (p.apply_ne_top x))
          (ENNReal.toReal_pos (hs.1 hx) (q.apply_ne_top x))
      · simp [(p.apply_eq_zero_iff x).mpr hx, relativeEntropyReal]
    rw [sum_weighted_relativeEntropy_eq_coe p hs.2]
    simp only [hblock, mul_add, Finset.sum_add_distrib, WithTop.coe_add]
  · rw [relativeEntropy_of_not_supportLE (fun h => hs (hiff.mp h))]
    by_cases hpq : p.support ⊆ q.support
    · rw [sum_weighted_relativeEntropy_eq_top p (fun h => hs ⟨hpq, h⟩), WithTop.add_top]
    · have htop : klDiv p.toMeasure q.toMeasure = ⊤ := by
        by_contra hn
        exact hpq (Cslib.Probability.PMF.klDiv_toMeasure_ne_top_iff.mp hn)
      rw [htop]
      simp

/-- Mutual information is relative entropy to the tensor product of the two marginals. -/
noncomputable def mutualInformation (ρ : Matrix (ι × X) (ι × X) ℂ) : WithTop ℝ :=
  relativeEntropy ρ (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ)

/-- The mutual information of a classical–quantum state is the weighted divergence of
the conditional quantum states from their average. -/
theorem mutualInformation_classicalQuantumState (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    mutualInformation (classicalQuantumState p ρ) =
      ∑ x, ((p x).toReal : WithTop ℝ) *
        relativeEntropy (ρ x) (partialTraceRight (classicalQuantumState p ρ)) := by
  let : MeasurableSpace X := ⊤
  let : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  let σ := partialTraceRight (classicalQuantumState p ρ)
  have hσ : IsDensityMatrix σ := (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight
  have hprod : σ ⊗ₖ partialTraceLeft (classicalQuantumState p ρ) =
      classicalQuantumState p (fun _ => σ) := by
    rw [partialTraceLeft_classicalQuantumState p hρ, kronecker_diagonal]
    unfold classicalQuantumState
    congr 1
    funext x
    ext i j
    exact mul_comm _ _
  change relativeEntropy (classicalQuantumState p ρ)
      (σ ⊗ₖ partialTraceLeft (classicalQuantumState p ρ)) = _
  rw [hprod, relativeEntropy_classicalQuantumState p p hρ (fun _ => hσ), klDiv_self]
  simp [σ]

omit [DecidableEq ι] in
/-- Each positive-mass conditional state is supported by the quantum marginal. -/
theorem supportLE_partialTraceRight_classicalQuantumState (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) {x : X} (hx : x ∈ p.support) :
    SupportLE (ρ x) (partialTraceRight (classicalQuantumState p ρ)) := by
  intro v hv
  rw [partialTraceRight_classicalQuantumState] at hv
  exact (mulVec_sum_smul_eq_zero_iff univ (fun y => (p y).toReal) ρ
    (fun _ _ => ENNReal.toReal_nonneg) (fun y _ => (hρ y).posSemidef) v).mp hv x
    (mem_univ _) (ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩)

omit [DecidableEq ι] in
private theorem supportLE_partialTraceRight_classicalQuantumState_iff (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (σ : Matrix ι ι ℂ) :
    SupportLE (partialTraceRight (classicalQuantumState p ρ)) σ ↔
      ∀ x ∈ p.support, SupportLE (ρ x) σ := by
  constructor
  · intro h x hx v hv
    exact supportLE_partialTraceRight_classicalQuantumState p hρ hx v (h v hv)
  · intro h v hv
    rw [partialTraceRight_classicalQuantumState, sum_mulVec]
    refine sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ p.support
    · rw [smul_mulVec, h x hx v hv, smul_zero]
    · simp [(p.apply_eq_zero_iff x).mpr hx]

/-- The expected divergence to a common reference is the mutual information plus the
divergence of the quantum marginal to that reference. The identity includes infinite terms. -/
theorem sum_weighted_relativeEntropy_eq_mutualInformation_add (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (σ : Matrix ι ι ℂ) :
    (∑ x, ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) σ) =
      mutualInformation (classicalQuantumState p ρ) +
        relativeEntropy (partialTraceRight (classicalQuantumState p ρ)) σ := by
  let μ := partialTraceRight (classicalQuantumState p ρ)
  have hμ : ∀ x ∈ p.support, SupportLE (ρ x) μ :=
    fun _ hx => supportLE_partialTraceRight_classicalQuantumState p hρ hx
  have hiff := supportLE_partialTraceRight_classicalQuantumState_iff p hρ σ
  by_cases hs : SupportLE μ σ
  · rw [mutualInformation_classicalQuantumState p hρ, sum_weighted_relativeEntropy_eq_coe p hμ,
      sum_weighted_relativeEntropy_eq_coe p (hiff.mp hs), relativeEntropy_of_supportLE hs,
      ← WithTop.coe_add]
    congr 1
    let L := cfc Real.log μ - cfc Real.log σ
    have hsplit (A : Matrix ι ι ℂ) :
        relativeEntropyReal A σ = relativeEntropyReal A μ + (A * L).trace.re := by
      simp only [relativeEntropyReal, L, mul_sub, trace_sub, Complex.sub_re]
      ring
    have hself : relativeEntropyReal μ μ = 0 := by simp [relativeEntropyReal]
    rw [hsplit μ, hself, zero_add]
    simp_rw [hsplit (ρ _), mul_add, sum_add_distrib]
    have hlin : (μ * L).trace.re = ∑ x, (p x).toReal * (ρ x * L).trace.re := by
      change (partialTraceRight (classicalQuantumState p ρ) * L).trace.re = _
      rw [partialTraceRight_classicalQuantumState, Finset.sum_mul, trace_sum, Complex.re_sum]
      simp only [Matrix.smul_mul, trace_smul, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hlin]
  · rw [relativeEntropy_of_not_supportLE hs, WithTop.add_top]
    exact sum_weighted_relativeEntropy_eq_top p (fun h => hs (hiff.mpr h))

/-- Relative entropy to a product reference bounds the mutual information plus
the divergence of the quantum marginal from the common quantum reference. -/
theorem mutualInformation_add_relativeEntropy_le_relativeEntropy_classicalQuantumState_const
    [MeasurableSpace X] [MeasurableSingletonClass X] (p q : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x))
    {σ : Matrix ι ι ℂ} (hσ : IsDensityMatrix σ) :
    mutualInformation (classicalQuantumState p ρ) +
      relativeEntropy (partialTraceRight (classicalQuantumState p ρ)) σ ≤
      relativeEntropy (classicalQuantumState p ρ) (classicalQuantumState q (fun _ => σ)) := by
  rw [relativeEntropy_classicalQuantumState p q hρ (fun _ => hσ),
    sum_weighted_relativeEntropy_eq_mutualInformation_add p hρ]
  apply le_add_of_nonneg_left
  split
  · exact le_top
  · exact_mod_cast ENNReal.toReal_nonneg

/-- For a classical–quantum source, the divergence to a product reference bounds
the mutual information. -/
theorem mutualInformation_le_relativeEntropy_classicalQuantumState_const
    [MeasurableSpace X] [MeasurableSingletonClass X] (p q : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x))
    {σ : Matrix ι ι ℂ} (hσ : IsDensityMatrix σ) :
    mutualInformation (classicalQuantumState p ρ) ≤
      relativeEntropy (classicalQuantumState p ρ) (classicalQuantumState q (fun _ => σ)) :=
  (le_add_of_nonneg_right (relativeEntropy_nonneg
    (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight hσ)).trans
    (mutualInformation_add_relativeEntropy_le_relativeEntropy_classicalQuantumState_const
      p q hρ hσ)

/-- For a classical–quantum state all active blocks have finite divergence to the quantum
marginal, so the mutual information is the lift of an ordinary real sum. -/
theorem mutualInformation_classicalQuantumState_eq_coe_sum (p : PMF X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    mutualInformation (classicalQuantumState p ρ) =
      ((∑ x, (p x).toReal * relativeEntropyReal (ρ x)
        (partialTraceRight (classicalQuantumState p ρ)) : ℝ) : WithTop ℝ) := by
  rw [mutualInformation_classicalQuantumState p hρ]
  exact sum_weighted_relativeEntropy_eq_coe p fun _ hx =>
    supportLE_partialTraceRight_classicalQuantumState p hρ hx

/-- A deterministic classical label carries no information about its quantum register. -/
theorem mutualInformation_classicalQuantumState_pure (x : X)
    {ρ : X → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    mutualInformation (classicalQuantumState (PMF.pure x) ρ) = 0 := by
  have hquantum : partialTraceRight (classicalQuantumState (PMF.pure x) ρ) = ρ x := by
    rw [partialTraceRight_classicalQuantumState]
    simp [PMF.pure_apply, apply_ite, ite_smul, eq_comm]
  rw [mutualInformation_classicalQuantumState _ hρ, hquantum]
  simp [PMF.pure_apply, apply_ite, ite_mul, eq_comm]

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open Cslib.Probability.PMF
  (conditionalSnd marginal_mul_conditionalSnd mem_support_conditionalSnd_iff)

/-- The quantum marginal after fixing the first of two classical labels. -/
@[expose] noncomputable def quantumMarginalGiven (p : PMF (X × Y))
    (ρ : X × Y → Matrix ι ι ℂ) (x : X) : Matrix ι ι ℂ :=
  partialTraceRight (classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y)))

omit [Fintype X] [DecidableEq X] [DecidableEq ι] in
/-- Conditional quantum marginals of density matrices are density matrices, including at a
zero-mass first label. -/
theorem isDensityMatrix_quantumMarginalGiven (p : PMF (X × Y))
    {ρ : X × Y → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z)) (x : X) :
    IsDensityMatrix (quantumMarginalGiven p ρ x) :=
  (isDensityMatrix_classicalQuantumState (conditionalSnd p x) fun y =>
    hρ (x, y)).partialTraceRight

omit [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] in
/-- The block obtained by weighting a conditional quantum marginal is the sum of the
corresponding joint blocks, including at a null first label. -/
theorem smul_quantumMarginalGiven (p : PMF (X × Y)) (ρ : X × Y → Matrix ι ι ℂ) (x : X) :
    ((p.map Prod.fst) x).toReal • quantumMarginalGiven p ρ x =
      ∑ y, (p (x, y)).toReal • ρ (x, y) := by
  rw [quantumMarginalGiven, partialTraceRight_classicalQuantumState, Finset.smul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [smul_smul, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]

omit [Fintype ι] [DecidableEq ι] in
/-- Averaging the conditional quantum marginals recovers the original quantum marginal. -/
theorem partialTraceRight_classicalQuantumState_map_fst (p : PMF (X × Y))
    (ρ : X × Y → Matrix ι ι ℂ) :
    partialTraceRight (classicalQuantumState (p.map Prod.fst) (quantumMarginalGiven p ρ)) =
      partialTraceRight (classicalQuantumState p ρ) := by
  rw [partialTraceRight_classicalQuantumState, partialTraceRight_classicalQuantumState,
    Fintype.sum_prod_type]
  exact sum_congr rfl fun x _ => smul_quantumMarginalGiven p ρ x

/-- The mutual information of two classical labels with a quantum register splits into the
information of the first label and the average information of the second label given the first.
The conditional law at an unsupported first label is multiplied by zero. -/
theorem mutualInformation_classicalQuantumState_prod (p : PMF (X × Y))
    {ρ : X × Y → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    mutualInformation (classicalQuantumState p ρ) =
      mutualInformation (classicalQuantumState (p.map Prod.fst) (quantumMarginalGiven p ρ)) +
        ∑ x, (((p.map Prod.fst) x).toReal : WithTop ℝ) *
          mutualInformation (classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y))) := by
  let μ := partialTraceRight (classicalQuantumState p ρ)
  let ν := p.map Prod.fst
  let μx := quantumMarginalGiven p ρ
  have hμx (x : X) : IsDensityMatrix (μx x) := isDensityMatrix_quantumMarginalGiven p hρ x
  have hsplit (x : X) (hx : x ∈ ν.support) :
      (∑ y, (conditionalSnd p x y).toReal * relativeEntropyReal (ρ (x, y)) μ) =
        relativeEntropyReal (μx x) μ +
          ∑ y, (conditionalSnd p x y).toReal * relativeEntropyReal (ρ (x, y)) (μx x) := by
    have hs (y : Y) (hy : y ∈ (conditionalSnd p x).support) : SupportLE (ρ (x, y)) μ :=
      supportLE_partialTraceRight_classicalQuantumState p hρ
        ((mem_support_conditionalSnd_iff p x hx y).mp hy)
    have hm : SupportLE (μx x) μ :=
      (supportLE_partialTraceRight_classicalQuantumState_iff
        (conditionalSnd p x) (fun y => hρ (x, y)) μ).mpr hs
    have h := sum_weighted_relativeEntropy_eq_mutualInformation_add (conditionalSnd p x)
      (fun y => hρ (x, y)) μ
    have hm' : SupportLE
        (partialTraceRight (classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y)))) μ :=
      hm
    rw [sum_weighted_relativeEntropy_eq_coe _ hs,
      mutualInformation_classicalQuantumState_eq_coe_sum _ (fun y => hρ (x, y)),
      relativeEntropy_of_supportLE hm', ← WithTop.coe_add] at h
    exact ((WithTop.coe_injective h).trans (add_comm _ _))
  rw [mutualInformation_classicalQuantumState_eq_coe_sum p hρ,
    mutualInformation_classicalQuantumState_eq_coe_sum (p.map Prod.fst) hμx,
    partialTraceRight_classicalQuantumState_map_fst]
  simp_rw [mutualInformation_classicalQuantumState_eq_coe_sum (conditionalSnd p _)
      (fun y => hρ (_, y)),
    ← WithTop.coe_mul, ← WithTop.coe_sum, ← WithTop.coe_add]
  apply congrArg ((↑) : ℝ → WithTop ℝ)
  rw [Fintype.sum_prod_type, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  change (∑ y, (p (x, y)).toReal * relativeEntropyReal (ρ (x, y)) μ) =
    (ν x).toReal * relativeEntropyReal (μx x) μ +
      (ν x).toReal * ∑ y, (conditionalSnd p x y).toReal * relativeEntropyReal (ρ (x, y)) (μx x)
  have he :
      (∑ y, (p (x, y)).toReal * relativeEntropyReal (ρ (x, y)) μ) =
        (ν x).toReal * ∑ y, (conditionalSnd p x y).toReal * relativeEntropyReal (ρ (x, y)) μ := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
  rw [he, ← mul_add]
  by_cases hx : x ∈ ν.support
  · rw [hsplit x hx]
  · simp [(ν.apply_eq_zero_iff x).mpr hx]

end Cslib.Quantum
