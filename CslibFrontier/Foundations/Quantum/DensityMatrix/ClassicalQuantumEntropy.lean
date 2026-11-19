/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonal
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonalOrder
import CslibFrontier.Probability.Divergence
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Classical–quantum relative entropy

A classical–quantum state stores a probability-weighted quantum state in each diagonal block.
The support test is blockwise, and so is the functional calculus. This gives the relative-entropy
chain rule and the classical–quantum mutual information formula of
[Bavarian, Vidick and Yuen, Propositions 5.6–5.7][BavarianVidickYuen2022]
(arXiv:1509.07466v2, printed pp. 19–20), with natural logarithms.

## Main definitions

* `classicalQuantumState`: the diagonal family of weighted conditional states.
* `mutualInformation`: quantum relative entropy to the product of the marginals.

## Main results

* `supportLE_classicalQuantumState_iff`: support compatibility on positive-mass labels.
* `relativeEntropy_classicalQuantumState`: the chain rule, including infinite divergence.
* `mutualInformation_classicalQuantumState`: the mean divergence from the quantum marginal.
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
    have hweight (x : X) :
        ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) (σ x) =
          ((p x).toReal * relativeEntropyReal (ρ x) (σ x) : ℝ) := by
      by_cases hx : x ∈ p.support
      · rw [relativeEntropy_of_supportLE (hs.2 x hx), WithTop.coe_mul]
      · simp [(p.apply_eq_zero_iff x).mpr hx]
    simp only [hblock, hweight, mul_add, Finset.sum_add_distrib,
      WithTop.coe_add, WithTop.coe_sum]
  · rw [relativeEntropy_of_not_supportLE (fun h => hs (hiff.mp h))]
    by_cases hpq : p.support ⊆ q.support
    · have hn : ¬ ∀ x ∈ p.support, SupportLE (ρ x) (σ x) := fun h => hs ⟨hpq, h⟩
      push Not at hn
      obtain ⟨x, hx, hnx⟩ := hn
      have hnz : ((p x).toReal : WithTop ℝ) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hx, p.apply_ne_top x⟩)
      have htop : (∑ x, ((p x).toReal : WithTop ℝ) * relativeEntropy (ρ x) (σ x)) = ⊤ := by
        refine WithTop.sum_eq_top.mpr ⟨x, mem_univ _, ?_⟩
        rw [relativeEntropy_of_not_supportLE hnx, WithTop.mul_top hnz]
      rw [htop, WithTop.add_top]
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

end Cslib.Quantum
