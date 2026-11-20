/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDataProcessing
import CslibFrontier.Probability.MutualInformation

/-!
# Marginalizing classical–quantum states

A deterministic map of classical labels groups all original blocks with the same
output label. The new block is the sum of their probability-weighted quantum states.
Partial trace also allows discarding part of a quantum register while keeping the
classical labels.

## Main definitions

* `classicalQuantumMarginal`: the state obtained by mapping the classical labels.
* `quantumMarginalGivenMap`: the normalized conditional quantum state after observing a map.

## Main results

* `classicalQuantumMarginal_eq_state`: the grouped blocks have the usual conditional-state form.
* `classicalQuantumMarginal_comp_of_eq`: deterministic classical marginalization composes.
* `mutualInformation_classicalQuantumState_partialTraceRight_le`: discarding a quantum factor
  cannot increase the mutual information with the classical labels.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open Cslib.Probability.PMF (map_equiv_apply map_fst_map_prodMk map_apply_of_injective)

variable {ι κ X Y Z : Type*}
variable [Fintype X] [DecidableEq Y]

/-- The classical marginal along `f`, with each quantum block summed over the appropriate fiber. -/
@[expose] noncomputable def classicalQuantumMarginal (p : PMF X) (ρ : X → Matrix ι ι ℂ)
    (f : X → Y) : Matrix (ι × Y) (ι × Y) ℂ :=
  blockDiagonal fun y => ∑ z ∈ univ.filter (fun x => f x = y), (p z).toReal • ρ z

/-- Condition the quantum register on the observed value of a deterministic map of labels. -/
noncomputable def quantumMarginalGivenMap [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ)
    (f : X → Y) (y : Y) : Matrix ι ι ℂ :=
  quantumMarginalGiven (p.map fun x => (f x, x)) (fun z => ρ z.2) y

/-- The grouped weight equals the classical marginal probability times the normalized
conditional quantum state. -/
theorem smul_quantumMarginalGivenMap [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) (f : X → Y)
    (y : Y) :
    ((p.map f) y).toReal • quantumMarginalGivenMap p ρ f y =
      ∑ x ∈ univ.filter (fun x => f x = y), (p x).toReal • ρ x := by
  let q := p.map fun x => (f x, x)
  have hmap : q.map Prod.fst = p.map f := map_fst_map_prodMk p f
  have happly (x : X) : q (y, x) = if f x = y then p x else 0 := by
    by_cases h : f x = y
    · subst y
      rw [ite_eq_left rfl]
      exact map_apply_of_injective p (fun _ _ he => congrArg Prod.snd he) x
    · rw [ite_eq_right h]
      apply (PMF.apply_eq_zero_iff q (y, x)).2
      intro hx
      obtain ⟨z, _, hz⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      have hz' : z = x := congrArg Prod.snd hz
      exact h (hz' ▸ congrArg Prod.fst hz)
  change ((p.map f) y).toReal • quantumMarginalGiven q (fun z => ρ z.2) y = _
  rw [← hmap, smul_quantumMarginalGiven, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [happly]
  split_ifs <;> simp

/-- The grouped state is the classical–quantum state of the observed law and its conditionals. -/
theorem classicalQuantumMarginal_eq_state [DecidableEq X] (p : PMF X) (ρ : X → Matrix ι ι ℂ)
    (f : X → Y) : classicalQuantumMarginal p ρ f =
      classicalQuantumState (p.map f) (quantumMarginalGivenMap p ρ f) := by
  unfold classicalQuantumMarginal classicalQuantumState
  congr 1
  funext y
  exact (smul_quantumMarginalGivenMap p ρ f y).symm

/-- Classical marginalization is unchanged by a bijective relabelling of its input. -/
theorem classicalQuantumMarginal_map_equiv [Fintype Z] (e : X ≃ Z) (p : PMF X)
    (ρ : X → Matrix ι ι ℂ) (f : X → Y) :
    classicalQuantumMarginal (p.map e) (ρ ∘ e.symm) (f ∘ e.symm) =
      classicalQuantumMarginal p ρ f := by
  unfold classicalQuantumMarginal
  congr 1
  funext y
  simp only [sum_filter]
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  simp only [Function.comp_apply, e.symm_apply_apply, map_equiv_apply]

/-- Grouping the blocks of an already marginalized classical–quantum state composes the
two maps on classical labels. -/
theorem classicalQuantumMarginal_comp_of_eq [Fintype Y] [DecidableEq Z]
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) (f : X → Y)
    (q : PMF Y) (σ : Y → Matrix ι ι ℂ) (g : Y → Z)
    (h : classicalQuantumState q σ = classicalQuantumMarginal p ρ f) :
    classicalQuantumMarginal q σ g = classicalQuantumMarginal p ρ (g ∘ f) := by
  have hblock (y : Y) :
      (q y).toReal • σ y = ∑ x ∈ univ.filter (fun z => f z = y), (p x).toReal • ρ x := by
    ext i j
    have he := congrArg (fun M : Matrix (ι × Y) (ι × Y) ℂ => M (i, y) (j, y)) h
    simpa only [classicalQuantumState, classicalQuantumMarginal, blockDiagonal_apply_eq] using he
  unfold classicalQuantumMarginal
  congr 1
  funext z
  simp only [hblock, sum_fiberwise_eq_sum_filter, Function.comp_apply, mem_filter_univ]

variable [Fintype ι]

omit [DecidableEq Y] in
/-- Conditioning on the observed classical value preserves density normalization. -/
theorem isDensityMatrix_quantumMarginalGivenMap [DecidableEq X]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (h : ∀ x, IsDensityMatrix (ρ x)) (f : X → Y) (y : Y) :
    IsDensityMatrix (quantumMarginalGivenMap p ρ f y) := by
  rw [quantumMarginalGivenMap]
  exact isDensityMatrix_quantumMarginalGiven _ (fun z => h z.2) y

variable [Fintype Y] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Discarding a quantum subsystem cannot increase its mutual information with a classical label. -/
theorem mutualInformation_classicalQuantumState_partialTraceRight_le
    (p : PMF Y) {ρ : Y → Matrix (ι × κ) (ι × κ) ℂ} (hρ : ∀ y, IsDensityMatrix (ρ y)) :
    mutualInformation (classicalQuantumState p (fun y => partialTraceRight (ρ y))) ≤
      mutualInformation (classicalQuantumState p ρ) := by
  have hρ' (y : Y) := (hρ y).partialTraceRight
  have hμ : partialTraceRight (classicalQuantumState p (fun y => partialTraceRight (ρ y))) =
      partialTraceRight (partialTraceRight (classicalQuantumState p ρ)) := by
    rw [partialTraceRight_classicalQuantumState, partialTraceRight_classicalQuantumState,
      partialTraceRight_sum]
    refine sum_congr rfl fun y _ => ?_
    change ((p y).toReal : ℂ) • partialTraceRight (ρ y) =
      partialTraceRight (((p y).toReal : ℂ) • ρ y)
    rw [partialTraceRight_smul]
  rw [mutualInformation_classicalQuantumState_eq_coe_sum p hρ',
    mutualInformation_classicalQuantumState_eq_coe_sum p hρ, WithTop.coe_le_coe, hμ]
  refine sum_le_sum fun y _ => ?_
  by_cases hy : p y = 0
  · simp [hy]
  have hσ := (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight.posSemidef
  have hsup := supportLE_partialTraceRight_classicalQuantumState p hρ hy
  have h := relativeEntropy_partialTraceRight_le (hρ y).posSemidef hσ
  rw [relativeEntropy_of_supportLE (hsup.partialTraceRight hσ),
    relativeEntropy_of_supportLE hsup, WithTop.coe_le_coe] at h
  exact mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg

end Cslib.Quantum
