/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
import CslibFrontier.Probability.PMF.Support
import Mathlib.Algebra.BigOperators.WithTop

/-!
# The classical–quantum mutual-information chain rule

For a tuple of classical labels and a quantum register, split off the first label and
apply the two-label chain rule. Repeating this on the tail gives the sum of the mutual
informations of each coordinate with the quantum register, conditioned on the preceding
coordinates. This is the chain identity in equation (27) of
[Bavarian, Vidick and Yuen][BavarianVidickYuen2022] (arXiv:1509.07466v2, printed p. 21).

## Main definitions

* `coordinateMutualInformationTerms`: the conditional information terms in tuple order.

## Main results

* `mutualInformation_classicalQuantumState_map_equiv`: invariance under a bijection of labels.
* `mutualInformation_classicalQuantumState_eq_sum_coordinates`: the finite-tuple chain rule.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open Cslib.Probability.PMF (conditionalSnd map_apply_of_injective map_eq_pure_iff)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bijectively relabelling the classical blocks preserves mutual information. -/
theorem mutualInformation_classicalQuantumState_map_equiv
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    mutualInformation (classicalQuantumState (p.map e) (ρ ∘ e.symm)) =
      mutualInformation (classicalQuantumState p ρ) := by
  have hm : partialTraceRight (classicalQuantumState (p.map e) (ρ ∘ e.symm)) =
      partialTraceRight (classicalQuantumState p ρ) := by
    rw [partialTraceRight_classicalQuantumState, partialTraceRight_classicalQuantumState]
    refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
    rw [map_apply_of_injective p e.injective, Function.comp_apply, e.symm_apply_apply]
  rw [mutualInformation_classicalQuantumState_eq_coe_sum (p.map e)
      (ρ := ρ ∘ e.symm) (fun y => hρ (e.symm y)),
    mutualInformation_classicalQuantumState_eq_coe_sum p hρ, hm]
  apply congrArg ((↑) : ℝ → WithTop ℝ)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_apply_of_injective p e.injective, Function.comp_apply, e.symm_apply_apply]

private theorem coe_untopD_mutualInformation {X : Type*} [Fintype X] [DecidableEq X]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    (↑((mutualInformation (classicalQuantumState p ρ)).untopD 0) : WithTop ℝ) =
      mutualInformation (classicalQuantumState p ρ) := by
  rw [mutualInformation_classicalQuantumState_eq_coe_sum p hρ, WithTop.untopD_coe]

universe u

/-- Each term is the mutual information of that coordinate and the quantum register averaged
over the preceding labels. The recursion disintegrates at the first coordinate. A zero-mass
label contributes zero, regardless of the fallback conditional law. For density matrices all
mutual-information values used here are finite. -/
@[expose] noncomputable def coordinateMutualInformationTerms :
    {n : ℕ} → (X : Fin n → Type u) → [∀ i, Fintype (X i)] → [∀ i, DecidableEq (X i)] →
    PMF (∀ i, X i) → ((∀ i, X i) → Matrix ι ι ℂ) → Fin n → ℝ
  | 0, _, _, _, _, _ => Fin.elim0
  | _n + 1, X, _, _, p, ρ =>
    let e := Fin.consEquiv X
    let q := p.map e.symm
    let σ := ρ ∘ e
    Fin.cons ((mutualInformation
      (classicalQuantumState (q.map Prod.fst) (quantumMarginalGiven q σ))).untopD 0)
      (fun i => ∑ x, ((q.map Prod.fst) x).toReal *
        coordinateMutualInformationTerms (fun j => X j.succ) (conditionalSnd q x)
          (fun y => σ (x, y)) i)

/-- The mutual information of a tuple and a quantum register is the sum of the information
of each coordinate given its predecessors. The empty tuple has zero information. -/
theorem mutualInformation_classicalQuantumState_eq_sum_coordinates
    {n : ℕ} (X : Fin n → Type u) [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : PMF (∀ i, X i)) {ρ : (∀ i, X i) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) :
    mutualInformation (classicalQuantumState p ρ) =
      ((∑ i, coordinateMutualInformationTerms X p ρ i : ℝ) : WithTop ℝ) := by
  induction n with
  | zero =>
    let z₀ : ∀ i, X i := fun i => i.elim0
    have hp : p.map id = PMF.pure z₀ :=
      map_eq_pure_iff.mpr fun z _ => funext fun i => i.elim0
    rw [PMF.map_id] at hp
    rw [hp, mutualInformation_classicalQuantumState_pure z₀ hρ]
    simp
  | succ n ih =>
    let e := Fin.consEquiv X
    let q := p.map e.symm
    let σ := ρ ∘ e
    have hσ (z : X 0 × (∀ i : Fin n, X i.succ)) : IsDensityMatrix (σ z) := hρ (e z)
    have htail (x : X 0) :
        (∑ i, coordinateMutualInformationTerms (fun j => X j.succ)
          (conditionalSnd q x) (fun y => σ (x, y)) i) =
          (mutualInformation
            (classicalQuantumState (conditionalSnd q x) (fun y => σ (x, y)))).untopD 0 := by
      rw [ih _ _ (fun y => hσ (x, y)), WithTop.untopD_coe]
    have hsum :
        (∑ i, coordinateMutualInformationTerms X p ρ i) =
          (mutualInformation
            (classicalQuantumState (q.map Prod.fst) (quantumMarginalGiven q σ))).untopD 0 +
          ∑ x, ((q.map Prod.fst) x).toReal * (mutualInformation
            (classicalQuantumState (conditionalSnd q x) (fun y => σ (x, y)))).untopD 0 := by
      rw [Fin.sum_univ_succ]
      simp only [coordinateMutualInformationTerms, Fin.cons_zero, Fin.cons_succ]
      change (mutualInformation
        (classicalQuantumState (q.map Prod.fst) (quantumMarginalGiven q σ))).untopD 0 +
        (∑ i : Fin n, ∑ x, ((q.map Prod.fst) x).toReal *
        coordinateMutualInformationTerms (fun j => X j.succ)
          (conditionalSnd q x) (fun y => σ (x, y)) i) = _
      rw [sum_comm]
      simp_rw [← mul_sum, htail]
    rw [← mutualInformation_classicalQuantumState_map_equiv e.symm p hρ]
    change mutualInformation (classicalQuantumState q σ) = _
    rw [mutualInformation_classicalQuantumState_prod q hσ, hsum, WithTop.coe_add, WithTop.coe_sum]
    rw [coe_untopD_mutualInformation (q.map Prod.fst) (ρ := quantumMarginalGiven q σ)
      (isDensityMatrix_quantumMarginalGiven q hσ)]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [WithTop.coe_mul, coe_untopD_mutualInformation (conditionalSnd q x) (fun y => hσ (x, y))]

end Cslib.Quantum
