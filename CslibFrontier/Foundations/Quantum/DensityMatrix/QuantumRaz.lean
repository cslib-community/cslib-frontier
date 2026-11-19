/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumMarginal
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumConditioning
public import CslibFrontier.Probability.Product
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDataProcessing
import CslibFrontier.Foundations.Algebra.Order.WithTop

/-!
# Quantum Raz's lemma

A classical–quantum state on a tuple of classical labels and a quantum register has
the sum of its coordinate mutual informations bounded by its relative entropy to
any independent product of classical reference laws and a constant quantum reference.

We split the first label off from the tail. Its conditional block retains the tail
register, allowing the product-reference identity to separate the tail divergence.
Discarding the tail from the first-label information gives the term needed for the
induction. This proves [Bavarian, Vidick and Yuen, Lemma 5.10][BavarianVidickYuen2022]
(arXiv:1509.07466v2, printed p. 21), with natural logarithms.

## Main results

* `sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy`: Quantum Raz's lemma
  for finite tuples and extended divergence.
* `sum_weighted_coordinate_mutualInformation_le_relativeEntropy`: the coordinate bound averaged
  over transcripts, with a different product reference at each transcript.
-/

public section

namespace Cslib.Quantum

open Matrix Finset InformationTheory
open scoped ComplexOrder
open Cslib.Probability.PMF (bind_map_prodMk_apply conditionalSnd
  marginal_mul_conditionalSnd map_equiv_apply pi pi_apply)

variable {ι X Y Z : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem extended_klDiv_nonneg {T : Type*} [MeasurableSpace T] (p q : PMF T) :
    (0 : WithTop ℝ) ≤ (if klDiv p.toMeasure q.toMeasure = ⊤ then ⊤
      else ((klDiv p.toMeasure q.toMeasure).toReal : WithTop ℝ)) := by
  split
  · exact le_top
  · exact_mod_cast ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] in
private theorem classicalQuantumState_map_fst_quantumMarginalGiven
    (p : PMF (X × Y)) (ρ : X × Y → Matrix ι ι ℂ) :
    classicalQuantumState (p.map Prod.fst) (quantumMarginalGiven p ρ) =
      classicalQuantumMarginal p ρ Prod.fst := by
  simp only [classicalQuantumState, classicalQuantumMarginal]
  congr 1
  funext x
  rw [smul_quantumMarginalGiven, sum_filter, Fintype.sum_prod_type]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, ite_true]

omit [Fintype ι] [DecidableEq ι] in
private theorem trace_conditional_tail
    (p : PMF (X × Y)) (ρ : X × Y → Matrix ι ι ℂ) :
    partialTraceRight (classicalQuantumState (p.map Prod.fst)
      (fun x => classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y)))) =
      classicalQuantumMarginal p ρ Prod.snd := by
  rw [partialTraceRight_classicalQuantumState]
  ext ⟨i, y⟩ ⟨j, y'⟩
  simp only [Matrix.sum_apply, classicalQuantumState, classicalQuantumMarginal,
    Matrix.smul_apply, blockDiagonal_apply]
  by_cases hy : y = y'
  · subst y'
    simp only [↓reduceIte]
    simp_rw [smul_smul, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
    rw [sum_filter, Fintype.sum_prod_type]
    simp
  · simp [hy]

private theorem head_information_add_tail_divergence_le
    (p : PMF (X × Y)) {ρ : X × Y → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z))
    (q : PMF X) (r : PMF Y) {σ : Matrix ι ι ℂ} (hσ : IsDensityMatrix σ) :
    mutualInformation (classicalQuantumMarginal p ρ Prod.fst) +
      relativeEntropy (classicalQuantumMarginal p ρ Prod.snd)
        (classicalQuantumState r (fun _ => σ)) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (q.bind fun x => r.map (x, ·)) (fun _ => σ)) := by
  let A (x : X) := classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y))
  let B := classicalQuantumState r (fun _ => σ)
  let μ := p.map Prod.fst
  have hA (x : X) : IsDensityMatrix (A x) :=
    isDensityMatrix_classicalQuantumState _ (fun y => hρ (x, y))
  have hhead : mutualInformation (classicalQuantumMarginal p ρ Prod.fst) ≤
      mutualInformation (classicalQuantumState μ A) := by
    rw [← classicalQuantumState_map_fst_quantumMarginalGiven]
    exact mutualInformation_classicalQuantumState_partialTraceRight_le μ hA
  have htail : partialTraceRight (classicalQuantumState μ A) =
      classicalQuantumMarginal p ρ Prod.snd := trace_conditional_tail p ρ
  let : MeasurableSpace X := ⊤
  let : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  rw [show (fun _ : X × Y => σ) = (fun _ : X => σ) ∘ Prod.fst from rfl,
    relativeEntropy_classicalQuantumState_prod p hρ q (fun _ => r) (fun _ => hσ)]
  change _ ≤ _ + ∑ x, ((μ x).toReal : WithTop ℝ) * relativeEntropy (A x) B
  rw [sum_weighted_relativeEntropy_eq_mutualInformation_add μ hA, htail]
  exact (add_le_add_left hhead _).trans (le_add_of_nonneg_left (extended_klDiv_nonneg μ q))

omit [Fintype ι] [DecidableEq ι] [Fintype X] in
private theorem reindex_classicalQuantumState {Z : Type*} [DecidableEq Z] (e : X ≃ Z)
    (p : PMF X) (ρ : X → Matrix ι ι ℂ) :
    reindex (Equiv.prodCongr (Equiv.refl ι) e) (Equiv.prodCongr (Equiv.refl ι) e)
      (classicalQuantumState p ρ) = classicalQuantumState (p.map e) (ρ ∘ e.symm) := by
  ext ⟨i, z⟩ ⟨j, z'⟩
  simp only [reindex_apply, submatrix_apply, classicalQuantumState, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    blockDiagonal_apply, Function.comp_apply,
    map_equiv_apply, e.symm.injective.eq_iff]

universe u

/-- **Quantum Raz's lemma**. For any joint law on a finite tuple of possibly different
classical alphabets and any conditional density matrices, the sum of the coordinate
mutual informations is at most the divergence to a product of classical laws and
a common quantum reference. The inequality includes singular states and empty tuples. -/
theorem sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy {n : ℕ}
    (W : Fin n → Type u) [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    (p : PMF (∀ i, W i)) {ρ : (∀ i, W i) → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z))
    (q : ∀ i, PMF (W i)) {σ : Matrix ι ι ℂ} (hσ : IsDensityMatrix σ) :
    (∑ i, mutualInformation (classicalQuantumMarginal p ρ (fun z => z i))) ≤
      relativeEntropy (classicalQuantumState p ρ) (classicalQuantumState (pi q) (fun _ => σ)) := by
  induction n with
  | zero =>
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using
      relativeEntropy_nonneg (isDensityMatrix_classicalQuantumState p hρ)
        (isDensityMatrix_classicalQuantumState (pi q) (fun _ => hσ))
  | succ n ih =>
    let T (i : Fin n) := W i.succ
    let e := Fin.consEquiv W
    let p' := p.map e.symm
    let ρ' := ρ ∘ e
    have hρ' (z : W 0 × (∀ i : Fin n, T i)) : IsDensityMatrix (ρ' z) := hρ (e z)
    let r := pi (fun i : Fin n => q i.succ)
    let q' := (q 0).bind fun x => r.map (x, ·)
    have hq' : (pi q).map e.symm = q' := by
      ext ⟨x, y⟩
      change (((pi q).map e.symm) (x, y)) = ((q 0).bind fun x => r.map (x, ·)) (x, y)
      rw [map_equiv_apply, bind_map_prodMk_apply, pi_apply, Fin.prod_univ_succ]
      simp only [r, pi_apply, e, e.symm_symm, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    let pTail := p'.map Prod.snd
    let ρTail := quantumMarginalGivenMap p' ρ' Prod.snd
    have hρTail (y : ∀ i : Fin n, T i) : IsDensityMatrix (ρTail y) :=
      isDensityMatrix_quantumMarginalGivenMap p' hρ' Prod.snd y
    have htail : classicalQuantumState pTail ρTail = classicalQuantumMarginal p' ρ' Prod.snd :=
      (classicalQuantumMarginal_eq_state p' ρ' Prod.snd).symm
    have hm (i : Fin (n + 1)) : classicalQuantumMarginal p ρ (fun z => z i) =
        classicalQuantumMarginal p' ρ' (fun z => e z i) :=
      (classicalQuantumMarginal_map_equiv e.symm p ρ (fun z => z i)).symm
    have hhead : classicalQuantumMarginal p ρ (fun z => z 0) =
        classicalQuantumMarginal p' ρ' Prod.fst := by
      rw [hm]
      rfl
    have htailCoord (i : Fin n) : classicalQuantumMarginal p ρ (fun z => z i.succ) =
        classicalQuantumMarginal pTail ρTail (fun z => z i) := by
      rw [hm, classicalQuantumMarginal_comp_of_eq p' ρ' Prod.snd pTail ρTail _ htail]
      rfl
    have hD : relativeEntropy (classicalQuantumState p' ρ')
        (classicalQuantumState q' (fun _ => σ)) =
        relativeEntropy (classicalQuantumState p ρ)
          (classicalQuantumState (pi q) (fun _ => σ)) := by
      rw [← relativeEntropy_reindex (Equiv.prodCongr (Equiv.refl ι) e.symm)
        (isDensityMatrix_classicalQuantumState p hρ).posSemidef.isHermitian
        (isDensityMatrix_classicalQuantumState (pi q) (fun _ => hσ)).posSemidef,
        reindex_classicalQuantumState, reindex_classicalQuantumState, hq']
      rfl
    rw [Fin.sum_univ_succ, hhead, ← hD]
    simp_rw [htailCoord]
    have htailBound := ih T pTail hρTail (fun i => q i.succ)
    rw [htail] at htailBound
    exact (add_le_add_right htailBound _).trans
      (head_information_add_tail_divergence_le p' hρ' (q 0) r hσ)

/-- **Quantum Raz's bound averaged over transcripts.** Conditional on each transcript,
compare the tuple to an independent product law and the quantum state to a common
reference. The source expectation of the sum of coordinate informations is bounded
by the joint relative entropy, including at null transcripts and support mismatches. -/
theorem sum_weighted_coordinate_mutualInformation_le_relativeEntropy {n : ℕ}
    (W : Fin n → Type u) [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    (p : PMF (X × (∀ i, W i))) {ρ : X × (∀ i, W i) → Matrix ι ι ℂ}
    (hρ : ∀ z, IsDensityMatrix (ρ z)) (q : PMF X) (r : X → ∀ i, PMF (W i))
    {σ : X → Matrix ι ι ℂ} (hσ : ∀ x, IsDensityMatrix (σ x)) :
    (∑ x, (((p.map Prod.fst) x).toReal : WithTop ℝ) *
      ∑ i, mutualInformation
        (classicalQuantumMarginal (conditionalSnd p x) (fun y => ρ (x, y)) (fun y => y i))) ≤
      relativeEntropy (classicalQuantumState p ρ)
        (classicalQuantumState (q.bind fun x => (pi (r x)).map (x, ·)) (σ ∘ Prod.fst)) := by
  let : MeasurableSpace X := ⊤
  let : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  rw [relativeEntropy_classicalQuantumState_prod p hρ q (fun x => pi (r x)) hσ]
  refine le_trans (sum_le_sum fun x _ => ?_)
    (le_add_of_nonneg_left (extended_klDiv_nonneg (p.map Prod.fst) q))
  have h := sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy W (conditionalSnd p x)
    (fun y => hρ (x, y)) (r x) (hσ x)
  exact WithTop.mul_le_mul_of_nonneg_coe_left ENNReal.toReal_nonneg h

end Cslib.Quantum
