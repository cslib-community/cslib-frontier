/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Normalize

/-!
# Conditioning classical–quantum states

A positive block diagonal with known block traces can be written as a
classical–quantum state with the corresponding classical law. Normalizing
each supported block gives the conditional quantum densities. Grouping a
joint classical label then gives a conditional chain rule for relative
entropy, including null labels and infinite divergence.
-/

public section

namespace Cslib.Quantum

open Matrix InformationTheory
open scoped ComplexOrder
open Cslib.Probability.PMF (bind_map_prodMk_apply conditionalSnd marginal_mul_conditionalSnd)

variable {ι X Y : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private def groupFirstLabel : (ι × (X × Y)) ≃ ((ι × Y) × X) where
  toFun | (i, x, y) => ((i, y), x)
  invFun | ((i, y), x) => (i, (x, y))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype Y] in
private theorem reindex_classicalQuantumState_prod
    (p : PMF (X × Y)) (ρ : X × Y → Matrix ι ι ℂ) (q : PMF X) (r : X → PMF Y)
    (h : ∀ x y, p (x, y) = q x * r x y) :
    reindex groupFirstLabel groupFirstLabel (classicalQuantumState p ρ) =
      classicalQuantumState q (fun x => classicalQuantumState (r x) (fun y => ρ (x, y))) := by
  ext ⟨⟨i, y⟩, x⟩ ⟨⟨j, y'⟩, x'⟩
  simp only [reindex_apply, submatrix_apply, groupFirstLabel, Equiv.coe_fn_symm_mk,
    classicalQuantumState, blockDiagonal_apply]
  by_cases hx : x = x' <;> by_cases hy : y = y'
  · subst x' y'
    simp only [↓reduceIte, h, ENNReal.toReal_mul, Matrix.smul_apply, blockDiagonal_apply_eq]
    change (((q x).toReal * (r x y).toReal) • ρ (x, y)) i j =
      ((q x).toReal • ((r x y).toReal • ρ (x, y))) i j
    rw [smul_smul]
  · subst x'
    simp [hy, Matrix.smul_apply, blockDiagonal_apply]
  · simp [hx]
  · simp [hx]

/-- Relative entropy is unchanged when the joint classical label is grouped into a
transcript and a conditional label. -/
theorem relativeEntropy_classicalQuantumState_prod_eq_grouped
    (p : PMF (X × Y)) {ρ : X × Y → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z))
    (q : PMF X) (r : X → PMF Y) {σ : X → Matrix ι ι ℂ} (hσ : ∀ x, IsDensityMatrix (σ x)) :
    relativeEntropy (classicalQuantumState p ρ)
      (classicalQuantumState (q.bind fun x => (r x).map (x, ·)) (σ ∘ Prod.fst)) =
      relativeEntropy
        (classicalQuantumState (p.map Prod.fst)
          (fun x => classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y))))
        (classicalQuantumState q (fun x => classicalQuantumState (r x) (fun _ => σ x))) := by
  let qprod := q.bind fun x => (r x).map (x, ·)
  have hq (z : X × Y) : IsDensityMatrix ((σ ∘ Prod.fst) z) := hσ z.1
  change relativeEntropy (classicalQuantumState p ρ)
    (classicalQuantumState qprod (σ ∘ Prod.fst)) = _
  rw [← relativeEntropy_reindex (groupFirstLabel (ι := ι) (X := X) (Y := Y))
    (isDensityMatrix_classicalQuantumState p hρ).posSemidef.isHermitian
    (isDensityMatrix_classicalQuantumState qprod hq).posSemidef,
    reindex_classicalQuantumState_prod p ρ (p.map Prod.fst) (conditionalSnd p)
      (fun x y => (marginal_mul_conditionalSnd p x y).symm),
    reindex_classicalQuantumState_prod qprod (σ ∘ Prod.fst) q r
      (fun x y => bind_map_prodMk_apply q r (x, y))]
  rfl

/-- The classical–quantum chain rule grouped by a transcript. The reference samples its
transcript from `q`, its second classical label from `r`, and uses the density `σ`
specified by that transcript. -/
theorem relativeEntropy_classicalQuantumState_prod [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF (X × Y)) {ρ : X × Y → Matrix ι ι ℂ} (hρ : ∀ z, IsDensityMatrix (ρ z))
    (q : PMF X) (r : X → PMF Y) {σ : X → Matrix ι ι ℂ} (hσ : ∀ x, IsDensityMatrix (σ x)) :
    relativeEntropy (classicalQuantumState p ρ)
      (classicalQuantumState (q.bind fun x => (r x).map (x, ·)) (σ ∘ Prod.fst)) =
        (if klDiv (p.map Prod.fst).toMeasure q.toMeasure = ⊤ then ⊤
          else ((klDiv (p.map Prod.fst).toMeasure q.toMeasure).toReal : WithTop ℝ)) +
        ∑ x, (((p.map Prod.fst) x).toReal : WithTop ℝ) *
          relativeEntropy (classicalQuantumState (conditionalSnd p x) (fun y => ρ (x, y)))
            (classicalQuantumState (r x) (fun _ => σ x)) := by
  rw [relativeEntropy_classicalQuantumState_prod_eq_grouped p hρ q r hσ]
  exact relativeEntropy_classicalQuantumState _ _
    (fun x => isDensityMatrix_classicalQuantumState _ (fun y => hρ (x, y)))
    (fun x => isDensityMatrix_classicalQuantumState _ (fun _ => hσ x))

omit [DecidableEq ι] [Fintype X] in
/-- A positive block diagonal whose block traces are the probabilities of `p` is
the corresponding classical–quantum state. On supported labels its conditional
state is the normalized block. The choice at a null label has zero weight. -/
theorem exists_classicalQuantumState_eq_blockDiagonal
    (p : PMF X) (A : X → Matrix ι ι ℂ) (hA : ∀ x, (A x).PosSemidef)
    (htrace : ∀ x, (A x).trace.re = (p x).toReal)
    {σ : Matrix ι ι ℂ} (hσ : IsDensityMatrix σ) :
    ∃ ρ : X → Matrix ι ι ℂ, (∀ x, IsDensityMatrix (ρ x)) ∧
      (∀ x ∈ p.support, ρ x = normalizeDensity (A x)) ∧
      classicalQuantumState p ρ = blockDiagonal A := by
  classical
  let ρ (x : X) := if x ∈ p.support then normalizeDensity (A x) else σ
  refine ⟨ρ, ?_, fun x hx => ite_eq_left hx, ?_⟩
  · intro x
    by_cases hx : x ∈ p.support
    · rw [show ρ x = normalizeDensity (A x) from ite_eq_left hx]
      exact isDensityMatrix_normalizeDensity (hA x)
        (by rw [htrace x]; exact ENNReal.toReal_pos hx (p.apply_ne_top x))
    · simpa only [ρ, ite_eq_right hx] using hσ
  · unfold classicalQuantumState
    congr 1
    funext x
    rw [← htrace x]
    by_cases hx : x ∈ p.support
    · rw [show ρ x = normalizeDensity (A x) from ite_eq_left hx,
        trace_smul_normalizeDensity (hA x)]
    · have hzero : (A x).trace.re = 0 := by
        simp only [htrace x, (p.apply_eq_zero_iff x).mpr hx, ENNReal.toReal_zero]
      rw [hzero, zero_smul]
      have hw := trace_smul_normalizeDensity (hA x)
      rw [hzero, zero_smul] at hw
      exact hw

end Cslib.Quantum
