/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Covering.Basic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Spectrum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tensors up to equivalence

The classes of tensors over the parties `I` under equivalence,
`Antisymmetrization (PartyTensor K I) (· ≤ ·)`, form a commutative monoid (module
`CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Equivalent`). Covers of representatives
make it a monoid with a covering relation (`Cslib.PartyTensor.tensorCovering`). An upper
functional on tensors is the same as an upper functional on classes for this covering relation
(`Cslib.PartyTensor.UpperFunctional.isUpperFunctional_lift`,
`Cslib.PartyTensor.UpperFunctional.ofIsUpperFunctional`), so the abstract results of
`Cslib.Covering` apply to tensors.

## Main definitions

* `Cslib.PartyTensor.tensorCovering`: covers of classes of tensors.
* `Cslib.PartyTensor.UpperFunctional.ofIsUpperFunctional`: the upper functional given by an upper
  functional on classes.

## Main results

* `Cslib.PartyTensor.UpperFunctional.isUpperFunctional_lift`: an upper functional on tensors is
  one on classes.
* `Cslib.PartyTensor.tensorCovering_coveredBy`: covers of classes are covers of tensors.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Ov.Duality.Minimal`
-/

public section

namespace Cslib.PartyTensor

open Finset Covering

variable {K : Type} [CommSemiring K] {I : Type} [Fintype I] [DecidableEq I]

/-- A representative of a product of classes is equivalent to the product of representatives. -/
theorem antisymmRel_ofAntisymmetrization_mul
    (x y : Antisymmetrization (PartyTensor K I) (· ≤ ·)) :
    AntisymmRel (· ≤ ·) (ofAntisymmetrization (· ≤ ·) (x * y))
      (ofAntisymmetrization (· ≤ ·) x * ofAntisymmetrization (· ≤ ·) y) := by
  conv_lhs => rw [← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) x,
    ← toAntisymmetrization_ofAntisymmetrization (· ≤ ·) y, ← toAntisymmetrization_mul]
  exact antisymmRel_ofAntisymmetrization_toAntisymmetrization _

/-- The covering relation on classes of tensors: covers of representatives. -/
noncomputable def tensorCovering (K : Type) [CommSemiring K] (I : Type) [Fintype I]
    [DecidableEq I] : Covering (Antisymmetrization (PartyTensor K I) (· ≤ ·)) where
  CoveredBy t b :=
    (ofAntisymmetrization (· ≤ ·) t).CoveredBy fun k => ofAntisymmetrization (· ≤ ·) (b k)
  refl _ := .single le_rfl
  bind h h' := h.bind h'
  mul {κ _ t b} s h := by
    have h1 := (h.mul (CoveredBy.single (le_refl (ofAntisymmetrization (· ≤ ·) s)))).reindex
      (Equiv.prodPUnit κ).symm
    exact (CoveredBy.of_le (antisymmRel_ofAntisymmetrization_mul t s).le h1).mono
      fun k => (antisymmRel_ofAntisymmetrization_mul (b k) s).ge

/-- Covers of classes are covers of tensors. -/
theorem tensorCovering_coveredBy {κ : Type} [Fintype κ] {t : PartyTensor K I}
    {b : κ → PartyTensor K I} :
    (tensorCovering K I).CoveredBy (toAntisymmetrization (· ≤ ·) t)
      (fun k => toAntisymmetrization (· ≤ ·) (b k)) ↔ t.CoveredBy b := by
  have ht := antisymmRel_ofAntisymmetrization_toAntisymmetrization t
  have hb := fun k => antisymmRel_ofAntisymmetrization_toAntisymmetrization (b k)
  exact ⟨fun h => (CoveredBy.of_le ht.ge h).mono fun k => (hb k).le,
    fun h => (CoveredBy.of_le ht.le h).mono fun k => (hb k).ge⟩

namespace UpperFunctional

/-- An upper functional on tensors is an upper functional on classes. -/
theorem isUpperFunctional_lift (P : UpperFunctional K I) :
    IsUpperFunctional (tensorCovering K I) P.lift where
  nonneg m := by
    induction m using Antisymmetrization.ind
    exact P.nonneg _
  map_one := P.map_one
  map_mul_le s t := by
    induction s using Antisymmetrization.ind
    induction t using Antisymmetrization.ind
    exact P.map_mul_le _ _
  le_sum t b h := by
    simpa only [← lift_toAntisymmetrization, toAntisymmetrization_ofAntisymmetrization] using
      P.le_sum _ _ h

/-- The upper functional on tensors given by an upper functional on classes. -/
def ofIsUpperFunctional {q : Antisymmetrization (PartyTensor K I) (· ≤ ·) → ℝ}
    (h : IsUpperFunctional (tensorCovering K I) q) : UpperFunctional K I where
  toFun t := q (toAntisymmetrization (· ≤ ·) t)
  nonneg _ := h.nonneg _
  map_one := h.map_one
  map_mul_le s t := by rw [toAntisymmetrization_mul]; exact h.map_mul_le _ _
  le_sum s b hb := h.le_sum _ _ (tensorCovering_coveredBy.2 hb)

@[simp] theorem ofIsUpperFunctional_apply {q : Antisymmetrization (PartyTensor K I) (· ≤ ·) → ℝ}
    (h : IsUpperFunctional (tensorCovering K I) q) (t : PartyTensor K I) :
    ofIsUpperFunctional h t = q (toAntisymmetrization (· ≤ ·) t) := by rfl

/-- An inequality `P (t * x) ≤ c * P (t * y)` for all tensors `t` holds for all classes. -/
theorem respects_lift {P : UpperFunctional K I} {x y : PartyTensor K I} {c : ℝ}
    (h : ∀ t, P (t * x) ≤ c * P (t * y)) :
    Respects P.lift (toAntisymmetrization (· ≤ ·) x) (toAntisymmetrization (· ≤ ·) y) c := by
  intro m
  induction m using Antisymmetrization.ind
  exact h _

end UpperFunctional

end Cslib.PartyTensor
