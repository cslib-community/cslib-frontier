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

The classes of tensors over the parties `I` under equivalence are Mathlib's antisymmetrization
`Antisymmetrization (PartyTensor K I) (· ≤ ·)` of the restriction preorder, a partial order. The
product of tensors makes it a commutative monoid, and covers of representatives make it a monoid
with a covering relation (`Cslib.PartyTensor.tensorCovering`). An upper functional on tensors
is the same as an upper functional on classes for this covering relation
(`Cslib.PartyTensor.UpperFunctional.isUpperFunctional_lift`,
`Cslib.PartyTensor.UpperFunctional.ofIsUpperFunctional`), so the abstract results of
`Cslib.Covering` apply to tensors.

## Main definitions

* `Cslib.PartyTensor.tensorCovering`: covers of classes of tensors.
* `Cslib.PartyTensor.UpperFunctional.lift`: an upper functional as a function on classes.
* `Cslib.PartyTensor.UpperFunctional.ofIsUpperFunctional`: the upper functional given by an upper
  functional on classes.

## Main results

* `Cslib.PartyTensor.toAntisymmetrization_mul`, `Cslib.PartyTensor.toAntisymmetrization_pow`,
  `Cslib.PartyTensor.toAntisymmetrization_prod`: the class map is multiplicative.
* `Cslib.PartyTensor.tensorCovering_coveredBy`: covers of classes are covers of tensors.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Ov.Duality.Minimal`, `Nc.Price.Cover` (`cls_prod`, `cls_mon`)
-/

public section

namespace Cslib.PartyTensor

open Finset Covering

variable {K : Type} [CommSemiring K] {I : Type} [Fintype I] [DecidableEq I]

theorem antisymmRel_ofAntisymmetrization_toAntisymmetrization (t : PartyTensor K I) :
    AntisymmRel (· ≤ ·) (ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) t)) t :=
  (toAntisymmetrization_eq _ _ _).1 (toAntisymmetrization_ofAntisymmetrization _ _)

/-- The classes of tensors form a commutative monoid under the product. -/
instance : CommMonoid (Antisymmetrization (PartyTensor K I) (· ≤ ·)) where
  one := toAntisymmetrization (· ≤ ·) 1
  mul := Quotient.map₂ (· * ·) fun _ _ h _ _ h' => antisymmRel_mul h h'
  mul_assoc x y z := by
    induction x using Antisymmetrization.ind
    induction y using Antisymmetrization.ind
    induction z using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_assoc _ _ _)
  one_mul x := by
    induction x using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_one_mul _)
  mul_one x := by
    induction x using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_one _)
  mul_comm x y := by
    induction x using Antisymmetrization.ind
    induction y using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_comm _ _)

theorem toAntisymmetrization_one : toAntisymmetrization (· ≤ ·) (1 : PartyTensor K I) = 1 := rfl

theorem toAntisymmetrization_mul (s t : PartyTensor K I) :
    toAntisymmetrization (· ≤ ·) (s * t) =
      toAntisymmetrization (· ≤ ·) s * toAntisymmetrization (· ≤ ·) t :=
  rfl

theorem toAntisymmetrization_pow (t : PartyTensor K I) (n : ℕ) :
    toAntisymmetrization (· ≤ ·) (t ^ n) = toAntisymmetrization (· ≤ ·) t ^ n := by
  induction n with
  | zero => exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_pow_zero t)
  | succ n ih =>
    rw [pow_succ', ← ih, ← toAntisymmetrization_mul]
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_pow_succ t n)

theorem toAntisymmetrization_prod {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → PartyTensor K I) :
    toAntisymmetrization (· ≤ ·) (prod b) = ∏ k, toAntisymmetrization (· ≤ ·) (b k) := by
  have key : ∀ {n : ℕ} (b : Fin n → PartyTensor K I),
      toAntisymmetrization (· ≤ ·) (prod b) = ∏ k, toAntisymmetrization (· ≤ ·) (b k) := by
    intro n
    induction n with
    | zero => exact fun b => (toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_of_isEmpty b)
    | succ n ih =>
      intro b
      rw [Fin.prod_univ_succ, ← ih, ← toAntisymmetrization_mul]
      exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_fin_succ b)
  rw [(toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_reindex b (Fintype.equivFin κ).symm),
    key]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- The class of a product of powers of tensors. -/
theorem toAntisymmetrization_prod_pow {B : Type} [Fintype B] [DecidableEq B]
    (A : B → PartyTensor K I) (v : B → ℕ) :
    toAntisymmetrization (· ≤ ·) (prod fun β => A β ^ v β) =
      ∏ β, toAntisymmetrization (· ≤ ·) (A β) ^ v β := by
  rw [toAntisymmetrization_prod]
  exact Finset.prod_congr rfl fun β _ => toAntisymmetrization_pow _ _

/-- A representative of a product of classes is equivalent to the product of representatives. -/
private theorem antisymmRel_ofAntisymmetrization_mul
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

/-- An upper functional as a function on classes. -/
@[expose] def lift (P : UpperFunctional K I) : Antisymmetrization (PartyTensor K I) (· ≤ ·) → ℝ :=
  Quotient.lift P fun _ _ => P.congr

@[simp] theorem lift_toAntisymmetrization (P : UpperFunctional K I) (t : PartyTensor K I) :
    P.lift (toAntisymmetrization (· ≤ ·) t) = P t := rfl

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

/-- An inequality `P (t * x) ≤ c * P (t * y)` for all tensors `t` holds for all classes. -/
theorem respects_lift {P : UpperFunctional K I} {x y : PartyTensor K I} {c : ℝ}
    (h : ∀ t, P (t * x) ≤ c * P (t * y)) :
    Respects P.lift (toAntisymmetrization (· ≤ ·) x) (toAntisymmetrization (· ≤ ·) y) c := by
  intro m
  induction m using Antisymmetrization.ind
  exact h _

end UpperFunctional

end Cslib.PartyTensor
