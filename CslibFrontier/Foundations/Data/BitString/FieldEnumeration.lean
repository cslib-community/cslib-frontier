/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi

/-!
# Enumeration by padded binary fields

A word of `rows * width` bits describes `rows` choices, in most-significant-field-first order.
In each field, zero denotes no choice and `k + 1` denotes choice `k`. Values above the number
of choices are padding, and contribute zero to a sum. This convention gives each tuple of
choices exactly one word, including when there are no rows or no choices.

## Main definitions

* `Cslib.BitString.binaryField`: extract one fixed-width field by division and remainder.
* `Cslib.BitString.fieldChoice`: interpret zero and positive field values as optional choices.

## Main results

* `Cslib.BitString.fieldChoice_eq_some`: positive field values identify their choices exactly.
* `Cslib.BitString.sum_binaryFields`: a padded binary sum equals a sum over all choice tuples.

These enumeration lemmas are original infrastructure for binary sum-of-products circuits.
-/

public section

namespace Cslib.BitString

/-- Field `position` in a `rows * width`-bit unsigned number, counting fields from the most
significant end. Callers use positions below `rows`; the expression is total on all naturals. -/
@[expose] def binaryField (rows width assignment position : ℕ) : ℕ :=
  assignment / (2 ^ width) ^ (rows - 1 - position) % 2 ^ width

/-- Zero denotes no choice, values `1, …, modes` denote the respective choices, and padding
values also return `none`. A separate range guard excludes padding in `sum_binaryFields`. -/
@[expose] def fieldChoice (modes value : ℕ) : Option (Fin modes) :=
  if h : value < modes + 1 then finSuccEquiv modes ⟨value, h⟩ else none

private theorem fieldChoice_fin {modes : ℕ} (i : Fin (modes + 1)) :
    fieldChoice modes i = finSuccEquiv modes i := by
  simp [fieldChoice, i.isLt]

/-- A field denotes `some i` precisely when its numeric value is `i + 1`. -/
theorem fieldChoice_eq_some {modes value : ℕ} (i : Fin modes) :
    fieldChoice modes value = some i ↔ value = i.val + 1 := by
  by_cases h : value < modes + 1
  · simp only [fieldChoice, dite_eq_left h, finSuccEquiv_eq_some, Fin.ext_iff, Fin.val_succ]
  · have hn : value ≠ i.val + 1 := by omega
    simp [fieldChoice, h, hn]

private theorem binaryField_enum {rows width : ℕ} (f : Fin rows → Fin (2 ^ width))
    (j : Fin rows) :
    binaryField rows width (finFunctionFinEquiv f) j = (f j.rev).val := by
  simpa only [binaryField, Fin.val_rev, finFunctionFinEquiv_symm_apply_val,
    Nat.sub_sub, Nat.add_comm 1 j.val] using
    congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply f) j.rev)

private theorem sum_bounded_choices {M : Type*} [AddCommMonoid M]
    (modes rows base : ℕ) (hbase : modes + 1 ≤ base)
    (F : (Fin rows → Option (Fin modes)) → M) :
    (∑ f : Fin rows → Fin base,
      if ∀ j, (f j).val ≤ modes then F (fun j => fieldChoice modes (f j)) else 0) =
      ∑ φ : Fin rows → Option (Fin modes), F φ := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun f _ j => fieldChoice modes (f j)) (by simp) ?_ ?_ (by simp)
  · intro f hf g hg hfg
    have hf := (Finset.mem_filter.mp hf).2
    have hg := (Finset.mem_filter.mp hg).2
    funext j
    apply Fin.ext
    have heq := congrFun hfg j
    simp only [fieldChoice, dite_eq_left (Nat.lt_succ_of_le (hf j)),
      dite_eq_left (Nat.lt_succ_of_le (hg j))] at heq
    exact congrArg (fun k : Fin (modes + 1) => k.val) ((finSuccEquiv modes).injective heq)
  · intro φ _
    let f : Fin rows → Fin base := fun j =>
      Fin.castLE hbase ((finSuccEquiv modes).symm (φ j))
    refine ⟨f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      exact Nat.le_of_lt_succ ((finSuccEquiv modes).symm (φ j)).isLt
    · funext j
      change fieldChoice modes ((finSuccEquiv modes).symm (φ j)).val = φ j
      rw [fieldChoice_fin, Equiv.apply_symm_apply]

/-- Padded words enumerate optional choices once each. The only width requirement is that all
`modes + 1` legitimate values fit in one field; zero-width fields and empty tuples are allowed. -/
theorem sum_binaryFields {M : Type*} [AddCommMonoid M]
    (modes rows width : ℕ) (hwidth : modes + 1 ≤ 2 ^ width)
    (F : (Fin rows → Option (Fin modes)) → M) :
    (∑ a ∈ Finset.range (2 ^ (rows * width)),
      if ∀ j : Fin rows, binaryField rows width a j ≤ modes then
        F (fun j => fieldChoice modes (binaryField rows width a j)) else 0) =
      ∑ φ : Fin rows → Option (Fin modes), F φ := by
  classical
  rw [Nat.mul_comm rows width, pow_mul, Finset.sum_range]
  calc
    _ = ∑ f : Fin rows → Fin (2 ^ width),
        if ∀ j : Fin rows, (f j.rev).val ≤ modes then
          F (fun j => fieldChoice modes (f j.rev)) else 0 := by
      symm
      apply Fintype.sum_equiv finFunctionFinEquiv
      intro f
      simp only [binaryField_enum]
    _ = ∑ f : Fin rows → Fin (2 ^ width),
        if ∀ j : Fin rows, (f j).val ≤ modes then
          F (fun j => fieldChoice modes (f j)) else 0 := by
      apply Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl _))
      intro f
      rfl
    _ = _ := sum_bounded_choices modes rows (2 ^ width) hwidth F

end Cslib.BitString
