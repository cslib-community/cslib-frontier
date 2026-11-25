/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Polynomial/Roots.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Div

/-!
# Divisibility by a product of distinct linear factors

Over an integral domain, `∏ a ∈ s, (X - C a)` divides `p` exactly when `p` vanishes on `s`
(`Polynomial.prod_X_sub_C_dvd_iff_forall_eval_eq_zero`). Unlike Mathlib's
`Multiset.prod_X_sub_C_dvd_iff_le_roots`, this needs no hypothesis `p ≠ 0`, because the
points of a `Finset` are distinct.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The product of the linear factors `X - C a` over `a ∈ s` divides `p` exactly when `p`
vanishes at every point of `s`. -/
theorem prod_X_sub_C_dvd_iff_forall_eval_eq_zero (s : Finset R) (p : R[X]) :
    (∏ a ∈ s, (X - C a)) ∣ p ↔ ∀ a ∈ s, p.eval a = 0 := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty =>
    simp only [Finset.prod_empty, one_dvd, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.forall_mem_insert]
    refine ⟨fun hdvd => ⟨?_, ?_⟩, fun ⟨ha0, hs0⟩ => ?_⟩
    · exact dvd_iff_isRoot.mp (dvd_of_mul_right_dvd hdvd)
    · exact (ih p).mp (dvd_of_mul_left_dvd hdvd)
    · obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr ha0
      refine mul_dvd_mul_left (X - C a) ((ih q).mpr fun x hx => ?_)
      have hxa : x - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hx)
      have hev := hs0 x hx
      simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
      exact (mul_eq_zero.mp hev).resolve_left hxa

end Polynomial
