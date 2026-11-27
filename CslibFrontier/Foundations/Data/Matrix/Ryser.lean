/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Ryser's Boolean-sum formula for the permanent

Ryser's inclusion–exclusion identity expresses the permanent as a signed sum over Boolean
column selectors [Schauz, Theorem 1.2, p. 3][Schauz2006]. The sign is the product of `1` for each
selected column and `-1` for each unselected column. Each summand multiplies the selected row
sums. The proof works over every commutative ring, including characteristic two and the zero
ring; Schauz's section-wide convention is an integral domain of characteristic zero.

The proof expands the row product into a sum over all functions from rows to columns. Summing
the signs cancels every nonsurjective function. On a finite square matrix, the surviving
functions are exactly the permutations. The empty matrix has permanent `1` and contributes
one empty Boolean assignment.

## Main results

* `Matrix.permanent_eq_ryser_bool`: Ryser's formula as a sum over `ι → Bool`.

## References

* [U. Schauz, *Colorings and orientations of matrices and graphs*][Schauz2006], Theorem 1.2

The proof is adapted from the saved Complexitylib development at revision `5b8acca7`.
-/

public section

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Boolean-indicator form of Ryser's inclusion–exclusion formula for the permanent
[Schauz, Theorem 1.2, p. 3][Schauz2006], generalized to every commutative ring. -/
theorem permanent_eq_ryser_bool (A : Matrix n n R) :
    A.permanent =
      ∑ e : n → Bool,
        (∏ j : n, if e j then (1 : R) else -1) *
          ∏ i : n, ∑ j : n, if e j then A i j else 0 := by
  have hprod (e : n → Bool) :
      (∏ i : n, ∑ j : n, if e j then A i j else 0) =
        ∑ f : n → n, (if ∀ i, e (f i) = true then (1 : R) else 0) * ∏ i : n, A i (f i) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.prod_congr rfl fun i _ => boole_mul (e (f i) = true) (A i (f i)),
      Finset.prod_mul_distrib, Finset.prod_boole]
    simp only [Finset.mem_univ, forall_true_left]
  have hfactor (f : n → n) (e : n → Bool) :
      (∏ j : n, if e j then (1 : R) else -1) *
          (if ∀ i, e (f i) = true then (1 : R) else 0) =
        ∏ j : n, if e j then (1 : R) else if ∃ i, f i = j then 0 else -1 := by
    split_ifs with hf
    · rw [mul_one]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hne (h0 : e j = false) : ¬ ∃ i, f i = j := fun ⟨i, h⟩ => by simpa [h, h0] using hf i
      cases hej : e j <;> simp [hne, hej]
    · obtain ⟨i, hi⟩ := not_forall.1 hf
      rw [mul_zero, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ (f i)) (by simp [hi])
  have hsum_e (f : n → n) :
      (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) =
        if Function.Surjective f then (1 : R) else 0 := by
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun (j : n) (b : Bool) =>
      if b = true then (1 : R) else if ∃ i, f i = j then 0 else -1)]
    have h1 (j : n) : (1 : R) + (if ∃ i, f i = j then 0 else -1) =
        if ∃ i, f i = j then 1 else 0 := by split_ifs <;> simp
    simp_rw [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, h1,
      Finset.prod_boole, Finset.mem_univ, forall_true_left]
    rfl
  simp_rw [hprod, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hsum_e, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← permanent_transpose, permanent]
  exact Finset.sum_bij (fun (σ : Perm n) _ => (σ : n → n))
    (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.surjective⟩)
    (fun _ _ _ _ h => DFunLike.coe_injective h)
    (fun f hf => ⟨Equiv.ofBijective f
      (Finite.surjective_iff_bijective.mp (Finset.mem_filter.mp hf).2), Finset.mem_univ _, rfl⟩)
    fun _ _ => rfl

end Matrix
