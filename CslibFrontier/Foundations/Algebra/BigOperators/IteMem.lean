/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-!
# A sum of one constant on a set and another outside

`Fintype.sum_ite_mem_const`: over a finite type, the sum of `y` on a set `A` and of `z` outside
is `|A| * y + (card - |A|) * z`.
-/

public section

open Finset

/-- The sum over a finite type of one constant on a set and another outside it. -/
theorem Fintype.sum_ite_mem_const {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (A : Finset ι) (y z : R) :
    ∑ a : ι, (if a ∈ A then y else z) = A.card * y + ((Fintype.card ι : R) - A.card) * z := by
  have h (a : ι) : (if a ∈ A then y else z) = z + if a ∈ A then y - z else 0 := by
    split_ifs <;> simp
  simp only [h, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_mem]
  rw [mul_sub, sub_mul]
  abel
