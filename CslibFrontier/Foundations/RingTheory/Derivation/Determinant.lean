/-
Copyright (c) 2026 Aviv Bar Natan and Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, `Mathlib/RingTheory/Derivation/Determinant`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# Derivations of determinants

A derivation applied to a determinant is the sum of the determinants obtained by replacing
each column in turn with its derivative (`Derivation.map_det`). The identity holds for an
arbitrary derivation of a commutative algebra and requires no invertibility hypothesis.
-/

public section

namespace Derivation

open Matrix Finset

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A] (δ : Derivation F A A)

private theorem map_prod_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → A) :
    δ (∏ i ∈ s, a i) = ∑ j ∈ s, (∏ i ∈ s.erase j, a i) * δ (a j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [prod_insert hk, leibniz, ih, sum_insert hk, erase_insert hk, smul_eq_mul, smul_eq_mul,
      mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hjk : k ≠ j := fun h => hk (h ▸ hj)
    rw [erase_insert_of_ne hjk, prod_insert (fun h => hk (mem_of_mem_erase h))]
    ring

/-- A derivation applied to a determinant is the sum over the columns of the determinant in
which that column is replaced by its derivative. -/
theorem map_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n A) :
    δ M.det = ∑ j, (M.updateCol j fun i => δ (M i j)).det := by
  simp only [det_apply', map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  have hsign : δ (((Equiv.Perm.sign σ : ℤ) : A) * ∏ i, M (σ i) i) =
      ((Equiv.Perm.sign σ : ℤ) : A) * δ (∏ i, M (σ i) i) := by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  rw [hsign, map_prod_erase, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ j), updateCol_self]
  have h : ∀ i ∈ univ.erase j, (M.updateCol j fun i => δ (M i j)) (σ i) i = M (σ i) i :=
    fun i hi => updateCol_ne (ne_of_mem_erase hi)
  rw [prod_congr rfl h]
  ring

end Derivation
