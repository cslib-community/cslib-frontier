/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Shears of `R × R`

The shears `(x, y) ↦ (x + k * y, y)` and `(x, y) ↦ (x, y + k * x)` of `R × R` over a commutative
ring, as permutations. The inverse of a shear is the opposite shear, and iterating a shear `m`
times multiplies its parameter by `m`.

## Main definitions

* `Cslib.shearFst`, `Cslib.shearSnd`: the shears `(x, y) ↦ (x + k * y, y)` and
  `(x, y) ↦ (x, y + k * x)` of `R × R`.

## Main results

* `Cslib.shearFst_symm`, `Cslib.shearSnd_symm`: the inverse of a shear is the opposite shear.
* `Cslib.shearFst_pow`, `Cslib.shearSnd_pow`: iterating a shear `m` times multiplies its
  parameter by `m`.
-/

public section

namespace Cslib

variable {R : Type*} [CommRing R]

/-- The shear `(x, y) ↦ (x + k * y, y)` of `R × R`, as a permutation. -/
@[expose] def shearFst (k : R) : Equiv.Perm (R × R) where
  toFun v := (v.1 + k * v.2, v.2)
  invFun v := (v.1 - k * v.2, v.2)
  left_inv _ := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv _ := Prod.ext (sub_add_cancel _ _) rfl

/-- The shear `(x, y) ↦ (x, y + k * x)` of `R × R`, as a permutation. -/
@[expose] def shearSnd (k : R) : Equiv.Perm (R × R) where
  toFun v := (v.1, v.2 + k * v.1)
  invFun v := (v.1, v.2 - k * v.1)
  left_inv _ := Prod.ext rfl (add_sub_cancel_right _ _)
  right_inv _ := Prod.ext rfl (sub_add_cancel _ _)

@[simp]
theorem shearFst_apply (k : R) (v : R × R) : shearFst k v = (v.1 + k * v.2, v.2) :=
  rfl

@[simp]
theorem shearSnd_apply (k : R) (v : R × R) : shearSnd k v = (v.1, v.2 + k * v.1) :=
  rfl

/-- The inverse of a shear is the opposite shear. -/
theorem shearFst_symm (k : R) : (shearFst k).symm = shearFst (-k) :=
  Equiv.ext fun v => Prod.ext (show v.1 - k * v.2 = v.1 + -k * v.2 by ring) rfl

/-- The inverse of a shear is the opposite shear. -/
theorem shearSnd_symm (k : R) : (shearSnd k).symm = shearSnd (-k) :=
  Equiv.ext fun v => Prod.ext rfl (show v.2 - k * v.1 = v.2 + -k * v.1 by ring)

/-- Iterating a shear multiplies its parameter. -/
theorem shearFst_pow (k : R) (m : ℕ) : shearFst k ^ m = shearFst (m * k) := by
  induction m with
  | zero =>
    exact Equiv.ext fun v => by
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq, shearFst_apply, Nat.cast_zero, zero_mul,
        add_zero]
  | succ m ih =>
    rw [pow_succ', ih]
    exact Equiv.ext fun v => by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, shearFst_apply]
      exact Prod.ext (by push_cast; ring) rfl

/-- Iterating a shear multiplies its parameter. -/
theorem shearSnd_pow (k : R) (m : ℕ) : shearSnd k ^ m = shearSnd (m * k) := by
  induction m with
  | zero =>
    exact Equiv.ext fun v => by
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq, shearSnd_apply, Nat.cast_zero, zero_mul,
        add_zero]
  | succ m ih =>
    rw [pow_succ', ih]
    exact Equiv.ext fun v => by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, shearSnd_apply]
      exact Prod.ext rfl (by push_cast; ring)

end Cslib
