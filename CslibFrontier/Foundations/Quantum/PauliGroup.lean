/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.BooleanRing

/-!
# The Pauli group

The Pauli group on `n` qubits, up to the phase `i`, is the group of the operators
`(-1)^s X^a Z^b` for a sign bit `s` and bit strings `a, b : ι → Bool`
(`Cslib.Quantum.PauliGroup`). Since `Z^b X^{a'} = (-1)^{a'·b} X^{a'} Z^b`, the product is

`(s, a, b) · (s', a', b') = (s + s' + b·a', a + a', b + b')`,

a central extension of `(ℤ/2)^{2n}` by `ℤ/2` with the bilinear cocycle `b·a'` (a finite
Heisenberg group). The central element `-1 = (1, 0, 0)` (`Cslib.Quantum.PauliGroup.negOne`)
squares to `1`; the generators `X^a` (`Cslib.Quantum.PauliGroup.ofX`) and `Z^b`
(`Cslib.Quantum.PauliGroup.ofZ`) satisfy `Z^b X^a = (-1)^{a·b} X^a Z^b`
(`Cslib.Quantum.PauliGroup.ofZ_mul_ofX`).

## Main definitions

* `Cslib.Quantum.PauliGroup`: the Pauli group, with its `Group` and `Fintype` instances.
* `Cslib.Quantum.PauliGroup.negOne`, `Cslib.Quantum.PauliGroup.ofX`,
  `Cslib.Quantum.PauliGroup.ofZ`: the central element `-1` and the generators.

## Main results

* `Cslib.Quantum.PauliGroup.ofZ_mul_ofX`: the commutation relation.
* `Cslib.Quantum.PauliGroup.commute_negOne`: `-1` is central.
-/

@[expose] public section

open Matrix

namespace Cslib.Quantum

variable {ι : Type*} [Fintype ι]

/-- The **Pauli group** on `ι` qubits: `(s, a, b)` stands for `(-1)^s X^a Z^b`. -/
@[ext]
structure PauliGroup (ι : Type*) where
  /-- The sign bit. -/
  sign : Bool
  /-- The bit-flip part. -/
  x : ι → Bool
  /-- The phase-flip part. -/
  z : ι → Bool

namespace PauliGroup

/-- `(-1)^s X^a Z^b · (-1)^{s'} X^{a'} Z^{b'} = (-1)^{s + s' + b·a'} X^{a+a'} Z^{b+b'}`. -/
instance : Mul (PauliGroup ι) where
  mul p q := ⟨p.sign + q.sign + p.z ⬝ᵥ q.x, p.x + q.x, p.z + q.z⟩

instance : One (PauliGroup ι) := ⟨⟨false, 0, 0⟩⟩

instance : Inv (PauliGroup ι) where
  inv p := ⟨p.sign + p.z ⬝ᵥ p.x, p.x, p.z⟩

@[simp] theorem mul_sign (p q : PauliGroup ι) : (p * q).sign = p.sign + q.sign + p.z ⬝ᵥ q.x := rfl
@[simp] theorem mul_x (p q : PauliGroup ι) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_z (p q : PauliGroup ι) : (p * q).z = p.z + q.z := rfl
omit [Fintype ι] in
@[simp] theorem one_sign : (1 : PauliGroup ι).sign = false := rfl
omit [Fintype ι] in
@[simp] theorem one_x : (1 : PauliGroup ι).x = 0 := rfl
omit [Fintype ι] in
@[simp] theorem one_z : (1 : PauliGroup ι).z = 0 := rfl
@[simp] theorem inv_sign (p : PauliGroup ι) : p⁻¹.sign = p.sign + p.z ⬝ᵥ p.x := rfl
@[simp] theorem inv_x (p : PauliGroup ι) : p⁻¹.x = p.x := rfl
@[simp] theorem inv_z (p : PauliGroup ι) : p⁻¹.z = p.z := rfl

instance : Group (PauliGroup ι) where
  mul_assoc p q r := by
    ext
    · simp only [mul_sign, mul_z, mul_x, add_dotProduct, dotProduct_add]; abel
    · simp [add_assoc]
    · simp [add_assoc]
  one_mul p := by ext <;> simp; rfl
  mul_one p := by ext <;> simp; rfl
  inv_mul_cancel p := by
    ext
    · simp only [mul_sign, inv_sign, inv_z, one_sign]
      rw [add_assoc _ p.sign]; exact BooleanRing.add_self (p.sign + p.z ⬝ᵥ p.x)
    · exact BooleanRing.add_self _
    · exact BooleanRing.add_self _

/-- `PauliGroup ι ≃ Bool × (ι → Bool) × (ι → Bool)`. -/
def equivProd : PauliGroup ι ≃ Bool × (ι → Bool) × (ι → Bool) where
  toFun p := (p.sign, p.x, p.z)
  invFun | (s, a, b) => ⟨s, a, b⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (PauliGroup ι) := equivProd.decidableEq
instance [DecidableEq ι] : Fintype (PauliGroup ι) := Fintype.ofEquiv _ equivProd.symm

/-- The central element `-1`. -/
def negOne : PauliGroup ι := ⟨true, 0, 0⟩

theorem negOne_mul (p : PauliGroup ι) : negOne * p = ⟨!p.sign, p.x, p.z⟩ := by
  ext <;> simp [negOne]; cases p.sign <;> rfl

theorem mul_negOne (p : PauliGroup ι) : p * negOne = ⟨!p.sign, p.x, p.z⟩ := by
  ext <;> simp [negOne]; cases p.sign <;> rfl

/-- `(false, a, 0)`, the element `X^a`. -/
def ofX (a : ι → Bool) : PauliGroup ι := ⟨false, a, 0⟩

/-- `(false, 0, b)`, the element `Z^b`. -/
def ofZ (b : ι → Bool) : PauliGroup ι := ⟨false, 0, b⟩

theorem ofX_mul_ofX (a a' : ι → Bool) : ofX a * ofX a' = ofX (a + a') := by
  ext <;> simp [ofX] ; rfl

theorem ofZ_mul_ofZ (b b' : ι → Bool) : ofZ b * ofZ b' = ofZ (b + b') := by
  ext <;> simp [ofZ] ; rfl

theorem ofX_inv (a : ι → Bool) : (ofX a)⁻¹ = ofX a := by
  ext <;> simp [ofX]

theorem ofZ_inv (b : ι → Bool) : (ofZ b)⁻¹ = ofZ b := by
  ext <;> simp [ofZ]

omit [Fintype ι] in
theorem ofX_zero : ofX (0 : ι → Bool) = 1 := rfl

omit [Fintype ι] in
theorem ofZ_zero : ofZ (0 : ι → Bool) = 1 := rfl

theorem ofX_mul_ofZ (a b : ι → Bool) : ofX a * ofZ b = ⟨false, a, b⟩ := by
  ext <;> simp [ofX, ofZ] ; rfl

/-- `Z^b X^a = (-1)^{a·b} X^a Z^b` in the group. -/
theorem ofZ_mul_ofX (a b : ι → Bool) :
    ofZ b * ofX a = (if a ⬝ᵥ b then negOne else 1) * (ofX a * ofZ b) := by
  rw [ofX_mul_ofZ]
  cases h : a ⬝ᵥ b
  · ext <;> simp [ofX, ofZ, dotProduct_comm b a, h] ; rfl
  · rw [ite_eq_left rfl, negOne_mul]
    ext <;> simp [ofX, ofZ, dotProduct_comm b a, h] ; rfl

theorem negOne_mul_negOne : (negOne : PauliGroup ι) * negOne = 1 := by
  rw [negOne_mul]; ext <;> simp [negOne]

theorem negOne_inv : (negOne : PauliGroup ι)⁻¹ = negOne :=
  inv_eq_of_mul_eq_one_left negOne_mul_negOne

theorem commute_negOne (p : PauliGroup ι) : negOne * p = p * negOne := by
  rw [negOne_mul, mul_negOne]

/-- Every element is `(-1)^s X^a Z^b`. -/
theorem eq_sign_mul (p : PauliGroup ι) :
    p = (if p.sign then negOne else 1) * (ofX p.x * ofZ p.z) := by
  rw [ofX_mul_ofZ]
  cases h : p.sign
  · ext <;> simp [h]
  · rw [ite_eq_left rfl, negOne_mul]; ext <;> simp [h]

end PauliGroup

end Cslib.Quantum
