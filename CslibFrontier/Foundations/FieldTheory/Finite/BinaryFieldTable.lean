/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial
public import CslibFrontier.Foundations.FieldTheory.Finite.Coordinates
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Multiplication tables of explicit binary fields

The modulus is found by trial division. Remainders of powers of `X` give the multiplication
table of the power basis, shared by hardness encodings and the powering small-bias construction.

## Main definitions

* `Cslib.BinaryField.powerMulTable`: the power-basis multiplication table for a supplied modulus.
* `Cslib.BinaryField.fieldTable`: the multiplication table in degree `w`.

## Main results

* `Cslib.BinaryField.isMulTable_powerMulTable`: correctness for any power basis and monic modulus
  vanishing at its generator.
* `Cslib.BinaryField.isMulTable_fieldTable`: correctness of the table for every nonzero degree.
-/

@[expose] public section

namespace Cslib.BinaryField

open Finset Polynomial BitString

/-- The multiplication table of the power basis modulo the binary polynomial with coefficient
list `g`: entry `(u, v)` lists the coefficients of the remainder of `X ^ (u + v)`. -/
def powerMulTable (g : List Bool) : List (List (List Bool)) :=
  (List.range (g.length - 1)).map fun u => (List.range (g.length - 1)).map fun v =>
    (powerTable g).getD (u + v) []

/-- Remainders of powers give a multiplication table for any power basis whose generator
is a root of the supplied monic binary polynomial. -/
theorem isMulTable_powerMulTable {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {l : List Bool} {q : ℕ} (hlen : l.length = q) (α : F)
    (hα : (polyOfBits (l ++ [true])).aeval α = 0)
    (b : Module.Basis (Fin q) (ZMod 2) F) (hb : ∀ i : Fin q, b i = α ^ i.1) :
    IsMulTable b (powerMulTable (l ++ [true])) := by
  have hglen : (l ++ [true]).length - 1 = q := by simp [hlen]
  refine ⟨by simp [powerMulTable, hlen], fun u v => ?_⟩
  have hentry : tableEntry (powerMulTable (l ++ [true])) u v =
      (powerTable (l ++ [true])).getD (u + v) [] := by
    simp only [tableEntry, powerMulTable, hglen]
    rw [List.getD_map_range _ [] u.2, List.getD_map_range _ [] v.2]
  have huv : (u : ℕ) + v < 2 * l.length := by omega
  rw [hb u, hb v, ← pow_add, pow_eq_sum_powerTable l hα huv,
    fieldOfBits, ofBits, hentry, hlen, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [hb i]

/-- The coefficient list of the modulus of the explicit binary field of degree `w`. -/
def modulusBits (w : ℕ) : List Bool := (leastIrreducibleCode (2 ^ (w + 1)) w).bits

/-- The multiplication table of the explicit binary field of degree `w`. -/
def fieldTable (w : ℕ) : List (List (List Bool)) := powerMulTable (modulusBits w)

/-- The coefficient list of the modulus is the coefficient list of `leastIrreducible w`. -/
theorem polyOfBits_modulusBits {w : ℕ} (hw : w ≠ 0) :
    polyOfBits (modulusBits w) = leastIrreducible w := by
  rw [modulusBits, polyOfBits_bits, polyOfCode_leastIrreducibleCode hw le_rfl]

/-- The coefficient list of the modulus has length `w + 1` and ends with a one. -/
private theorem exists_modulusBits_eq {w : ℕ} (hw : w ≠ 0) :
    ∃ l : List Bool, modulusBits w = l ++ [true] ∧ l.length = w := by
  have hne : leastIrreducibleCode (2 ^ (w + 1)) w ≠ 0 := by
    intro h
    have := polyOfCode_leastIrreducibleCode hw (le_refl (2 ^ (w + 1)))
    rw [h, polyOfCode_zero] at this
    exact (irreducible_leastIrreducible w).ne_zero this.symm
  obtain ⟨l, hl⟩ := exists_bits_eq_append_true hne
  refine ⟨l, hl, ?_⟩
  have := natDegree_polyOfBits_append_true l
  rw [← hl, ← modulusBits, polyOfBits_modulusBits hw, natDegree_leastIrreducible hw] at this
  exact this.symm

/-- The basis of the explicit binary field used by the program. -/
local notation "𝔅" => BinaryField.basis

/-- **The table multiplies**: `fieldTable w` is a multiplication table of the power basis of the
explicit binary field of degree `w`. -/
theorem isMulTable_fieldTable {w : ℕ} (hw : w ≠ 0) : IsMulTable (𝔅 hw) (fieldTable w) := by
  obtain ⟨l, hl, hlen⟩ := exists_modulusBits_eq hw
  subst hlen
  have hα : aeval (AdjoinRoot.root (leastIrreducible l.length))
      (polyOfBits (l ++ [true])) = 0 := by
    rw [← hl, polyOfBits_modulusBits hw, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [fieldTable, hl]
  exact isMulTable_powerMulTable rfl _ hα (𝔅 hw) (BinaryField.basis_apply hw)

variable {w : ℕ}

/-- The element with given coordinates in the power basis is the element with these bits. -/
theorem fieldOfBits_basis (hw : w ≠ 0) (a : List Bool) :
    fieldOfBits (BinaryField.basis hw) a =
      (BinaryField.equivBits hw).symm fun j => a.getD j false := by
  rw [fieldOfBits, ofBits, BinaryField.equivBits_symm_apply]

/-- The bits of the element with given coordinates. -/
theorem equivBits_fieldOfBits (hw : w ≠ 0) (a : List Bool) (j : Fin w) :
    BinaryField.equivBits hw (fieldOfBits (BinaryField.basis hw) a) j = a.getD j false := by
  rw [BinaryField.equivBits_apply, repr_fieldOfBits, RingEquiv.apply_symm_apply]

/-- The coordinates `[true]` are those of `1`. -/
theorem fieldOfBits_one (hw : w ≠ 0) : fieldOfBits (BinaryField.basis hw) [true] = 1 := by
  rw [fieldOfBits, ofBits, Fintype.sum_eq_single ⟨0, Nat.pos_of_ne_zero hw⟩]
  · simp [BinaryField.basis_apply, bitEquiv_symm_true]
  · intro u hu
    have : (u : ℕ) ≠ 0 := fun h => hu (Fin.ext h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    simp [hk, bitEquiv_symm_false]

end Cslib.BinaryField
