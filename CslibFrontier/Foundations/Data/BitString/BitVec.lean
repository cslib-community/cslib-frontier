/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Bit strings as `BitVec` words

Both `Cslib.BitString n` (`Fin n → Bool`, numbered via `Cslib.BitString.equivFin n`) and Lean's
`BitVec n` index bits from the least significant position `0`. The computable equivalence
`Cslib.BitString.equivBitVec` identifies the two representations while translating the
`BooleanRing` operations on `BitString n` (`+`, `*`, `0`, `1`, `⊔`, `xᶜ`) to the bitwise operations
on `BitVec n` (`^^^`, `&&&`, `0#n`, `BitVec.allOnes n`, `|||`, `~~~`), keeping them distinct from
`BitVec`'s modular integer addition `+`.

## Main definitions

* `Cslib.BitString.equivBitVec`: computable equivalence `BitString n ≃ BitVec n` preserving
  little-endian bit coordinates and unsigned values (`equivFin n`).

## Main results

* `Cslib.BitString.getLsbD_equivBitVec`, `Cslib.BitString.getElem_equivBitVec`,
  `Cslib.BitString.equivBitVec_symm_apply`: coordinate agreement at every bit position `i < n`.
* `Cslib.BitString.equivBitVec_zero`, `Cslib.BitString.equivBitVec_one`,
  `Cslib.BitString.equivBitVec_add`, `Cslib.BitString.equivBitVec_mul`,
  `Cslib.BitString.equivBitVec_sup`, `Cslib.BitString.equivBitVec_compl`: homomorphisms to
  `0#n`, `BitVec.allOnes n`, bitwise XOR (`^^^`), AND (`&&&`), OR (`|||`), and NOT (`~~~`).
-/

@[expose] public section

namespace Cslib.BitString

/-- Computable equivalence `BitString n ≃ BitVec n`, identifying bit `i` of `x : BitString n` with
least-significant bit `i` of `BitVec n` and `equivFin n x` with `BitVec.toFin`. -/
def equivBitVec (n : ℕ) : BitString n ≃ BitVec n where
  toFun x := BitVec.ofFin (equivFin n x)
  invFun v := (equivFin n).symm v.toFin
  left_inv x := (equivFin n).symm_apply_apply x
  right_inv v := BitVec.eq_of_toFin_eq ((equivFin n).apply_symm_apply v.toFin)

variable {n : ℕ}

@[simp]
theorem toFin_equivBitVec (x : BitString n) : (equivBitVec n x).toFin = equivFin n x := by
  rfl

@[simp]
theorem toNat_equivBitVec (x : BitString n) : (equivBitVec n x).toNat = (equivFin n x : ℕ) := by
  rfl

/-- Least-significant bit `i` of `equivBitVec n x` is `x i`. -/
theorem getLsbD_equivBitVec (x : BitString n) (i : Fin n) :
    (equivBitVec n x).getLsbD i = x i := by
  rw [equivBitVec, Equiv.coe_fn_mk, BitVec.getLsbD_ofFin, testBit_equivFin]

/-- Indexing `equivBitVec n x` at `i < n` returns `x ⟨i, hi⟩`. -/
@[simp]
theorem getElem_equivBitVec (x : BitString n) (i : ℕ) (hi : i < n) :
    (equivBitVec n x)[i] = x ⟨i, hi⟩ :=
  getLsbD_equivBitVec x ⟨i, hi⟩

/-- Bit `i` of `(equivBitVec n).symm v` is `v[i]`. -/
@[simp]
theorem equivBitVec_symm_apply (v : BitVec n) (i : Fin n) :
    (equivBitVec n).symm v i = v[i] := by
  rw [← getElem_equivBitVec ((equivBitVec n).symm v) i.1 i.2, (equivBitVec n).apply_symm_apply]
  rfl

@[simp]
theorem equivBitVec_zero : equivBitVec n 0 = 0#n :=
  BitVec.eq_of_getElem_eq fun i hi => by simp [getElem_equivBitVec, Bool.zero_eq_false]

@[simp]
theorem equivBitVec_symm_zero : (equivBitVec n).symm 0#n = 0 :=
  (equivBitVec n).symm_apply_eq.mpr equivBitVec_zero.symm

@[simp]
theorem equivBitVec_one : equivBitVec n 1 = BitVec.allOnes n :=
  BitVec.eq_of_getElem_eq fun i hi => by simp [getElem_equivBitVec, Bool.one_eq_true]

@[simp]
theorem equivBitVec_symm_allOnes : (equivBitVec n).symm (BitVec.allOnes n) = 1 :=
  (equivBitVec n).symm_apply_eq.mpr equivBitVec_one.symm

/-- `equivBitVec` maps `BitString` addition (coordinatewise XOR) to `BitVec` bitwise XOR `^^^`. -/
@[simp]
theorem equivBitVec_add (x y : BitString n) :
    equivBitVec n (x + y) = equivBitVec n x ^^^ equivBitVec n y :=
  BitVec.eq_of_getElem_eq fun i hi => by
    simp only [getElem_equivBitVec, BitVec.getElem_xor, Pi.add_apply, Bool.add_eq_xor]

@[simp]
theorem equivBitVec_symm_xor (u v : BitVec n) :
    (equivBitVec n).symm (u ^^^ v) = (equivBitVec n).symm u + (equivBitVec n).symm v :=
  (equivBitVec n).injective <| by simp

/-- `equivBitVec` maps `BitString` multiplication (coordinatewise AND) to `BitVec` bitwise AND
`&&&`. -/
@[simp]
theorem equivBitVec_mul (x y : BitString n) :
    equivBitVec n (x * y) = equivBitVec n x &&& equivBitVec n y :=
  BitVec.eq_of_getElem_eq fun i hi => by
    simp only [getElem_equivBitVec, BitVec.getElem_and, Pi.mul_apply, Bool.mul_eq_and]

@[simp]
theorem equivBitVec_symm_and (u v : BitVec n) :
    (equivBitVec n).symm (u &&& v) = (equivBitVec n).symm u * (equivBitVec n).symm v :=
  (equivBitVec n).injective <| by simp

/-- `equivBitVec` maps lattice join (coordinatewise OR) to `BitVec` bitwise OR `|||`. -/
@[simp]
theorem equivBitVec_sup (x y : BitString n) :
    equivBitVec n (x ⊔ y) = equivBitVec n x ||| equivBitVec n y :=
  BitVec.eq_of_getElem_eq fun i hi => by
    simp only [getElem_equivBitVec, BitVec.getElem_or, Pi.sup_apply, Bool.sup_eq_bor]

/-- `equivBitVec` maps Boolean complement `xᶜ` to `BitVec` bitwise complement `~~~`. -/
@[simp]
theorem equivBitVec_compl (x : BitString n) :
    equivBitVec n xᶜ = ~~~equivBitVec n x :=
  BitVec.eq_of_getElem_eq fun i hi => by
    simp only [getElem_equivBitVec, BitVec.getElem_not, Pi.compl_apply]
    cases x ⟨i, hi⟩ <;> rfl

end Cslib.BitString
