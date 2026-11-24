/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.List.OfFn

/-!
# Bit strings as `BitVec` words

Both `Cslib.BitString w` (`Fin w → Bool`, numbered via `Cslib.BitString.equivFin w`) and Lean's
`BitVec w` index bits from the least significant position `0`. The computable equivalence
`Cslib.BitString.equivBitVec` identifies the two representations (`getLsbD_equivBitVec`,
`getElem_equivBitVec`, `equivBitVec_symm_apply`, `equivBitVec_getLsbD`), preserves unsigned natural
values (`toNat_equivBitVec_eq_equivFin`), and relates the `BooleanRing` zero and complement on
`BitString w` to `0#w` and bitwise complement `~~~` (`equivBitVec_zero`, `equivBitVec_symm_zero`,
`equivBitVec_compl`).

## Main definitions

* `Cslib.BitString.equivBitVec`: computable equivalence `BitString w ≃ BitVec w` preserving
  little-endian bit coordinates.

## Main results

* `Cslib.BitString.toNat_equivBitVec_eq_equivFin`: `(equivBitVec x).toNat` agrees with the unsigned
  value `(equivFin w x : ℕ)`.
-/

public section

namespace Cslib.BitString

variable {w : ℕ}

/-- Computable equivalence `BitString w ≃ BitVec w`, reading bit `i` of `x : BitString w` as
least-significant bit `i` of `BitVec w`. -/
@[expose] def equivBitVec : BitString w ≃ BitVec w where
  toFun bits := (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)
  invFun v i := v.getLsbD i.val
  left_inv bits := funext fun i => by
    dsimp only
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
    simp
  right_inv v := BitVec.eq_of_getLsbD_eq fun i hi => by
    dsimp only
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
    simp [hi]

/-- Bit `i` (least significant first) of `equivBitVec x` is `x i`. -/
theorem getLsbD_equivBitVec (x : BitString w) (i : Fin w) :
    (equivBitVec x).getLsbD i.val = x i :=
  congrFun (equivBitVec.symm_apply_apply x) i

/-- Indexing `equivBitVec x` at `i < w` returns `x ⟨i, hi⟩`. -/
@[simp] theorem getElem_equivBitVec (x : BitString w) (i : ℕ) (hi : i < w) :
    (equivBitVec x)[i] = x ⟨i, hi⟩ :=
  getLsbD_equivBitVec x ⟨i, hi⟩

/-- Bit `i` of `equivBitVec.symm v` is `v[i.val]`. -/
@[simp] theorem equivBitVec_symm_apply (v : BitVec w) (i : Fin w) :
    equivBitVec.symm v i = v[i.val] :=
  rfl

/-- Rebuilding a `BitVec w` from the bits `v.getLsbD i.val` via `equivBitVec` recovers `v`. -/
theorem equivBitVec_getLsbD (v : BitVec w) :
    equivBitVec (fun i : Fin w => v.getLsbD i.val) = v :=
  equivBitVec.apply_symm_apply v

/-- `equivBitVec` and `equivFin` assign the same unsigned natural value to every `w`-bit string. -/
theorem toNat_equivBitVec_eq_equivFin {w : ℕ} (x : BitString w) :
    (equivBitVec x).toNat = (equivFin w x : ℕ) := by
  induction w with
  | zero =>
    have h := (equivFin 0 x).isLt
    have hx := (equivBitVec x).isLt
    omega
  | succ w ih =>
    have heq : x = Fin.cons (x 0) (fun i => x i.succ) := by
      funext i
      induction i using Fin.cases <;> rfl
    rw [heq, val_equivFin_cons]
    have hw : equivBitVec (Fin.cons (x 0) (fun i => x i.succ)) =
        (equivBitVec fun i => x i.succ).concat (x 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_equivBitVec _ ⟨i, hi⟩, BitVec.getLsbD_concat]
      cases i with
      | zero => simp
      | succ i =>
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
          Nat.add_sub_cancel]
        exact (getLsbD_equivBitVec (fun i => x i.succ) ⟨i, by omega⟩).symm
    rw [hw, BitVec.toNat_concat, ih]
    omega

/-- `equivBitVec` maps the zero bit string (all `false`) to `0#w`. -/
@[simp] theorem equivBitVec_zero : equivBitVec (0 : BitString w) = 0#w :=
  BitVec.eq_of_getElem_eq fun _ _ => by simp [Bool.zero_eq_false]

/-- `equivBitVec.symm` maps `0#w` to the zero bit string. -/
@[simp] theorem equivBitVec_symm_zero : equivBitVec.symm 0#w = 0 :=
  equivBitVec.symm_apply_eq.mpr equivBitVec_zero.symm

/-- `equivBitVec` maps Boolean complement `xᶜ` to `BitVec` bitwise complement `~~~`. -/
@[simp] theorem equivBitVec_compl (x : BitString w) :
    equivBitVec xᶜ = ~~~equivBitVec x :=
  BitVec.eq_of_getElem_eq fun i hi => by
    simp only [getElem_equivBitVec, BitVec.getElem_not, Pi.compl_apply]
    cases x ⟨i, hi⟩ <;> rfl

end Cslib.BitString
