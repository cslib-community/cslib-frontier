/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProductQuery
import CslibFrontier.Computability.Circuit.Boolean.Modular.Subtract
import CslibFrontier.Foundations.Data.BitString.Binary

/-! # Carry-lookahead queries for the Newton correction factor -/

public section
namespace Cslib.Circuits.Frontier.FastContraction.NewtonCorrection

open Boolean BitString Polynomial GaloisRingArith

/-- The carry-lookahead constant is three in the constant coefficient and one elsewhere. -/
@[expose] def offset (i : ℕ) : ℕ := if i = 0 then 3 else 1

/-- Add the offset to the bitwise complement of a queried coefficient. -/
@[expose] noncomputable def pair {p : ℕ} (i : ℕ) (a : (ZMod (2 ^ p))[X]) :
    BitString (p + p) :=
  Fin.append ((equivFin p).symm ⟨offset i % 2 ^ p, Nat.mod_lt _ (by positivity)⟩)
    (fun j => !(coeffWord a i j))

/-- The two physical root ports select a local constant or one complemented operand digit. -/
theorem component_pair {p : ℕ} (i : ℕ) (a : (ZMod (2 ^ p))[X]) (right : Bool) (j : Fin p) :
    CarrySaveQuery.component (pair i a) right j =
      if right then !(a.coeff i).val.testBit j.val else (offset i).testBit j.val := by
  cases right <;> simp only [CarrySaveQuery.component, pair, Bool.false_eq_true, ↓reduceIte,
    fstBits_append, sndBits_append, coeffWord, equivFin_symm_apply, Nat.testBit_mod_two_pow,
    j.isLt, decide_true, Bool.true_and]

private theorem coeff_two (m p : ℕ) (i : Fin (modulus m).length) :
    (representative m p 2).coeff i.val = if i.val = 0 then 2 else 0 := by
  have h : (2 : Ring p (modulus m)) = val p (modulus m) [2] := by simp
  rw [h, representative, coeff_modByMonicHom_val, ite_eq_left i.isLt]
  rcases i with ⟨_ | i, hi⟩ <;> simp [List.getD_eq_getElem?_getD]

/-- The ordinary binary sum really is a coordinate of the factor used by Newton iteration. -/
theorem bit_sum (m p : ℕ) (z : Ring p (modulus m)) (i : Fin (modulus m).length) (j : Fin p) :
    (carryLookaheadAdd p).eval interpretation (pair i.val (representative m p z)) j =
      ((representative m p (2 - z)).coeff i.val).val.testBit j.val := by
  let b := coeffWord (representative m p z) i.val
  let a := (equivFin p).symm ⟨offset i.val % 2 ^ p, Nat.mod_lt _ (by positivity)⟩
  let out := (carryLookaheadAdd p).eval interpretation (Fin.append a (fun t => !b t))
  have hb : (equivFin p b : ℕ) = ((representative m p z).coeff i.val).val := by
    simp [b, coeffWord]
  have ha : ((equivFin p a : ℕ) : ZMod (2 ^ p)) = offset i.val := by simp [a]
  have hneg : ((equivFin p (fun t => !b t) : ℕ) : ZMod (2 ^ p)) +
      ((equivFin p b : ℕ) : ZMod (2 ^ p)) + 1 = 0 := by
    have h := (equivFin p b).isLt
    have ht : 2 ^ p - 1 - (equivFin p b : ℕ) + (equivFin p b : ℕ) + 1 = 2 ^ p := by omega
    rw [Modular.val_not]
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using
      congrArg (fun n : ℕ => (n : ZMod (2 ^ p))) ht
  have hz : ((equivFin p out : ℕ) : ZMod (2 ^ p)) =
      (representative m p (2 - z)).coeff i.val := by
    rw [show representative m p (2 - z) = representative m p 2 - representative m p z from
      map_sub _ _ _, coeff_sub, coeff_two]
    dsimp only [out]
    rw [val_eval_carryLookaheadAdd, ZMod.natCast_mod, Nat.cast_add, ha]
    rw [hb, ZMod.natCast_zmod_val] at hneg
    by_cases hi : i.val = 0
    · rw [hi] at hneg ⊢
      simp [offset]
      linear_combination hneg
    · simp [offset, hi]
      linear_combination hneg
  have he := congrArg ZMod.val hz
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (equivFin p out).isLt] at he
  change out j = _
  rw [← he]
  exact (testBit_equivFin out j).symm

end Cslib.Circuits.Frontier.FastContraction.NewtonCorrection
