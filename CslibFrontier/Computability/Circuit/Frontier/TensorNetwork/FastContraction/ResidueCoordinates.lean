/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse

import Mathlib.Data.List.GetD

/-! # Connecting the native residue bit to Newton's lifted starting coordinates -/

public section
namespace Cslib.Circuits.Frontier.FastContraction.ResidueInverse

open GaloisRingArith

/-- The residue word has exactly one bit per coefficient, with zero padding for short lists. -/
@[expose] def lowWord (m : ℕ) (x : List ℕ) : List Bool :=
  List.ofFn fun i : Fin (modulus m).length => (x.getD i.val 0).testBit 0

@[simp] theorem length_lowWord (m : ℕ) (x : List ℕ) :
    (lowWord m x).length = (modulus m).length := by simp [lowWord]

/-- The actual input request emitted by the residue game is a low bit of the full input. -/
theorem getD_lowWord (m : ℕ) (x : List ℕ) (i : Fin (modulus m).length) :
    (lowWord m x).getD i.val false = (x.getD i.val 0).testBit 0 := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [lowWord]

private theorem val_lowWord (m : ℕ) (x : List ℕ) :
    val 1 (modulus m) ((lowWord m x).map Bool.toNat) =
      val 1 (modulus m) (residueCoeffs x) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < (modulus m).length := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
    residueCoeffs, getD_map_of_map_zero (f := (· % 2)) rfl]
  simp only [lowWord, List.getElem_ofFn, Nat.toNat_testBit, pow_zero, Nat.div_one]

private theorem seed_getD_lt (fl x : List ℕ) (i : ℕ) : (residueSeed fl x).getD i 0 < 2 := by
  by_cases h : i < (residueSeed fl x).length
  · rw [List.getD_eq_getElem _ _ h]
    have hmem := List.getElem_mem (l := residueSeed fl x) h
    change _ ∈ newton 1 fl (residueCoeffs x) (seed 1 fl (residueCoeffs x)) at hmem
    exact lt_of_mem_mul hmem
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    decide

/-- The native bit test supplies all digits of the lifted Newton seed. Digits above the
residue precision are zero, independently of the full target precision. -/
theorem seed_bit (m : ℕ) (x : List ℕ) (i : Fin (modulus m).length) (j : ℕ)
    (hx : IsUnit (val 1 (modulus m) x)) :
    ((residueSeed (modulus m) x).getD i.val 0).testBit j =
      (decide (j = 0) && run ⟨m, i.val, lowWord m x⟩) := by
  by_cases hj : j = 0
  · subst j
    simp only [decide_true, Bool.true_and]
    have hr := val_residueCoeffs (modulus m) x
    have hw := val_lowWord m x
    have hir := irreducible_modulus m
    have hs : IsUnit (val 1 (modulus m) (residueCoeffs x)) := by rw [hr]; exact hx
    have hg : IsUnit (val 1 (modulus m) ((lowWord m x).map Bool.toNat)) := by
      rw [hw]; exact hs
    have hinv : val 1 (modulus m) (residueSeed (modulus m) x) =
        val 1 (modulus m) (GaloisRingArith.inv 1 (modulus m) ((lowWord m x).map Bool.toNat)) := by
      rw [residueSeed, val_inv_of_isUnit hir hs, val_inv_of_isUnit hir hg, hw]
    have he := mod_eq_of_val_eq (p := 1) (fl := modulus m)
      (c := residueSeed (modulus m) x) (d := GaloisRingArith.inv 1 (modulus m)
        ((lowWord m x).map Bool.toNat)) hinv i.isLt
    simpa [run, Nat.testBit_zero] using congrArg (fun n : ℕ => decide (n = 1)) he
  · simp only [hj, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (seed_getD_lt _ _ _)
      (Nat.le_self_pow (by omega) 2))

end Cslib.Circuits.Frontier.FastContraction.ResidueInverse
