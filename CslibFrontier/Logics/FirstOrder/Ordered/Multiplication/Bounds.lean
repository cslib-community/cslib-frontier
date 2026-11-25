/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.Nat.Log
import Batteries.Data.Nat.Lemmas

/-!
# Packing bounds for native multiplication

For every universe of size at least 257, eight words hold the carries at block boundaries,
and sixteen words hold the carries of one block. The terminal column covers both input widths.
Every bound applies to arbitrary universe sizes, including sizes between powers of two.

## Main results

* `Cslib.Logic.FO.Ordered.Multiplication.exists_parameters`: uniform packing witnesses.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1).
  These bounds support the carry-table variant of the source's packed short sums.
-/

public section

namespace Cslib.Logic.FO.Ordered.Multiplication

private theorem sixteen_mul_le_pow {h : ℕ} (hh : 8 ≤ h) : 16 * h ≤ 2 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih => rw [Nat.pow_succ]; omega

private theorem sq_le_pow {d : ℕ} (hd : 4 ≤ d) : d * d ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    have h4d : 4 * d ≤ d * d := Nat.mul_le_mul_right d hd
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

/-- Powers of two give a block size and terminal column whose packed carries fit in a fixed
number of words. The first pair characterizes the actual highest bit of `n-1`. -/
theorem exists_parameters {n : ℕ} (hn : 257 ≤ n) :
    ∃ h e m : ℕ, 2 ^ h ≤ n - 1 ∧ n - 1 < 2 ^ (h + 1) ∧
      8 ≤ h ∧ 16 * h < n ∧ e ≤ m ∧ 2 ^ e ≤ h ∧
      h + 1 < 2 ^ (2 ^ e) ∧ 2 * (h + 1) ≤ 2 ^ m ∧
      2 ^ m + 2 ^ e ≤ 8 * h ∧ (2 ^ e + 1) * 2 ^ e ≤ 16 * h := by
  let h := (n - 1).log2
  have hn0 : n - 1 ≠ 0 := by omega
  have hh : 8 ≤ h := (Nat.le_log2 hn0).mpr (by omega)
  have hlo : 2 ^ h ≤ n - 1 := Nat.log2_self_le hn0
  have hhi : n - 1 < 2 ^ (h + 1) := (Nat.log2_lt hn0).mp (Nat.lt_succ_self h)
  have hspace : 16 * h < n := lt_of_le_of_lt (sixteen_mul_le_pow hh) (by omega)
  let d := h.log2 + 1
  have hd4 : 4 ≤ d := Nat.succ_le_succ ((Nat.le_log2 (by omega)).mpr (show 2 ^ 3 ≤ h by omega))
  have hpowlo : 2 ^ (d - 1) ≤ h := Nat.log2_self_le (by omega)
  have hpowhi : h < 2 ^ d := (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := Nat.pow_succ 2 h.log2
  have hd2 : d * d ≤ 2 * h := by have := sq_le_pow hd4; omega
  let e := d.log2 + 1
  have hds : d < 2 ^ e := (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  have hsd : 2 ^ e ≤ 2 * d := by
    have := Nat.log2_self_le (by omega : d ≠ 0)
    rw [show e = d.log2 + 1 from rfl, Nat.pow_succ]
    omega
  have hdh : 2 * d ≤ h := by have := Nat.mul_le_mul_right d hd4; omega
  have he : e ≤ d + 1 := Nat.succ_le_succ ((Nat.log2_lt (by omega)).mpr Nat.lt_two_pow_self).le
  refine ⟨h, e, d + 1, hlo, hhi, hh, hspace, he, by omega,
    lt_of_le_of_lt (by omega : h + 1 ≤ 2 ^ d) (Nat.pow_lt_pow_right Nat.one_lt_two hds),
    by rw [Nat.pow_succ]; omega, by rw [Nat.pow_succ]; omega, ?_⟩
  calc (2 ^ e + 1) * 2 ^ e ≤ (2 * d + 1) * (2 * d) :=
        Nat.mul_le_mul (Nat.add_le_add_right hsd 1) hsd
    _ = 4 * (d * d) + 2 * d := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm d 2 d, ← Nat.mul_assoc]
    _ ≤ 16 * h := by omega

end Cslib.Logic.FO.Ordered.Multiplication
