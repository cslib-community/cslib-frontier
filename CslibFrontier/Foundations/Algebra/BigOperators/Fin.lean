/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Fin.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel

/-!
# Truncation, telescoping and summation by parts for finite sums

A finite-vector sum agrees with a shorter range sum when all omitted summands vanish.
`sum_univ_adjacent_differences` telescopes differences along a sequence of indexed pairs.
`sum_univ_smul_by_parts_prefix` and `sum_univ_smul_by_parts_tail` express summation by parts
using cumulative sums from the left or from the right.
-/

public section

open Finset
namespace Fin

/-- A sum over `Fin n` of a function vanishing from `k` on is a sum over `range k`. -/
theorem sum_eq_sum_range_of_eq_zero {M : Type*} [AddCommMonoid M] {n k : ℕ} (hk : k ≤ n)
    (f : ℕ → M) (hf : ∀ j, k ≤ j → f j = 0) :
    ∑ j : Fin n, f j = ∑ j ∈ range k, f j := by
  rw [Fin.sum_univ_eq_sum_range f n, ← Finset.sum_range_add_sum_Ico _ hk,
    Finset.sum_eq_zero (s := Ico k n) fun j hj => hf j (Finset.mem_Ico.1 hj).1, add_zero]

/-- The differences within indexed pairs and across consecutive pairs telescope
to the difference from the first entry to the last exit. -/
theorem sum_univ_adjacent_differences {M : Type*} [AddCommGroup M] {n : ℕ}
    (entry exit : Fin (n + 1) → M) :
    (∑ i, (exit i - entry i)) + ∑ i : Fin n, (entry i.succ - exit i.castSucc) =
      exit (Fin.last n) - entry 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc exit, Fin.sum_univ_succ entry]
  abel

/-- A weighted sum of within-round potential drops from `a` to `b` is bounded by the
endpoint difference in weighted slack plus the inter-round drift. The `hslack` condition
compares weights at the same potential and holds automatically for constant weights. -/
theorem sum_range_mul_sub_le_of_adjacent {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedAddMonoid R] (w a b drift : ℕ → R) (D : R) (T : ℕ)
    (hslack : ∀ t < T, w t * (D - a (t + 1)) ≤ w (t + 1) * (D - a (t + 1)))
    (hdrift : ∀ t < T, w t * (a (t + 1) - b t) ≤ drift t) :
    ∑ t ∈ range (T + 1), w t * (a t - b t) ≤
      w T * (D - b T) - w 0 * (D - a 0) + ∑ t ∈ range T, drift t := by
  let entry (i : Fin (T + 1)) := w i * (D - a i)
  let exit (i : Fin (T + 1)) := w i * (D - b i)
  have hwithin (i : Fin (T + 1)) : exit i - entry i = w i * (a i - b i) := by
    simp only [entry, exit, ← mul_sub, sub_sub_sub_cancel_left]
  have hbetween (i : Fin T) : exit i.castSucc - entry i.succ ≤ drift i := by
    calc
      exit i.castSucc - entry i.succ ≤ w i * (D - b i) - w i * (D - a (i + 1)) :=
        sub_le_sub_left (hslack i i.isLt) _
      _ = w i * (a (i + 1) - b i) := by rw [← mul_sub, sub_sub_sub_cancel_left]
      _ ≤ drift i := hdrift i i.isLt
  have htel := sum_univ_adjacent_differences entry exit
  simp only [hwithin] at htel
  rw [← Fin.sum_univ_eq_sum_range _ (T + 1), ← Fin.sum_univ_eq_sum_range _ T]
  change _ ≤ exit (Fin.last T) - entry 0 + _
  rw [← htel, add_assoc, le_add_iff_nonneg_right, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun i _ => by
    rw [sub_add_eq_add_sub, sub_nonneg]
    exact (sub_le_iff_le_add.mp (hbetween i)).trans_eq (add_comm _ _)

/-- Summation by parts on a finite vector using prefix sums and successive differences. -/
theorem sum_univ_smul_by_parts_prefix {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {n : ℕ} (a : Fin (n + 1) → R) (b : Fin (n + 1) → M) :
    ∑ i, a i • b i =
      (∑ i, a i) • b (Fin.last n) +
        ∑ i : Fin n, (∑ j ∈ Iic i.castSucc, a j) • (b i.castSucc - b i.succ) := by
  let f (i : ℕ) := a (Fin.ofNat (n + 1) i)
  let g (i : ℕ) := b (Fin.ofNat (n + 1) i)
  have hofNat (i : Fin (n + 1)) : Fin.ofNat (n + 1) i.val = i :=
    Fin.natCast_eq_mk i.isLt
  have hprefix (k : Fin (n + 1)) :
      (∑ i ∈ range (k.val + 1), f i) = ∑ i ∈ Iic k, a i := by
    rw [Nat.range_succ_eq_Iic, ← map_valEmbedding_Iic, sum_map]
    exact sum_congr rfl fun i _ => congrArg a (hofNat i)
  have htotal : ∑ i ∈ range (n + 1), f i = ∑ i, a i := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [f, hofNat]
  have hlast : g n = b (Fin.last n) := congrArg b (hofNat (Fin.last n))
  calc
    ∑ i, a i • b i = ∑ i ∈ range (n + 1), f i • g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [f, g, hofNat]
    _ = _ := by
      rw [sum_range_by_parts' f g, Nat.add_sub_cancel, htotal, hlast, sub_eq_add_neg,
        ← sum_neg_distrib, ← Fin.sum_univ_eq_sum_range _ n]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      have hi := hprefix i.castSucc
      simp only [Fin.val_castSucc] at hi
      rw [hi]
      simp only [g, show Fin.ofNat (n + 1) i.val = i.castSucc from hofNat i.castSucc,
        show Fin.ofNat (n + 1) (i.val + 1) = i.succ from hofNat i.succ, ← smul_neg, neg_sub]

/-- Summation by parts on a finite vector using tail sums and successive differences. -/
theorem sum_univ_smul_by_parts_tail {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {n : ℕ} (a : Fin (n + 1) → R) (b : Fin (n + 1) → M) :
    ∑ i, a i • b i =
      (∑ i, a i) • b 0 +
        ∑ i : Fin n, (∑ j ∈ Ici i.succ, a j) • (b i.succ - b i.castSucc) := by
  have h := sum_univ_smul_by_parts_prefix (a ∘ revPerm) (b ∘ revPerm)
  have hs : (∑ i : Fin (n + 1), a i.rev • b i.rev) = ∑ i, a i • b i :=
    Equiv.sum_comp revPerm (fun i => a i • b i)
  have htotal : (∑ i : Fin (n + 1), a i.rev) = ∑ i, a i := Equiv.sum_comp revPerm a
  have htail (i : Fin n) :
      (∑ j ∈ Iic i.castSucc, a j.rev) = ∑ j ∈ Ici i.rev.succ, a j := by
    rw [← rev_castSucc, ← map_revPerm_Iic i.castSucc, Finset.sum_map]
    rfl
  simp only [Function.comp_apply, show ∀ i : Fin (n + 1), revPerm i = i.rev from fun _ => rfl,
    hs, htotal, rev_last, htail, rev_castSucc, rev_succ] at h
  exact h.trans (congrArg ((∑ i, a i) • b 0 + ·)
    (Equiv.sum_comp revPerm fun i => (∑ j ∈ Ici i.succ, a j) • (b i.succ - b i.castSucc)))

end Fin
