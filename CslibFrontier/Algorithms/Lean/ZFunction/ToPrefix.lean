/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.KMP.Search
public import CslibFrontier.Algorithms.Lean.ZFunction.Basic

/-!
# Converting the Z table to the KMP prefix table

A proper border of length `k` in the prefix ending at position `t - 1` starts at `j = t - k`.
The Z value at `j` covers that border precisely when `k ≤ z[j]`. Thus the earliest positive
starting position gives the longest border. Once the Z value at a position fails to reach
the current end, it also fails at every later end, and the scan can discard that position.

`zToPrefix` reads only the table. The convention `z[0] = n` is immaterial because a proper
border starts after zero. `zToPrefix_zArray` identifies the result with the KMP construction
for every word, including the empty word.
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

/-- Scan the Z table for the earliest positive start covering the prefix of length `t`.
The entries in `acc` concern the shorter prefixes. A failed comparison advances the candidate
start `j`; a successful one emits the border length and advances the prefix end. At `j = t`
the length is zero regardless of the table entry, including at the right boundary. -/
@[expose] def zToPrefixLoop (z : Array ℕ) (t j : ℕ) (acc : Array ℕ) : Array ℕ :=
  if t ≤ z.size then
    if z.getD j 0 < t - j then
      zToPrefixLoop z t (j + 1) acc
    else
      zToPrefixLoop z (t + 1) j (acc.push (t - j))
  else
    acc
termination_by (z.size + 1 - t) + (z.size + 1 - j)
decreasing_by all_goals omega

/-- Compute the KMP prefix table from the Z table, with entry `t - 1` giving the longest
proper border of the prefix of length `t` when the input is a realizable Z table. -/
@[expose] def zToPrefix (z : Array ℕ) : Array ℕ :=
  zToPrefixLoop z 1 1 #[]

private theorem size_zToPrefixLoop (z : Array ℕ) (t j : ℕ) (acc : Array ℕ) :
    (zToPrefixLoop z t j acc).size = acc.size + (z.size + 1 - t) := by
  fun_induction zToPrefixLoop z t j acc with
  | case1 _ _ _ _ _ ih => exact ih
  | case2 t j acc ht _ ih => rw [ih, Array.size_push]; omega
  | case3 t j acc ht => omega

/-- Every input entry has one corresponding output entry, including for unrealizable tables. -/
@[simp] theorem size_zToPrefix (z : Array ℕ) : (zToPrefix z).size = z.size := by
  simp [zToPrefix, size_zToPrefixLoop]

variable {α : Type*} [DecidableEq α]

/-- A proper border of a prefix is exactly a match of the same length at its starting position. -/
theorem isProperBorderLen_take_iff_le_lcpLen {s : List α} {t k : ℕ} (ht : t ≤ s.length)
    (hk : k < t) :
    KMP.IsProperBorderLen (s.take t) k ↔ k ≤ List.lcpLen s (s.drop (t - k)) := by
  rw [KMP.isProperBorderLen_iff_take_eq_drop, List.length_take_of_le ht, List.take_take,
    Nat.min_eq_left hk.le, List.le_lcpLen_iff, List.length_drop, List.take_drop,
    Nat.sub_add_cancel hk.le]
  have hlen : k ≤ s.length := by omega
  have hdrop : k ≤ s.length - (t - k) := by omega
  simp only [hk, hlen, hdrop, true_and]

private theorem getD_zArray (p : Array α) (j : ℕ) :
    (zArray p).getD j 0 = List.lcpLen p.toList (p.toList.drop j) := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hj : j < (zArray p).size
  · rw [Array.getElem?_eq_getElem hj, Option.getD_some, getElem_zArray]
  · have hlen : p.toList.length ≤ j := by
      simpa only [size_zArray, Array.length_toList, not_lt] using hj
    rw [Array.getElem?_eq_none (Nat.le_of_not_gt hj), Option.getD_none,
      List.drop_eq_nil_of_le hlen, List.lcpLen_nil_right]

private theorem borderLen_of_first_start (p : Array α) {t j : ℕ} (ht : t ≤ p.size)
    (hj : 0 < j) (hjt : j ≤ t) (hit : t - j ≤ (zArray p).getD j 0)
    (miss : ∀ i, 0 < i → i < j → (zArray p).getD i 0 < t - i) :
    t - j = KMP.borderLen p.toList t := by
  have hlen : t ≤ p.toList.length := by simpa using ht
  rw [getD_zArray] at hit
  have hborder : KMP.IsProperBorderLen (p.toList.take t) (t - j) :=
    (isProperBorderLen_take_iff_le_lcpLen hlen (by omega)).mpr (by
      rwa [show t - (t - j) = j by omega])
  apply Nat.le_antisymm (KMP.le_maxBorderLen_of_isProperBorderLen hborder)
  change KMP.borderLen p.toList t ≤ t - j
  have hmax : KMP.IsProperBorderLen (p.toList.take t) (KMP.borderLen p.toList t) :=
    KMP.isProperBorderLen_maxBorderLen (by rw [List.length_take_of_le hlen]; omega)
  have hlt : KMP.borderLen p.toList t < t := by
    simpa only [List.length_take_of_le hlen] using hmax.1
  by_contra! h
  have old := miss (t - KMP.borderLen p.toList t) (by omega) (by omega)
  rw [getD_zArray] at old
  have fits := (isProperBorderLen_take_iff_le_lcpLen hlen hlt).mp hmax
  omega

private theorem zToPrefixLoop_correct (p : Array α) (t j : ℕ) (acc : Array ℕ)
    (hj : 0 < j) (hjt : j ≤ t)
    (miss : ∀ i, 0 < i → i < j → (zArray p).getD i 0 < t - i)
    (hacc : acc.toList = (KMP.computePrefix p).toList.take (t - 1)) :
    zToPrefixLoop (zArray p) t j acc = KMP.computePrefix p := by
  fun_induction zToPrefixLoop (zArray p) t j acc with
  | case1 t j acc ht hshort ih =>
    refine ih (by omega) (by omega) (fun i hi hij => ?_) hacc
    by_cases heq : i = j
    · simpa only [heq] using hshort
    · exact miss i hi (by omega)
  | case2 t j acc ht hfit ih =>
    have hsize : t ≤ p.size := by simpa only [size_zArray] using ht
    have hval := borderLen_of_first_start p hsize hj hjt (Nat.le_of_not_gt hfit) miss
    refine ih hj (by omega) (fun i hi hij => ?_) ?_
    · have := miss i hi hij
      omega
    · have hidx : t - 1 < (KMP.computePrefix p).size := by rw [KMP.computePrefix_size]; omega
      rw [Array.toList_push, hacc, show t + 1 - 1 = (t - 1) + 1 by omega, List.take_add_one,
        List.getElem?_eq_getElem (by simpa using hidx), Option.toList_some, Array.getElem_toList,
        KMP.getElem_computePrefix, show t - 1 + 1 = t by omega, hval]
  | case3 t j acc ht =>
    apply Array.toList_inj.mp
    rw [hacc, List.take_of_length_le]
    simp only [Array.length_toList, KMP.computePrefix_size, size_zArray] at *
    omega

/-- Converting the Z table of any array gives its KMP prefix table. -/
theorem zToPrefix_zArray (p : Array α) : zToPrefix (zArray p) = KMP.computePrefix p :=
  zToPrefixLoop_correct p 1 1 #[] (by decide) (by decide) (by omega) (by simp)

end Cslib.Algorithms.Lean.ZFunction
