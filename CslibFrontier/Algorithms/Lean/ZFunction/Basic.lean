/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.CommonPrefix

/-!
# The Z-algorithm

The Z-function of a word `s` records, at each position `i`, the length of the longest common
prefix of `s` and its suffix `s.drop i`. The Z-algorithm (`[Gusfield1997]`, Section 1.4) computes
all of these values from left to right. It keeps the box `[l, r)`, the rightmost interval found
so far that repeats a prefix of `s`. At a position `i` inside the box, the value `z[i - l]`
either gives `z[i]` outright or shows that `z[i] ≥ r - i`, so explicit comparisons start at
`r`.

Machine-level `O(|s|)` and `O(|p| + |t|)` running-time bounds on word arrays are proved in
`CslibFrontier.Algorithms.WordRAM.ZFunction`.

## Source Conventions

* **Indexing:** positions are `0`-based, and `z[0] = |s|` (the whole word is a prefix of
  itself). Gusfield indexes from `1` and leaves `Z_1` undefined.
* **Box:** `[l, r)` is half-open. Gusfield's box `[l, r]` is closed and `1`-indexed. Initially
  `l = r = 0`, the empty box.

## Main definitions

* `Cslib.Algorithms.Lean.ZFunction.zFunction`: the specification
  `z[i] = List.lcpLen s (s.drop i)`.
* `Cslib.Algorithms.Lean.ZFunction.zArray`, `zAlgorithm`: the pure Z-algorithm on arrays and its
  list wrapper.

## Main results

* `Cslib.Algorithms.Lean.ZFunction.min_lcpLen_zBox`: inside a valid Z-box `[l, r)`, `s.drop (i - l)`
  and `s.drop i` have the same longest common prefix with `s` up to `r - i`.
* `Cslib.Algorithms.Lean.ZFunction.zArray_toList`, `size_zArray`, `getElem_zArray`, and
  `zAlgorithm_eq_zFunction`: the algorithm computes the Z-function on every input.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

variable {α : Type*} [DecidableEq α]

/-! ## Specification -/

/-- The Z-function of `s`: at each position `i < |s|`, the length of the longest common prefix
of `s` and `s.drop i`. -/
@[expose] def zFunction (s : List α) : List ℕ :=
  (List.range s.length).map fun i => List.lcpLen s (s.drop i)

@[simp] theorem length_zFunction (s : List α) : (zFunction s).length = s.length := by
  rw [zFunction, List.length_map, List.length_range]

theorem getElem_zFunction (s : List α) (i : ℕ) (hi : i < (zFunction s).length) :
    (zFunction s)[i]'hi = List.lcpLen s (s.drop i) := by
  simp only [zFunction, List.getElem_map, List.getElem_range]

/-- The Z-function at `0` is the length of the word. -/
theorem getElem_zFunction_zero (s : List α) (hs : 0 < (zFunction s).length) :
    (zFunction s)[0]'hs = s.length := by
  rw [getElem_zFunction, List.drop_zero, List.lcpLen_self]

/-! ## The algorithm -/

/-- Starting from a known common prefix length `h`, extend the common prefix of the suffixes of
`s` at positions `j` and `i` one character at a time. -/
private def extend (s : Array α) (j i h : ℕ) : ℕ :=
  if hlt : j + h < s.size ∧ i + h < s.size then
    if s[j + h]'hlt.1 = s[i + h]'hlt.2 then
      extend s j i (h + 1)
    else
      h
  else
    h
termination_by s.size - (i + h)

private theorem extend_eq_add_lcpLen (s : Array α) (j i h : ℕ) :
    extend s j i h = h + List.lcpLen (s.toList.drop (j + h)) (s.toList.drop (i + h)) := by
  fun_induction extend s j i h with
  | case1 h hlt heq ih =>
    rw [ih, List.drop_eq_getElem_cons (i := j + h) (l := s.toList) (by simpa using hlt.1),
      List.drop_eq_getElem_cons (i := i + h) (l := s.toList) (by simpa using hlt.2),
      Array.getElem_toList, Array.getElem_toList, heq, List.lcpLen_cons_cons_self,
      show j + (h + 1) = j + h + 1 by omega, show i + (h + 1) = i + h + 1 by omega]
    omega
  | case2 h hlt hne =>
    rw [List.drop_eq_getElem_cons (i := j + h) (l := s.toList) (by simpa using hlt.1),
      List.drop_eq_getElem_cons (i := i + h) (l := s.toList) (by simpa using hlt.2),
      Array.getElem_toList, Array.getElem_toList, List.lcpLen_cons_cons]
    simp only [hne, ↓reduceIte, Nat.add_zero]
  | case3 h hlt =>
    have h1 := List.lcpLen_le_length_left (s.toList.drop (j + h)) (s.toList.drop (i + h))
    have h2 := List.lcpLen_le_length_right (s.toList.drop (j + h)) (s.toList.drop (i + h))
    simp only [List.length_drop, Array.length_toList] at h1 h2
    omega

/-- The main loop of the Z-algorithm at position `i`, with box `[l, r)` and the values `z` at
the positions before `i`. If `z[i - l] < r - i` then `z[i] = z[i - l]`; otherwise extend the
common prefix of `s` and `s.drop i` from `r - i`. When `i ≥ r` the test fails because `r - i = 0`,
whatever the read returns (`Array.getD` returns `0` outside `z`). -/
private def zLoop (s : Array α) (i l r : ℕ) (z : Array ℕ) : Array ℕ :=
  if i < s.size then
    if z.getD (i - l) 0 < r - i then
      zLoop s (i + 1) l r (z.push (z.getD (i - l) 0))
    else
      let k := extend s 0 i (r - i)
      zLoop s (i + 1) i (i + k) (z.push k)
  else
    z
termination_by s.size - i

/-- The pure Z-algorithm on arrays. The value at `0` is the length of the word; the loop computes
the remaining positions from left to right. -/
def zArray (s : Array α) : Array ℕ :=
  if s.size = 0 then #[] else zLoop s 1 0 0 #[s.size]

/-- The Z-algorithm on lists. -/
def zAlgorithm (s : List α) : List ℕ :=
  (zArray s.toArray).toList

/-! ## Correctness -/

/-- **Z-box transfer lemma** (`[Gusfield1997]`, Section 1.4): if `[l, r)` repeats a prefix of `s`
(`r ≤ l + List.lcpLen s (s.drop l)`) and `l ≤ i ≤ r`, then `s.drop (i - l)` and `s.drop i` agree on
their longest common prefix with `s` up to `r - i`. -/
theorem min_lcpLen_zBox (s : List α) {i l r : ℕ} (hli : l ≤ i) (hir : i ≤ r)
    (hrl : r ≤ l + List.lcpLen s (s.drop l)) :
    min (List.lcpLen s (s.drop (i - l))) (r - i) = min (List.lcpLen s (s.drop i)) (r - i) := by
  obtain ⟨_, _, htake⟩ :=
    List.le_lcpLen_iff.mp (show r - l ≤ List.lcpLen s (s.drop l) by omega)
  apply List.min_lcpLen_eq_of_take_eq
  have hdrop : s.drop i = (s.drop l).drop (i - l) := by
    rw [List.drop_drop, Nat.add_sub_of_le hli]
  rw [hdrop, List.take_drop, List.take_drop, show i - l + (r - i) = r - l by omega, htake]

private theorem z_push_getElem {s : Array α} {z : Array ℕ} {i v : ℕ} (hz : z.size = i)
    (hzs : ∀ (j : ℕ) (hj : j < i), z[j]'(hz ▸ hj) = List.lcpLen s.toList (s.toList.drop j))
    (hv : v = List.lcpLen s.toList (s.toList.drop i))
    (j : ℕ) (hj : j < i + 1) :
    (z.push v)[j]'(by rw [Array.size_push, hz]; exact hj) =
      List.lcpLen s.toList (s.toList.drop j) := by
  rw [Array.getElem_push]
  split_ifs with hji
  · exact hzs j (hz ▸ hji)
  · rw [show j = i by omega]
    exact hv

private theorem getD_sub_eq_lcpLen {s : Array α} {z : Array ℕ} {i l r : ℕ}
    (hi1 : 1 ≤ i) (hl0 : r = 0 ∨ 0 < l) (hir : i < r) (hz : z.size = i)
    (hzs : ∀ (j : ℕ) (hj : j < i), z[j]'(hz ▸ hj) = List.lcpLen s.toList (s.toList.drop j)) :
    z.getD (i - l) 0 = List.lcpLen s.toList (s.toList.drop (i - l)) := by
  have hil : i - l < i := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (hz ▸ hil), Option.getD_some]
  exact hzs (i - l) hil

/-- Loop invariant: the values before `i` are correct, `l < i`, the box `[l, r)` repeats a
prefix of `s` (`r ≤ l + z[l]`), and the box is empty when `l = 0`. -/
private theorem zLoop_spec (s : Array α) (i l r : ℕ) (z : Array ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ s.size) (hz : z.size = i)
    (hzs : ∀ (j : ℕ) (hj : j < i), z[j]'(hz ▸ hj) = List.lcpLen s.toList (s.toList.drop j))
    (hl : l < i) (hl0 : r = 0 ∨ 0 < l)
    (hrl : r ≤ l + List.lcpLen s.toList (s.toList.drop l)) (hr : r ≤ s.size) :
    (zLoop s i l r z).toList = zFunction s.toList := by
  fun_induction zLoop s i l r z with
  | case3 i l r z his =>
    refine List.ext_getElem (by simp only [Array.length_toList, length_zFunction]; omega)
      fun j h1 h2 => ?_
    simp only [Array.length_toList] at h1
    rw [Array.getElem_toList, getElem_zFunction, hzs j (hz ▸ h1)]
  | case1 i l r z his hcopy ih =>
    have hir : i < r := by omega
    have hval : z.getD (i - l) 0 = List.lcpLen s.toList (s.toList.drop i) := by
      have := getD_sub_eq_lcpLen hi1 hl0 hir hz hzs
      have := min_lcpLen_zBox s.toList hl.le hir.le hrl
      grind
    exact ih (by omega) (by omega) (by rw [Array.size_push, hz]) (z_push_getElem hz hzs hval)
      (by omega) hl0 hrl hr
  | case2 i l r z his hncopy k ih =>
    have hh : r - i ≤ List.lcpLen s.toList (s.toList.drop i) := by
      by_cases hir : i < r
      · have := getD_sub_eq_lcpLen hi1 hl0 hir hz hzs
        have := min_lcpLen_zBox s.toList hl.le hir.le hrl
        grind
      · simp [Nat.sub_eq_zero_of_le (Nat.not_lt.mp hir)]
    have hext : k = List.lcpLen s.toList (s.toList.drop i) := by
      dsimp only [k]
      rw [extend_eq_add_lcpLen, List.lcpLen_eq_add_lcpLen_drop hh, List.drop_drop, Nat.zero_add]
    have hlen := List.lcpLen_le_length_right s.toList (s.toList.drop i)
    simp only [List.length_drop, Array.length_toList] at hlen
    exact ih (by omega) (by omega) (by rw [Array.size_push, hz]) (z_push_getElem hz hzs hext)
      (by omega) (Or.inr (by omega)) (by rw [hext]) (by rw [hext]; omega)

/-- **Correctness of the Z-algorithm**: `zArray s` computes the Z-function of `s` on every
input. -/
theorem zArray_toList (s : Array α) : (zArray s).toList = zFunction s.toList := by
  rw [zArray]
  split_ifs with h0
  · rw [zFunction, Array.length_toList, h0, List.range_zero, List.map_nil, Array.toList_empty]
  · refine zLoop_spec s 1 0 0 #[s.size] (le_refl _) (by omega) rfl (fun j hj => ?_)
      Nat.zero_lt_one (Or.inl rfl) (Nat.zero_le _) (Nat.zero_le _)
    obtain rfl : j = 0 := by omega
    rw [List.drop_zero, List.lcpLen_self, Array.length_toList]
    rfl

@[simp] theorem size_zArray (s : Array α) : (zArray s).size = s.size := by
  rw [← Array.length_toList, zArray_toList, length_zFunction, Array.length_toList]

theorem getElem_zArray (s : Array α) (i : ℕ) (hi : i < (zArray s).size) :
    (zArray s)[i]'hi = List.lcpLen s.toList (s.toList.drop i) := by
  rw [← Array.getElem_toList hi, ← getElem_zFunction s.toList i
    (by rwa [length_zFunction, Array.length_toList, ← size_zArray])]
  congr 1
  exact zArray_toList s

/-- **Correctness of the Z-algorithm** on lists. -/
theorem zAlgorithm_eq_zFunction (s : List α) : zAlgorithm s = zFunction s :=
  zArray_toList s.toArray

end Cslib.Algorithms.Lean.ZFunction
