/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import CslibFrontier.Algorithms.Lean.SuffixArray.Basic
import CslibFrontier.Foundations.Data.List.Lex

/-!
# Pattern search in a suffix array

The suffixes of `w` that start with a pattern `p` occupy a contiguous range of ranks in the suffix
array, because the words with prefix `p` form an interval of the lexicographic order. Two binary
searches over `sa` find the endpoints of that range (the plain search of `[ManberMyers1993]`,
without LCP information), comparing `p` with at most `|p|` characters of a suffix per probe.

Query-complexity bounds for bisection are proved in
`CslibFrontier.Algorithms.Lean.Query.BinarySearch`, and machine-level `O(|p| log |w|)` running-time
bounds on word arrays are proved in `CslibFrontier.Algorithms.WordRAM.SuffixArray`.

## Source Conventions

* **Result:** `search w sa p = (lo, hi)` is the half-open rank interval `[lo, hi)`; the
  occurrences of `p` are the positions `sa[lo], …, sa[hi - 1]`, listed in suffix order rather than
  text order.
* **Empty pattern:** `p = []` returns `(0, |w|)`, every position `i < |w|`. Unlike
  `Cslib.Algorithms.Lean.KMP.kmpMatchesList`, the position `|w|` of the empty suffix is not
  reported, since the suffix array does not list it.

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.cmpSuffix`: compare `p` with a suffix of `w`, up to `|p|`
  characters.
* `Cslib.Algorithms.Lean.SuffixArray.probeBelow`, `probeAtMost`: threshold predicates on ranks for
  the lower and upper endpoints.
* `Cslib.Algorithms.Lean.SuffixArray.searchArray`, `search`: the rank interval of the suffixes
  starting with `p`.
* `Cslib.Algorithms.Lean.SuffixArray.occurrences`: the positions of the occurrences of `p`.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.cmpSuffix_eq`: `cmpSuffix w p i` compares `p` with
  `(w.drop i).take |p|`.
* `Cslib.Algorithms.Lean.SuffixArray.searchArray_spec` and `search_spec`: on a suffix array, the
  suffix of rank `r` starts with `p` iff `lo ≤ r < hi`.
* `Cslib.Algorithms.Lean.SuffixArray.mem_occurrences`: `i ∈ occurrences w sa p` iff `i < |w|` and
  `p` occurs in `w` at position `i`.

## References

* [U. Manber and G. Myers, *Suffix Arrays: A New Method for On-Line String
  Searches*][ManberMyers1993]
-/

public section

namespace Cslib.Algorithms.Lean.SuffixArray

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ## Comparing a pattern with a suffix -/

section Compare

variable [LinearOrder α]

/-- Compare the pattern `p` with the first `|p|` characters of the suffix of `w` at position
`i`. -/
@[expose] def cmpSuffix (w : Array α) : List α → ℕ → Ordering
  | [], _ => .eq
  | a :: p, i =>
    if hi : i < w.size then
      match compare a w[i] with
      | .lt => .lt
      | .gt => .gt
      | .eq => cmpSuffix w p (i + 1)
    else
      .gt

/-- `cmpSuffix w p i` compares `p` with the window `(w.drop i).take |p|` of the same length as
`p` (shorter if the suffix is shorter). -/
theorem cmpSuffix_eq (w : Array α) (p : List α) (i : ℕ) :
    cmpSuffix w p i =
      if p < (w.toList.drop i).take p.length then .lt
      else if p = (w.toList.drop i).take p.length then .eq else .gt := by
  induction p generalizing i with
  | nil =>
    simp only [cmpSuffix, List.length_nil, List.take_zero, lt_self_iff_false, ↓reduceIte]
  | cons a p ih =>
    rw [cmpSuffix]
    by_cases hi : i < w.size
    · simp only [hi, ↓reduceDIte]
      rw [List.drop_eq_getElem_cons (i := i) (l := w.toList) (by simpa using hi),
        List.length_cons, List.take_succ_cons, Array.getElem_toList]
      rcases lt_trichotomy a w[i] with h | rfl | h
      · have hlt : a :: p < w[i] :: (w.toList.drop (i + 1)).take p.length := List.Lex.rel h
        simp only [compare_lt_iff_lt.mpr h, hlt, ↓reduceIte]
      · have e1 : w[i] :: p < w[i] :: (w.toList.drop (i + 1)).take p.length ↔
            p < (w.toList.drop (i + 1)).take p.length := List.lex_cons_iff
        simp only [compare_eq_iff_eq.mpr rfl, e1, List.cons.injEq, true_and, ih (i + 1)]
      · have hgt : w[i] :: (w.toList.drop (i + 1)).take p.length < a :: p := List.Lex.rel h
        simp only [compare_gt_iff_gt.mpr h, not_lt_of_gt hgt, List.cons.injEq, h.ne', false_and,
          ↓reduceIte]
    · have hgt : [] < a :: p := List.Lex.nil
      simp only [hi, ↓reduceDIte, List.drop_eq_nil_of_le (Array.length_toList ▸ Nat.not_lt.mp hi),
        List.take_nil, not_lt_of_gt hgt, reduceCtorEq, ↓reduceIte]

/-- `cmpSuffix` reports `.gt` iff the window of the suffix is below `p`. -/
theorem cmpSuffix_eq_gt_iff (w : Array α) (p : List α) (i : ℕ) :
    cmpSuffix w p i = .gt ↔ (w.toList.drop i).take p.length < p := by
  rw [cmpSuffix_eq]
  split_ifs with h1 h2
  · simp [h1.le]
  · simp [h2.le]
  · simp [lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)]

/-- `cmpSuffix` reports `.eq` or `.gt` iff the window of the suffix is at most `p`. -/
theorem cmpSuffix_ne_lt_iff (w : Array α) (p : List α) (i : ℕ) :
    cmpSuffix w p i ≠ .lt ↔ (w.toList.drop i).take p.length ≤ p := by
  rw [cmpSuffix_eq]
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2.symm.le]
  · simp [not_lt.mp h1]

/-- `cmpSuffix` reports `.eq` iff `p` is a prefix of the suffix. -/
theorem cmpSuffix_eq_eq_iff (w : Array α) (p : List α) (i : ℕ) :
    cmpSuffix w p i = .eq ↔ p <+: w.toList.drop i := by
  rw [cmpSuffix_eq, List.prefix_iff_eq_take]
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (ne_of_lt h1)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2

end Compare

/-! ## Searching a suffix array -/

section Search

variable [LinearOrder α]

/-- Binary-search probe at rank `r`: is the `|p|`-window of the suffix of rank `r` below `p`? -/
@[expose] def probeBelow (w : Array α) (sa : Array ℕ) (p : List α) (r : ℕ) : Bool :=
  decide (cmpSuffix w p sa[r]! = .gt)

/-- Binary-search probe at rank `r`: is the `|p|`-window of the suffix of rank `r` at most
`p`? -/
@[expose] def probeAtMost (w : Array α) (sa : Array ℕ) (p : List α) (r : ℕ) : Bool :=
  decide (cmpSuffix w p sa[r]! ≠ .lt)

/-- Find the range of ranks whose suffixes start with `p`, by two binary searches over `sa`:
`lo` is the first rank whose suffix's `|p|`-window is not below `p`, and `hi` is the first rank
whose window is above `p`. -/
@[expose] def searchArray (w : Array α) (sa : Array ℕ) (p : List α) : ℕ × ℕ :=
  (lowerBound (probeBelow w sa p) 0 sa.size, lowerBound (probeAtMost w sa p) 0 sa.size)

/-- The rank interval of suffixes of `w` starting with `p`. -/
@[expose] def search (w : List α) (sa : List ℕ) (p : List α) : ℕ × ℕ :=
  searchArray w.toArray sa.toArray p

/-- The starting positions of the occurrences of `p` in `w`, listed in suffix-array order. -/
@[expose] def occurrences (w : List α) (sa : List ℕ) (p : List α) : List ℕ :=
  let r := search w sa p
  (sa.take r.2).drop r.1

/-- Specification of the probe used to find the lower end of the rank interval. -/
theorem probeBelow_eq_true_iff (w : Array α) (sa : Array ℕ) (p : List α) {r : ℕ}
    (hr : r < sa.size) :
    probeBelow w sa p r = true ↔ (w.toList.drop sa[r]).take p.length < p := by
  simp only [probeBelow, decide_eq_true_eq]
  rw [getElem!_pos sa r hr]
  exact cmpSuffix_eq_gt_iff w p _

/-- Specification of the probe used to find the upper end of the rank interval. -/
theorem probeAtMost_eq_true_iff (w : Array α) (sa : Array ℕ) (p : List α) {r : ℕ}
    (hr : r < sa.size) :
    probeAtMost w sa p r = true ↔ (w.toList.drop sa[r]).take p.length ≤ p := by
  simp only [probeAtMost, decide_eq_true_eq]
  rw [getElem!_pos sa r hr]
  exact cmpSuffix_ne_lt_iff w p _

/-- On a suffix array, the `|p|`-windows of the suffixes are sorted by rank. -/
private theorem take_drop_le_take_drop {w : Array α} {sa : Array ℕ}
    (hsa : IsSuffixArray w.toList sa.toList) {r r' : ℕ} (hrr' : r ≤ r') (hr' : r' < sa.size)
    (n : ℕ) :
    (w.toList.drop (sa[r]'(by omega))).take n ≤ (w.toList.drop sa[r']).take n := by
  rcases Nat.lt_or_eq_of_le hrr' with hlt | rfl
  · have := hsa.drop_lt_drop (r := r) (r' := r') hlt (by simpa using hr')
    simp only [Array.getElem_toList] at this
    exact List.take_le_take_of_le (le_of_lt this) n
  · exact le_refl _

private theorem lowerBound_lt_iff {n : ℕ} (f : ℕ → Bool) {P : ∀ r, r < n → Prop}
    (hf : ∀ r (hr : r < n), f r = true ↔ P r hr)
    (hmono : ∀ r r' (hr : r < n) (hr' : r' < n), r ≤ r' → P r' hr' → P r hr) :
    lowerBound f 0 n ≤ n ∧ ∀ r (hr : r < n), P r hr ↔ r < lowerBound f 0 n := by
  obtain ⟨-, hle, hlt, hge⟩ := lowerBound_spec f (lo := 0) (hi := n)
    fun m m' _ hmm' hm' h =>
      (hf m (by omega)).2 (hmono m m' (by omega) hm' hmm' ((hf m' hm').1 h))
  refine ⟨hle, fun r hr => ⟨fun h => ?_, fun h => (hf r hr).1 (hlt r (Nat.zero_le _) h)⟩⟩
  by_contra hc
  have hfalse := hge r (by omega) hr
  rw [← Bool.not_eq_true, hf r hr] at hfalse
  exact hfalse h

/-- **Correctness of suffix-array search**: on a suffix array, `searchArray` returns ranks
`lo ≤ hi ≤ |sa|` such that the suffix of rank `r` starts with `p` exactly when `lo ≤ r < hi`. -/
theorem searchArray_spec {w : Array α} {sa : Array ℕ} (hsa : IsSuffixArray w.toList sa.toList)
    (p : List α) :
    (searchArray w sa p).1 ≤ (searchArray w sa p).2 ∧ (searchArray w sa p).2 ≤ sa.size ∧
      ∀ (r : ℕ) (hr : r < sa.size),
        p <+: w.toList.drop sa[r] ↔ (searchArray w sa p).1 ≤ r ∧ r < (searchArray w sa p).2 := by
  simp only [searchArray]
  obtain ⟨hlo_le, hbelow⟩ := lowerBound_lt_iff (probeBelow w sa p)
    (fun r hr => probeBelow_eq_true_iff w sa p hr)
    (fun m m' _ hm' hmm' h => lt_of_le_of_lt (take_drop_le_take_drop hsa hmm' hm' p.length) h)
  obtain ⟨hhi_le, hatmost⟩ := lowerBound_lt_iff (probeAtMost w sa p)
    (fun r hr => probeAtMost_eq_true_iff w sa p hr)
    (fun m m' _ hm' hmm' h => le_trans (take_drop_le_take_drop hsa hmm' hm' p.length) h)
  set lo := lowerBound (probeBelow w sa p) 0 sa.size
  set hi := lowerBound (probeAtMost w sa p) 0 sa.size
  have hlohi : lo ≤ hi := by
    by_contra h
    have hlt : hi < sa.size := by omega
    have := (hatmost hi hlt).1 ((hbelow hi hlt).2 (by omega)).le
    omega
  refine ⟨hlohi, hhi_le, fun r hr => ?_⟩
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h
    refine ⟨?_, (hatmost r hr).1 h.symm.le⟩
    by_contra hc
    exact ((hbelow r hr).2 (by omega)).ne h.symm
  · rintro ⟨h1, h2⟩
    have hnlt : ¬ (w.toList.drop sa[r]).take p.length < p :=
      fun h => by have := (hbelow r hr).1 h; omega
    exact (le_antisymm ((hatmost r hr).2 h2) (not_lt.mp hnlt)).symm

/-- **Correctness of suffix-array search** on lists. -/
theorem search_spec {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) (p : List α) :
    (search w sa p).1 ≤ (search w sa p).2 ∧ (search w sa p).2 ≤ sa.length ∧
      ∀ (r : ℕ) (hr : r < sa.length),
        p <+: w.drop sa[r] ↔ (search w sa p).1 ≤ r ∧ r < (search w sa p).2 := by
  have := searchArray_spec (w := w.toArray) (sa := sa.toArray) hsa p
  simpa only [search, List.size_toArray, List.getElem_toArray] using this

/-- `occurrences w sa p` lists exactly the positions where `p` occurs in `w` (as a prefix of a
nonempty suffix). -/
theorem mem_occurrences {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) (p : List α)
    {i : ℕ} : i ∈ occurrences w sa p ↔ i < w.length ∧ p <+: w.drop i := by
  rw [show occurrences w sa p = (sa.take (search w sa p).2).drop (search w sa p).1 from rfl]
  obtain ⟨hlohi, hhi, hspec⟩ := search_spec hsa p
  set lo := (search w sa p).1
  set hi := (search w sa p).2
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.length_drop, List.length_take] at hk
    simp only [List.getElem_drop, List.getElem_take]
    have hr : lo + k < sa.length := by omega
    exact ⟨hsa.getElem_lt hr, (hspec (lo + k) hr).mpr ⟨by omega, by omega⟩⟩
  · rintro ⟨hi', hp⟩
    obtain ⟨r, hr, rfl⟩ := hsa.exists_getElem_eq hi'
    obtain ⟨h1, h2⟩ := (hspec r hr).mp hp
    refine ⟨r - lo, by simp only [List.length_drop, List.length_take]; omega, ?_⟩
    simp only [List.getElem_drop, List.getElem_take]
    congr 1
    omega

end Search

end Cslib.Algorithms.Lean.SuffixArray
