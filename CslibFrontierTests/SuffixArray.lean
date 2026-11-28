/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.Query.BinarySearch
import CslibFrontier.Algorithms.Lean.KMP.Search
import CslibFrontier.Algorithms.Lean.SuffixArray.Basic
import CslibFrontier.Algorithms.Lean.SuffixArray.Kasai
import CslibFrontier.Algorithms.Lean.SuffixArray.Search
import CslibFrontier.Algorithms.WordRAM.BinarySearch
import CslibFrontier.Algorithms.WordRAM.SuffixArray
meta import CslibFrontier.Algorithms.Lean.KMP.Search
meta import CslibFrontier.Algorithms.WordRAM.BinarySearch
meta import CslibFrontier.Algorithms.WordRAM.SuffixArray
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
import Mathlib.Data.Char
meta import Mathlib.Data.Char

/-!
# Suffix array, Kasai LCP, binary search, and Word-RAM tests

Executable `#guard` checks and kernel-checked non-vacuity instantiations for:
* pure and query-model bisection (`Cslib.Algorithms.Lean.lowerBound`,
  `Cslib.Query.lowerBoundQ`) and Word-RAM bisection
  (`Cslib.Algorithms.WordRAM.BinarySearch`);
* pure suffix-array specification, Kasai LCP construction, and pattern search
  (`Cslib.Algorithms.Lean.SuffixArray`); and
* uniform Word-RAM `O(n)` Kasai LCP construction and `O(|p| log |sa|)` / `O(|p| log |sa| + occ)`
  suffix-array search (`Cslib.Algorithms.WordRAM.SuffixArray`).
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace Cslib.Algorithms.Lean.SuffixArray.Tests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.SuffixArray
open Cslib.Query
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.BinarySearch
open Cslib.Algorithms.WordRAM.SuffixArray

private def banana : List Char := "banana".toList
private def mississippi : List Char := "mississippi".toList

/-! ## Binary search (pure, query model, and Word-RAM) -/

-- Pure and query-model bisection on `[0, 100)` and empty `[5, 5)`.
#guard lowerBound (fun m => decide (m < 7)) 0 100 = 7
#guard lowerBound (fun m => decide (m * m ≤ 50)) 0 100 = 8
#guard (lowerBoundQ 0 100).eval (ProbeQuery.oracleOf (fun m => decide (m * m ≤ 50))) = 8
#guard (lowerBoundQ 0 100).countQueries (ProbeQuery.oracleOf (fun m => decide (m * m ≤ 50))) ≤
  Nat.log 2 100 + 1
#guard lowerBound (fun _ => true) 5 5 = 5
#guard (lowerBoundQ 5 5).countQueries (ProbeQuery.oracleOf (fun _ => true)) = 0

private meta def evalLowerBound (w : ℕ) (I : LowerBoundInput) : Option (List ℕ × ℕ) :=
  (lowerBoundCode.eval w (I.arr.length + 10) (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.BinarySearch.Reg.out), steps)

-- Sorted array with duplicates `[10, 20, 20, 20, 35, 50]` (width 6: `50 < 64`).
#guard match evalLowerBound 6 ⟨0, [10, 20, 20, 20, 35, 50]⟩ with
  | some (res, steps) => res == [0] && steps ≤ 13 * (Nat.log 2 6 + 1) + 13
  | none => false

#guard match evalLowerBound 6 ⟨20, [10, 20, 20, 20, 35, 50]⟩ with
  | some (res, steps) => res == [1] && steps ≤ 13 * (Nat.log 2 6 + 1) + 13
  | none => false

#guard match evalLowerBound 6 ⟨25, [10, 20, 20, 20, 35, 50]⟩ with
  | some (res, steps) => res == [4] && steps ≤ 13 * (Nat.log 2 6 + 1) + 13
  | none => false

#guard match evalLowerBound 6 ⟨60, [10, 20, 20, 20, 35, 50]⟩ with
  | some (res, steps) => res == [6] && steps ≤ 13 * (Nat.log 2 6 + 1) + 13
  | none => false

-- Boundary cases: empty array at minimal width 2 (`0 + 3 < 4`) and singleton array.
#guard match evalLowerBound 2 ⟨1, []⟩ with
  | some (res, steps) => res == [0] && steps ≤ 13 * (Nat.log 2 0 + 1) + 13
  | none => false

#guard match evalLowerBound 3 ⟨5, [5]⟩ with
  | some (res, steps) => res == [0] && steps ≤ 13 * (Nat.log 2 1 + 1) + 13
  | none => false

#guard match evalLowerBound 3 ⟨6, [5]⟩ with
  | some (res, steps) => res == [1] && steps ≤ 13 * (Nat.log 2 1 + 1) + 13
  | none => false

-- Kernel-checked sorted-partition witness and `ExecutesList` non-vacuity check for
-- `lowerBoundProgram`.
private theorem lb_empty_eq : (LowerBoundInput.mk 1 []).result = 0 :=
  lowerBound_of_le _ (le_refl 0)

example : ∃ n, ExecutesList 2 lowerBoundProgram (.init (LowerBoundInput.encode ⟨1, []⟩)) [0] n ∧
    n ≤ 27 := by
  have h := lowerBoundProgram_computesListInTime ⟨1, []⟩ 2 (by decide) (by decide)
  simpa only [List.length_nil, Nat.log_zero_right, Nat.zero_add, Nat.mul_one, lb_empty_eq] using h

example : ∃ res, res ≤ 3 ∧
    (∀ i (hi : i < 3), i < res → [2, 4, 7][i]'hi < 4) ∧
    (∀ i (hi : i < 3), res ≤ i → 4 ≤ [2, 4, 7][i]'hi) := by
  obtain ⟨hb, hlt, hge⟩ := lowerBound_sorted_spec ⟨4, [2, 4, 7]⟩ (by decide)
  exact ⟨_, hb, fun i _ hir => hlt i hir, hge⟩

/-! ## Suffix arrays -/

-- banana: a(5) < ana(3) < anana(1) < banana(0) < na(4) < nana(2).
#guard suffixArray banana = [5, 3, 1, 0, 4, 2]
#guard suffixArray mississippi = [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]
#guard suffixArray ([] : List Char) = []
#guard suffixArray "aaaa".toList = [3, 2, 1, 0]

-- The specification holds for the sorted positions and fails for other permutations or
-- non-permutations.
#guard decide (IsSuffixArray banana [5, 3, 1, 0, 4, 2])
#guard !decide (IsSuffixArray banana [0, 1, 2, 3, 4, 5])
#guard !decide (IsSuffixArray banana [5, 3, 1, 0, 4])
#guard !decide (IsSuffixArray banana [5, 3, 1, 0, 4, 2, 6])
#guard decide (IsSuffixArray ([] : List Char) [])

-- Uniqueness: a kernel-checked suffix array of `banana` is the only one.
example (sa : List ℕ) (h : IsSuffixArray ['b', 'a', 'n', 'a', 'n', 'a'] sa) :
    sa = [5, 3, 1, 0, 4, 2] :=
  h.unique (by decide)

/-! ## LCP arrays and Kasai et al.'s algorithm (pure and Word-RAM) -/

#guard lcpArray banana (suffixArray banana) = [0, 1, 3, 0, 0, 2]
#guard kasai banana (suffixArray banana) = [0, 1, 3, 0, 0, 2]
#guard lcpArray mississippi (suffixArray mississippi) = [0, 1, 1, 4, 0, 0, 1, 0, 2, 1, 3]
#guard kasai mississippi (suffixArray mississippi) = [0, 1, 1, 4, 0, 0, 1, 0, 2, 1, 3]
#guard kasai ([] : List Char) [] = []
#guard kasai "aaaaaaaaaa".toList (suffixArray "aaaaaaaaaa".toList) =
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

-- The height lemma on `banana`: `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1` for all `i < |w| - 1`.
#guard
  let sa := suffixArray banana
  let lcp := lcpArray banana sa
  let rk := rankArray banana.length sa
  (List.range (banana.length - 1)).all fun i => lcp[rk[i]!]! - 1 ≤ lcp[rk[i + 1]!]!

-- Non-vacuity: the correctness hypothesis is met by the reference construction.
example (w : List Char) : kasai w (suffixArray w) = lcpArray w (suffixArray w) :=
  kasai_eq_lcpArray (isSuffixArray_suffixArray w)

private def bananaWords : List ℕ := [2, 1, 14, 1, 14, 1]
private def bananaSA : List ℕ := [5, 3, 1, 0, 4, 2]
private def mississippiWords : List ℕ := [13, 9, 19, 19, 9, 19, 19, 9, 16, 16, 9]
private def mississippiSA : List ℕ := [10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2]

private meta def evalKasai (w : ℕ) (I : KasaiInput) : Option (List ℕ × ℕ) :=
  let fuel := 2 * (I.text.length + I.sa.length) + 10
  (kasaiCode.eval w fuel (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.SuffixArray.Reg.out), steps)

-- Word-RAM Kasai on `banana` (width 5: `3 * 6 + 6 + 4 = 28 < 32`), `mississippi`, and `a ^ 8`.
#guard match evalKasai 5 ⟨bananaWords, bananaSA⟩ with
  | some (lcp, steps) => lcp == [0, 1, 3, 0, 0, 2] && steps ≤ 55 * 6 + 8 * 6 + 25
  | none => false

#guard match evalKasai 6 ⟨mississippiWords, mississippiSA⟩ with
  | some (lcp, steps) => lcp == [0, 1, 1, 4, 0, 0, 1, 0, 2, 1, 3] && steps ≤ 55 * 11 + 8 * 11 + 25
  | none => false

#guard match evalKasai 6 ⟨List.replicate 8 1, [7, 6, 5, 4, 3, 2, 1, 0]⟩ with
  | some (lcp, steps) => lcp == [0, 1, 2, 3, 4, 5, 6, 7] && steps ≤ 55 * 8 + 8 * 8 + 25
  | none => false

-- Boundary cases: empty text at minimal width 3 (`4 < 8`), singleton, and malformed `sa` with
-- out-of-range index `25` (proving total execution and exact match with pure `kasai`).
#guard match evalKasai 3 ⟨[], []⟩ with
  | some (lcp, steps) => lcp == [] && steps ≤ 25
  | none => false

#guard match evalKasai 4 ⟨[7], [0]⟩ with
  | some (lcp, steps) => lcp == [0] && steps ≤ 55 * 1 + 8 * 1 + 25
  | none => false

#guard match evalKasai 5 ⟨[1, 2, 1], [25, 0]⟩ with
  | some (lcp, steps) => lcp == [0, 0, 0] && steps ≤ 55 * 3 + 8 * 2 + 25
  | none => false

example : ∃ n, ExecutesList 5 kasaiProgram
    (.init (KasaiInput.encode ⟨[1, 2, 1], [25, 0]⟩)) (kasai [1, 2, 1] [25, 0]) n ∧
    n ≤ 55 * 3 + 8 * 2 + 26 :=
  kasaiProgram_computesListInTime ⟨[1, 2, 1], [25, 0]⟩ 5 (by decide) (by decide)

-- Kernel-checked non-vacuity instantiations of `kasaiProgram_computesLcpArrayInTime`.
private theorem lcpArray_banana_eq : lcpArray [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] =
    [0, 1, 3, 0, 0, 2] := by
  apply List.ext_getElem (by simp only [length_lcpArray, List.length_cons, List.length_nil])
  intro r hr1 _
  simp only [length_lcpArray, List.length_cons, List.length_nil] at hr1
  have hle_eq {u v : List ℕ} {k : ℕ} (h1 : k ≤ List.lcpLen u v) (h2 : ¬(k + 1 ≤ List.lcpLen u v)) :
      List.lcpLen u v = k := by omega
  match r with
  | 0 => exact getElem_lcpArray_zero _ _ _
  | 1 =>
    rw [getElem_lcpArray_of_pos _ _ _ (by decide)]
    simp only [Nat.reduceSub, List.getElem_cons_zero, List.getElem_cons_succ]
    exact hle_eq (List.le_lcpLen_iff.mpr ⟨by decide, by decide, rfl⟩)
      (by rw [List.le_lcpLen_iff]; decide)
  | 2 =>
    rw [getElem_lcpArray_of_pos _ _ _ (by decide)]
    simp only [Nat.reduceSub, List.getElem_cons_zero, List.getElem_cons_succ]
    exact hle_eq (List.le_lcpLen_iff.mpr ⟨by decide, by decide, rfl⟩)
      (by rw [List.le_lcpLen_iff]; decide)
  | 3 =>
    rw [getElem_lcpArray_of_pos _ _ _ (by decide)]
    simp only [Nat.reduceSub, List.getElem_cons_zero, List.getElem_cons_succ]
    exact hle_eq (Nat.zero_le _) (by rw [List.le_lcpLen_iff]; decide)
  | 4 =>
    rw [getElem_lcpArray_of_pos _ _ _ (by decide)]
    simp only [Nat.reduceSub, List.getElem_cons_zero, List.getElem_cons_succ]
    exact hle_eq (Nat.zero_le _) (by rw [List.le_lcpLen_iff]; decide)
  | 5 =>
    rw [getElem_lcpArray_of_pos _ _ _ (by decide)]
    simp only [Nat.reduceSub, List.getElem_cons_zero, List.getElem_cons_succ]
    exact hle_eq (List.le_lcpLen_iff.mpr ⟨by decide, by decide, rfl⟩)
      (by rw [List.le_lcpLen_iff]; decide)
  | _ + 6 => omega

example : ∃ n, ExecutesList 5 kasaiProgram
    (.init (KasaiInput.encode ⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2]⟩))
    [0, 1, 3, 0, 0, 2] n ∧ n ≤ 63 * 6 + 26 := by
  have hsa : IsSuffixArray [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] := by decide
  have h := kasaiProgram_computesLcpArrayInTime ⟨⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2]⟩, hsa⟩
    5 (by dsimp only; decide) (by dsimp only; decide)
  simpa only [List.length_cons, List.length_nil, lcpArray_banana_eq] using h

example : ∃ n, ExecutesList 3 kasaiProgram (.init (KasaiInput.encode ⟨[], []⟩)) [] n ∧
    n ≤ 26 := by
  have hsa : IsSuffixArray ([] : List ℕ) [] := by decide
  have h := kasaiProgram_computesLcpArrayInTime ⟨⟨[], []⟩, hsa⟩ 3
    (by dsimp only; decide) (by dsimp only; decide)
  have hlcp : lcpArray ([] : List ℕ) [] = [] := by
    apply List.eq_nil_of_length_eq_zero; simp only [length_lcpArray, List.length_nil]
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, hlcp] using h

/-! ## Pattern search (pure and Word-RAM) -/

-- "ana" occurs at positions 3 and 1 of `banana`, ranks 1 and 2.
#guard search banana (suffixArray banana) "ana".toList = (1, 3)
#guard occurrences banana (suffixArray banana) "ana".toList = [3, 1]
#guard occurrences mississippi (suffixArray mississippi) "issi".toList = [4, 1]
#guard occurrences mississippi (suffixArray mississippi) "ssi".toList = [5, 2]
#guard occurrences mississippi (suffixArray mississippi) "i".toList = [10, 7, 4, 1]
#guard occurrences mississippi (suffixArray mississippi) "mississippi".toList = [0]
-- Absent patterns, including one longer than the text.
#guard occurrences banana (suffixArray banana) "nab".toList = []
#guard occurrences banana (suffixArray banana) "bananas".toList = []
#guard occurrences banana (suffixArray banana) "z".toList = []
-- The empty pattern occurs at every position `i < |w|`.
#guard search mississippi (suffixArray mississippi) [] = (0, 11)
#guard occurrences ([] : List Char) [] "a".toList = []

-- Cross-check against KMP: same positions, except that KMP also reports the empty-suffix
-- position `|w|` for the empty pattern.
#guard (["ana", "na", "a", "b", "banana", "x", ""].map String.toList).all fun p =>
  (occurrences banana (suffixArray banana) p).mergeSort (· ≤ ·) =
    (KMP.kmpMatchesList p banana).filter (· < banana.length)
#guard (["ssi", "issi", "i", "s", "pp", "mississippi", "sis", ""].map String.toList).all fun p =>
  (occurrences mississippi (suffixArray mississippi) p).mergeSort (· ≤ ·) =
    (KMP.kmpMatchesList p mississippi).filter (· < mississippi.length)

-- Non-vacuity: the correctness hypothesis is met by the reference construction.
example (w p : List Char) (i : ℕ) :
    i ∈ occurrences w (suffixArray w) p ↔ i < w.length ∧ p <+: w.drop i :=
  mem_occurrences (isSuffixArray_suffixArray w) p

private meta def evalRangeSearch (w : ℕ) (I : SearchInput) : Option (List ℕ × ℕ) :=
  let fuel := I.sa.length + I.pat.length + 10
  (rangeSearchCode.eval w fuel (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.SuffixArray.Reg.out), steps)

private meta def evalOccurrences (w : ℕ) (I : SearchInput) : Option (List ℕ × ℕ) :=
  let fuel := I.sa.length + I.pat.length + 10
  (occurrencesCode.eval w fuel (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Cslib.Algorithms.WordRAM.SuffixArray.Reg.out), steps)

-- Word-RAM `rangeSearchCode` and `occurrencesCode` on `banana` ("ana" = `[1, 14, 1]`) and
-- `mississippi` ("issi" = `[9, 19, 19, 9]`, "i" = `[9]`).
#guard match evalRangeSearch 5 ⟨bananaWords, bananaSA, [1, 14, 1]⟩ with
  | some (rng, steps) => rng == [1, 3] && steps ≤ (32 * 3 + 63) * (Nat.log 2 6 + 1) + 25
  | none => false

#guard match evalOccurrences 5 ⟨bananaWords, bananaSA, [1, 14, 1]⟩ with
  | some (occ, steps) =>
    occ == [3, 1] && steps ≤ (32 * 3 + 63) * (Nat.log 2 6 + 1) + 9 * 2 + 26
  | none => false

#guard match evalOccurrences 6 ⟨mississippiWords, mississippiSA, [9, 19, 19, 9]⟩ with
  | some (occ, steps) =>
    occ == [4, 1] && steps ≤ (32 * 4 + 63) * (Nat.log 2 11 + 1) + 9 * 2 + 26
  | none => false

#guard match evalOccurrences 6 ⟨mississippiWords, mississippiSA, [9]⟩ with
  | some (occ, steps) =>
    occ == [10, 7, 4, 1] && steps ≤ (32 * 1 + 63) * (Nat.log 2 11 + 1) + 9 * 4 + 26
  | none => false

-- Absent pattern ("nab" = `[14, 1, 2]`), overlong pattern, empty pattern, and empty text.
#guard match evalOccurrences 5 ⟨bananaWords, bananaSA, [14, 1, 2]⟩ with
  | some (occ, steps) => occ == [] && steps ≤ (32 * 3 + 63) * (Nat.log 2 6 + 1) + 26
  | none => false

#guard match evalOccurrences 5 ⟨bananaWords, bananaSA, [2, 1, 14, 1, 14, 1, 19]⟩ with
  | some (occ, steps) => occ == [] && steps ≤ (32 * 7 + 63) * (Nat.log 2 6 + 1) + 26
  | none => false

#guard match evalRangeSearch 5 ⟨bananaWords, bananaSA, []⟩ with
  | some (rng, steps) => rng == [0, 6] && steps ≤ 63 * (Nat.log 2 6 + 1) + 25
  | none => false

#guard match evalOccurrences 5 ⟨bananaWords, bananaSA, []⟩ with
  | some (occ, steps) => occ == bananaSA && steps ≤ 63 * (Nat.log 2 6 + 1) + 9 * 6 + 26
  | none => false

#guard match evalRangeSearch 3 ⟨[], [], [1]⟩ with
  | some (rng, steps) => rng == [0, 0] && steps ≤ (32 * 1 + 63) * 1 + 25
  | none => false

#guard match evalOccurrences 3 ⟨[], [], []⟩ with
  | some (occ, steps) => occ == [] && steps ≤ 63 * 1 + 26
  | none => false

-- Kernel-checked non-vacuity instantiations of `rangeSearchProgram_computesListInTime` and
-- `occurrencesProgram_computesListInTime` on empty-array and nonempty-match instances.
private theorem search_empty_eq : search ([] : List ℕ) [] [1] = (0, 0) :=
  Prod.ext (lowerBound_of_le _ (le_refl 0)) (lowerBound_of_le _ (le_refl 0))

private theorem search_banana_ana :
    search [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1] = (1, 3) := by
  have hsa : IsSuffixArray [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] := by decide
  obtain ⟨hlo_hi, hhi_le, hiff⟩ := search_spec hsa [1, 14, 1]
  have h0 : ¬([1, 14, 1] <+: ([2, 1, 14, 1, 14, 1] : List ℕ).drop 5) := by decide
  have h1 : [1, 14, 1] <+: ([2, 1, 14, 1, 14, 1] : List ℕ).drop 3 := by decide
  have h2 : [1, 14, 1] <+: ([2, 1, 14, 1, 14, 1] : List ℕ).drop 1 := by decide
  have h3 : ¬([1, 14, 1] <+: ([2, 1, 14, 1, 14, 1] : List ℕ).drop 0) := by decide
  have r0 := hiff 0 (by decide)
  have r1 := hiff 1 (by decide)
  have r2 := hiff 2 (by decide)
  have r3 := hiff 3 (by decide)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at r0 r1 r2 r3
  have e1 : ¬((search [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1]).1 ≤ 0 ∧
      0 < (search [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1]).2) :=
    fun h => h0 (r0.mpr h)
  have e2 := r1.mp h1
  have e3 := r2.mp h2
  have e4 : ¬((search [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1]).1 ≤ 3 ∧
      3 < (search [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1]).2) :=
    fun h => h3 (r3.mpr h)
  exact Prod.ext (by omega) (by omega)

example : ∃ n, ExecutesList 5 rangeSearchProgram
    (.init (SearchInput.encode ⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2], [1, 14, 1]⟩))
    [1, 3] n ∧ n ≤ (32 * 3 + 63) * (Nat.log 2 6 + 1) + 26 := by
  have h := rangeSearchProgram_computesListInTime
    ⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2], [1, 14, 1]⟩ 5 (by decide) (by decide)
  simpa only [List.length_cons, List.length_nil, search_banana_ana] using h

example : ∃ n, ExecutesList 5 occurrencesProgram
    (.init (SearchInput.encode ⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2], [1, 14, 1]⟩))
    [3, 1] n ∧ n ≤ (32 * 3 + 63) * (Nat.log 2 6 + 1) + 9 * 2 + 27 := by
  have h := occurrencesProgram_computesListInTime
    ⟨[2, 1, 14, 1, 14, 1], [5, 3, 1, 0, 4, 2], [1, 14, 1]⟩ 5 (by decide) (by decide)
  have hocc : occurrences [2, 1, 14, 1, 14, 1] [5, 3, 1, 0, 4, 2] [1, 14, 1] = [3, 1] := by
    simp only [occurrences, search_banana_ana]; rfl
  simpa only [List.length_cons, List.length_nil, hocc] using h

example : ∃ n, ExecutesList 3 rangeSearchProgram
    (.init (SearchInput.encode ⟨[], [], [1]⟩)) [0, 0] n ∧ n ≤ 95 * 1 + 26 := by
  have h := rangeSearchProgram_computesListInTime ⟨[], [], [1]⟩ 3 (by decide) (by decide)
  simpa only [List.length_cons, List.length_nil, Nat.log_zero_right, Nat.zero_add,
    search_empty_eq] using h

end Cslib.Algorithms.Lean.SuffixArray.Tests
