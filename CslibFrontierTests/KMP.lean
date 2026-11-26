/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.KMP.Basic
import CslibFrontier.Algorithms.Lean.KMP.Search
import CslibFrontier.Algorithms.WordRAM.KMP
meta import CslibFrontier.Algorithms.WordRAM.KMP
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Knuth–Morris–Pratt String Matching Tests

Executable checks and kernel-checked non-vacuity instantiations for the pure reference
implementation (`CslibFrontier.Algorithms.Lean.KMP.Basic` and
`CslibFrontier.Algorithms.Lean.KMP.Search`) and the linear-time Word-RAM implementation
(`CslibFrontier.Algorithms.WordRAM.KMP`), covering overlapping occurrences, adversarial fallback
chains, and empty-pattern / empty-text / minimal-width boundary cases.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace Cslib.Algorithms.Lean.KMP.Tests

open Cslib.Algorithms.Lean.KMP
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.KMP

/-! ## Border, period, and `[CLRS2009]` Figures 32.10–32.11 failure-table checks -/

private def clrsPat : Array Char := "ababaca".toList.toArray

-- `[CLRS2009]`, Figure 32.11(a): π for "ababaca" is [0, 0, 1, 2, 3, 0, 1]
-- (Figure 32.10(c) shows π[5] = 3).
#guard computePrefix clrsPat = #[0, 0, 1, 2, 3, 0, 1]

example : computePrefix #['a', 'b', 'a', 'b', 'a', 'c', 'a'] = #[0, 0, 1, 2, 3, 0, 1] := by
  rw [computePrefix_eq_ofFn]
  decide

-- `[CLRS2009]`, Lemma 32.5 & Figure 32.11: proper border chains via π* iteration.
#guard borderChain "ababaca".toList 5 = [3, 1, 0]
#guard borderChain "ababaca".toList 7 = [1, 0]
#guard borderChain "ababaca".toList 0 = []
#guard borderChain "ababababca".toList 8 = [6, 4, 2, 0]

-- Minimum period checks (`minPeriod w + maxBorderLen w = w.length`).
#guard maxBorderLen "ababab".toList = 4
#guard minPeriod "ababab".toList = 2
#guard maxBorderLen "ababaca".toList = 1
#guard minPeriod "ababaca".toList = 6

/-! ## Pure edge cases: empty pattern, empty text, singleton, and overlapping matches -/

-- Empty pattern matches at every position `0 .. t.size`.
#guard computePrefix (#[] : Array Nat) = #[]
#guard kmpMatches (#[] : Array Nat) #[10, 20, 30] = [0, 1, 2, 3]
#guard kmpMatches (#[] : Array Nat) (#[] : Array Nat) = [0]

-- Nonempty pattern against empty text or shorter text.
#guard kmpMatches #[1] (#[] : Array Nat) = []
#guard kmpMatches #[1, 2, 3, 4] #[1, 2] = []

-- Singleton pattern.
#guard computePrefix #[7] = #[0]
#guard kmpMatches #[7] #[7, 3, 7, 7] = [0, 2, 3]

-- Overlapping occurrences (`"aba"` in `"abababa"`, `"aa"` in `"aaaa"`).
#guard kmpMatches #[0, 1, 0] #[0, 1, 0, 1, 0, 1, 0] = [0, 2, 4]
#guard kmpMatches #[1, 1] #[1, 1, 1, 1] = [0, 1, 2]
#guard kmpMatchesList "aba".toList "babababab".toList = [1, 3, 5]

-- Adversarial fallback chain (`p = "aaaaab"`, `t = "aaaaaaaaaaab"`).
private def advPat : Array Char := "aaaaab".toList.toArray
private def advTxt : Array Char := "aaaaaaaaaaab".toList.toArray

#guard computePrefix advPat = #[0, 1, 2, 3, 4, 0]
#guard kmpMatches advPat advTxt = [6]

/-! ## Pure non-vacuity and universe-polymorphism checks -/

-- Concrete witness for `IsPrefixTableFor` and `IsDecreasingTable`.
example : IsPrefixTableFor advPat (computePrefix advPat) ∧
    IsDecreasingTable (computePrefix advPat) :=
  ⟨(isPrefixTableFor_computePrefix advPat).2, isDecreasingTable_computePrefix advPat⟩

-- Concrete witness for `IsMatchAt`, `mem_kmpMatches_iff`, and strict ordering.
example : IsMatchAt advPat advTxt 6 ∧
    6 ∈ kmpMatches advPat advTxt ∧
    (∀ s, s ∈ kmpMatches advPat advTxt ↔ IsMatchAt advPat advTxt s) ∧
    (kmpMatches advPat advTxt).Pairwise (· < ·) ∧
    (kmpMatches advPat advTxt).Nodup :=
  have hmatch : IsMatchAt advPat advTxt 6 := ⟨by decide, by decide⟩
  ⟨hmatch,
    (mem_kmpMatches_iff advPat advTxt 6).mpr hmatch,
    mem_kmpMatches_iff advPat advTxt,
    pairwise_lt_kmpMatches advPat advTxt,
    nodup_kmpMatches advPat advTxt⟩

-- Concrete witness for border-period duality, `minPeriod_le_of_isPeriod`, and `borderChain`.
example : IsPeriod "ababab".toList 2 ∧
    minPeriod "ababab".toList ≤ 4 ∧
    minPeriod "ababab".toList ≤ 10 ∧
    (3 ∈ borderChain "ababaca".toList 5 ↔
      IsProperBorderLen ("ababaca".toList.take 5) 3) :=
  have hper4 : IsPeriod "ababab".toList 4 :=
    ((isProperBorderLen_iff_isPeriod (w := "ababab".toList) (k := 2)).mp ⟨by decide, by decide⟩).2
  have hper10 : IsPeriod "ababab".toList 10 :=
    fun _ h => absurd (Nat.lt_of_add_left_lt h) (by decide)
  ⟨isPeriod_minPeriod (w := "ababab".toList) (by decide),
    minPeriod_le_of_isPeriod (by decide) hper4,
    minPeriod_le_of_isPeriod (by decide) hper10,
    mem_borderChain_iff (p := "ababaca".toList) (q := 5) (j := 3) (by decide) (by decide)⟩

-- Universe-polymorphic instantiation (`Type 1` via `ULift.{1} Nat`).
example (p t : Array (ULift.{1} Nat)) :
    (∀ s, s ∈ kmpMatches p t ↔ IsMatchAt p t s) ∧
      (kmpMatches p t).Pairwise (· < ·) :=
  ⟨mem_kmpMatches_iff p t, pairwise_lt_kmpMatches p t⟩

/-! ## Word-RAM execution and linear running-time checks -/

private meta def evalPrefix (w : ℕ) (p : List ℕ) : Option (List ℕ × ℕ) :=
  (prefixCode.eval w (2 * p.length + 5) (Data.init p)).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.out), steps)

private meta def evalSearch (w : ℕ) (I : SearchInput) : Option (List ℕ × ℕ) :=
  let fuel := 2 * (I.pat.length + I.txt.length) + 10
  (searchCode.eval w fuel (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.out), steps)

-- CLRS Figure 32.11(a) "ababaca" = [1, 2, 1, 2, 1, 3, 1] at minimal width 4 (2*7+1 = 15 < 16).
#guard match evalPrefix 4 [1, 2, 1, 2, 1, 3, 1] with
  | some (pi, steps) => pi == [0, 0, 1, 2, 3, 0, 1] && steps ≤ 31 * 7 + 9
  | none => false

-- Adversarial fallback chain: pat = "aaaaab", txt = "aaaaaaaaaaab" at width 6 (40 < 64).
#guard match evalSearch 6 ⟨[1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]⟩ with
  | some (ms, steps) => ms == [6] && steps ≤ 31 * 6 + 37 * 12 + 22
  | none => false

-- Overlapping occurrences: "aba" in "abababa" and "aa" in "aaaa".
#guard match evalSearch 5 ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩ with
  | some (ms, steps) => ms == [0, 2, 4] && steps ≤ 31 * 3 + 37 * 7 + 22
  | none => false

#guard match evalSearch 5 ⟨[1, 1], [1, 1, 1, 1]⟩ with
  | some (ms, steps) => ms == [0, 1, 2] && steps ≤ 31 * 2 + 37 * 4 + 22
  | none => false

-- Boundary cases: empty pattern, empty text, both empty, and pattern longer than text,
-- tested at minimal admissible word widths.
#guard match evalPrefix 1 [] with
  | some (pi, steps) => pi == [] && steps ≤ 9
  | none => false

#guard match evalSearch 5 ⟨[], [10, 20, 30]⟩ with
  | some (ms, steps) => ms == [0, 1, 2, 3] && steps ≤ 37 * 3 + 22
  | none => false

#guard match evalSearch 3 ⟨[], []⟩ with
  | some (ms, steps) => ms == [0] && steps ≤ 22
  | none => false

#guard match evalSearch 3 ⟨[5], []⟩ with
  | some (ms, steps) => ms == [] && steps ≤ 31 * 1 + 22
  | none => false

#guard match evalSearch 5 ⟨[1, 2, 3, 4], [1, 2]⟩ with
  | some (ms, steps) => ms == [] && steps ≤ 31 * 4 + 37 * 2 + 22
  | none => false

-- Kernel-checked non-vacuity instantiations of `prefixProgram_computesListInTime` and
-- `searchProgram_computesListInTime` (exercised as an ordinary `module` client).
example : ∃ n, ExecutesList 4 prefixProgram (.init [1, 2, 1, 2, 1, 3, 1])
    [0, 0, 1, 2, 3, 0, 1] n ∧ n ≤ 31 * 7 + 10 := by
  have h := prefixProgram_computesListInTime [1, 2, 1, 2, 1, 3, 1] 4 (by decide) (by decide)
  have heq : (computePrefix #[1, 2, 1, 2, 1, 3, 1]).toList = [0, 0, 1, 2, 3, 0, 1] := by
    rw [computePrefix_eq_ofFn]; decide
  simpa only [List.length_cons, List.length_nil, heq] using h

example : ∃ n, ExecutesList 1 prefixProgram (.init []) [] n ∧ n ≤ 10 := by
  have h := prefixProgram_computesListInTime [] 1 (by decide) (by decide)
  have heq : (computePrefix (#[] : Array ℕ)).toList = [] := by
    rw [computePrefix_eq_ofFn]; decide
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, heq] using h

example : ∃ n, ExecutesList 5 searchProgram
    (.init (SearchInput.encode ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩))
    [0, 2, 4] n ∧ n ≤ 31 * 3 + 37 * 7 + 23 := by
  have h := searchProgram_computesListInTime ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩ 5
    (by decide) (by decide)
  have heq : kmpMatchesList [1, 2, 1] [1, 2, 1, 2, 1, 2, 1] = [0, 2, 4] := by
    rw [kmpMatchesList_eq_filter_range]; decide
  simpa only [List.length_cons, List.length_nil, heq] using h

example : ∃ n, ExecutesList 5 searchProgram
    (.init (SearchInput.encode ⟨[], [10, 20, 30]⟩)) [0, 1, 2, 3] n ∧ n ≤ 37 * 3 + 23 := by
  have h := searchProgram_computesListInTime ⟨[], [10, 20, 30]⟩ 5 (by decide) (by decide)
  have heq : kmpMatchesList ([] : List ℕ) [10, 20, 30] = [0, 1, 2, 3] := by
    rw [kmpMatchesList_eq_filter_range]; decide
  simpa only [List.length_cons, List.length_nil, Nat.mul_zero, Nat.zero_add, heq] using h

example : ∃ n, ExecutesList 3 searchProgram
    (.init (SearchInput.encode ⟨[], []⟩)) [0] n ∧ n ≤ 23 := by
  have h := searchProgram_computesListInTime ⟨[], []⟩ 3 (by decide) (by decide)
  have heq : kmpMatchesList ([] : List ℕ) [] = [0] := by
    rw [kmpMatchesList_eq_filter_range]; decide
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, heq] using h

example : ∃ n, ExecutesList 3 searchProgram
    (.init (SearchInput.encode ⟨[5], []⟩)) [] n ∧ n ≤ 31 * 1 + 23 := by
  have h := searchProgram_computesListInTime ⟨[5], []⟩ 3 (by decide) (by decide)
  have heq : kmpMatchesList [5] ([] : List ℕ) = [] := by
    rw [kmpMatchesList_eq_filter_range]; decide
  simpa only [List.length_cons, List.length_nil, Nat.mul_zero, Nat.add_zero, heq] using h

end Cslib.Algorithms.Lean.KMP.Tests
