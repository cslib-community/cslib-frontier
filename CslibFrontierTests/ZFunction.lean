/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Foundations.Data.Array.CommonPrefix
import CslibFrontier.Algorithms.Lean.KMP.Search
import CslibFrontier.Algorithms.Lean.ZFunction.Basic
import CslibFrontier.Algorithms.Lean.ZFunction.Search
import CslibFrontier.Algorithms.WordRAM.ZFunction
meta import CslibFrontier.Algorithms.WordRAM.ZFunction
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
import Mathlib.Data.Char

/-!
# Z-algorithm tests

Executable `#guard` checks and kernel-checked non-vacuity instances for the pure Z-algorithm
(`CslibFrontier.Algorithms.Lean.ZFunction.Basic` and `Search`) and the linear-time Word-RAM
Z-algorithm (`CslibFrontier.Algorithms.WordRAM.ZFunction`), covering Gusfield's running example,
adversarial fallback inputs, overlapping occurrences, and empty / singleton / minimal-width
boundary cases.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace Cslib.Algorithms.Lean.ZFunction.Tests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.ZFunction
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ZFunction

private def aabxaab : List Char := "aabxaab".toList
private def gusfield : List Char := "aabcaabxaaz".toList

/-! ## Resuming a common-prefix scan -/

-- The last two entries match the first two, and the right suffix ends.
#guard #[1, 2, 1, 2].extendLcp 0 2 1 = 2
-- A supplied offset skips the first pair even when its entries differ.
#guard #[0, 5, 7, 1, 5, 8].extendLcp 0 3 1 = 2
#guard (#[] : Array Nat).extendLcp 0 0 3 = 3

/-! ## Pure Z-function and Z-algorithm checks -/

-- `aabxaab`: the suffix `aab` at position 4 repeats the prefix `aab`.
#guard zFunction aabxaab = [7, 1, 0, 0, 3, 1, 0]
#guard zAlgorithm aabxaab = zFunction aabxaab
#guard zFunction gusfield = [11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0]
#guard zAlgorithm gusfield = zFunction gusfield
#guard zAlgorithm "abacaba".toList = [7, 0, 1, 0, 3, 0, 1]
#guard zAlgorithm "abababab".toList = [8, 0, 6, 0, 4, 0, 2, 0]
-- Edge cases: the empty word, one letter, a constant word, and `a ^ (n - 1) b`.
#guard zAlgorithm ([] : List Char) = []
#guard zAlgorithm "a".toList = [1]
#guard zAlgorithm "aaaa".toList = [4, 3, 2, 1]
#guard zAlgorithm "aaaaaaaaab".toList = [10, 8, 7, 6, 5, 4, 3, 2, 1, 0]

-- Kernel-checked instance of `zFunction` via `List.le_lcpLen_iff` / `getElem_zFunction_zero`.
private theorem lcpLen_zero_zero_one_one : List.lcpLen [0, 0, 1] [0, 1] = 1 := by
  have hge : 1 ≤ List.lcpLen [0, 0, 1] [0, 1] := List.le_lcpLen_iff.mpr ⟨by decide, by decide, rfl⟩
  have hlt : ¬(2 ≤ List.lcpLen [0, 0, 1] [0, 1]) := by
    rw [List.le_lcpLen_iff]; decide
  omega

private theorem lcpLen_zero_zero_one_two : List.lcpLen [0, 0, 1] [1] = 0 := by
  have hlt : ¬(1 ≤ List.lcpLen [0, 0, 1] [1]) := by
    rw [List.le_lcpLen_iff]; decide
  omega

private theorem zFunction_zero_zero_one : zFunction [0, 0, 1] = [3, 1, 0] := by
  apply List.ext_getElem (by simp only [length_zFunction, List.length_cons, List.length_nil])
  intro i h1 _
  rw [getElem_zFunction]
  simp only [length_zFunction, List.length_cons, List.length_nil] at h1
  match i with
  | 0 => simp only [List.drop_zero, List.lcpLen_self]; rfl
  | 1 => exact lcpLen_zero_zero_one_one
  | 2 => exact lcpLen_zero_zero_one_two
  | _ + 3 => omega

example : zAlgorithm [0, 0, 1] = [3, 1, 0] :=
  (zAlgorithm_eq_zFunction [0, 0, 1]).trans zFunction_zero_zero_one

/-! ## Pure pattern matching -/

#guard zMatches "aab".toList aabxaab = [0, 4]
#guard zMatches "aab".toList aabxaab = KMP.kmpMatchesList "aab".toList aabxaab
#guard zMatches "aba".toList "abababa".toList = [0, 2, 4]
#guard zMatches "aba".toList "abababa".toList = KMP.kmpMatchesList "aba".toList "abababa".toList
-- The pattern overlaps itself and runs into the text: values above `|p|` are allowed.
#guard zMatches "aa".toList "aaaa".toList = [0, 1, 2]
-- No occurrence; a pattern longer than the text.
#guard zMatches "xyz".toList aabxaab = []
#guard zMatches "aabxaabx".toList aabxaab = []
-- The empty pattern occurs at every shift `0, …, |t|`, as in KMP.
#guard zMatches ([] : List Char) "abc".toList = [0, 1, 2, 3]
#guard zMatches ([] : List Char) "abc".toList = KMP.kmpMatchesList [] "abc".toList
#guard zMatches "a".toList ([] : List Char) = []

-- Correctness and agreement with KMP are theorems for every input.
example (p t : List Char) : zMatches p t = KMP.kmpMatchesList p t :=
  zMatches_eq_kmpMatchesList p t

/-! ## Longest common prefix -/

#guard List.lcpLen "abcd".toList "abxd".toList = 2
#guard List.lcpLen "abc".toList "abc".toList = 3
#guard List.lcpLen ([] : List Char) "abc".toList = 0

/-! ## Word-RAM execution and linear running-time checks -/

private meta def evalZ (w : ℕ) (s : List ℕ) : Option (List ℕ × ℕ) :=
  (zCode.eval w (2 * s.length + 5) (Data.init s)).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.out), steps)

private meta def evalMatch (w : ℕ) (I : MatchInput) : Option (List ℕ × ℕ) :=
  let fuel := 3 * (I.pat.length + I.txt.length) + 10
  (matchCode.eval w fuel (Data.init I.encode)).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.out), steps)

-- Gusfield "aabcaabxaaz" = [1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5] at minimal width 5 (23 < 32).
#guard match evalZ 5 [1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5] with
  | some (zs, steps) => zs == [11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0] && steps ≤ 39 * 11 + 9
  | none => false

-- Worst-case `a ^ (n - 1) b` (`n = 10`) and constant word `a ^ 8`.
#guard match evalZ 5 [1, 1, 1, 1, 1, 1, 1, 1, 1, 2] with
  | some (zs, steps) => zs == [10, 8, 7, 6, 5, 4, 3, 2, 1, 0] && steps ≤ 39 * 10 + 9
  | none => false

#guard match evalZ 5 [1, 1, 1, 1, 1, 1, 1, 1] with
  | some (zs, steps) => zs == [8, 7, 6, 5, 4, 3, 2, 1] && steps ≤ 39 * 8 + 9
  | none => false

-- Boundary cases for `zCode`: empty word (width 1) and singleton word (width 2).
#guard match evalZ 1 [] with
  | some (zs, steps) => zs == [] && steps ≤ 9
  | none => false

#guard match evalZ 2 [1] with
  | some (zs, steps) => zs == [1] && steps ≤ 39 * 1 + 9
  | none => false

-- Overlapping pattern matches and non-matches via `matchCode`.
#guard match evalMatch 5 ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩ with
  | some (ms, steps) => ms == [0, 2, 4] && steps ≤ 39 * 3 + 50 * 7 + 22
  | none => false

#guard match evalMatch 5 ⟨[1, 1], [1, 1, 1, 1]⟩ with
  | some (ms, steps) => ms == [0, 1, 2] && steps ≤ 39 * 2 + 50 * 4 + 22
  | none => false

-- Boundary cases for `matchCode`: empty pattern, empty text, both empty, and overlong pattern.
#guard match evalMatch 5 ⟨[], [10, 20, 30]⟩ with
  | some (ms, steps) => ms == [0, 1, 2, 3] && steps ≤ 50 * 3 + 22
  | none => false

#guard match evalMatch 3 ⟨[], []⟩ with
  | some (ms, steps) => ms == [0] && steps ≤ 22
  | none => false

#guard match evalMatch 3 ⟨[5], []⟩ with
  | some (ms, steps) => ms == [] && steps ≤ 39 * 1 + 22
  | none => false

#guard match evalMatch 5 ⟨[1, 2, 3, 4], [1, 2]⟩ with
  | some (ms, steps) => ms == [] && steps ≤ 39 * 4 + 50 * 2 + 22
  | none => false

-- Kernel-checked non-vacuity instantiations of `zProgram_computesListInTime` and
-- `matchProgram_computesListInTime`.
example : ∃ n, ExecutesList 3 zProgram (.init [0, 0, 1]) [3, 1, 0] n ∧ n ≤ 39 * 3 + 10 := by
  have h := zProgram_computesListInTime [0, 0, 1] 3 (by decide) (by decide)
  simpa only [List.length_cons, List.length_nil, zFunction_zero_zero_one] using h

example : ∃ n, ExecutesList 1 zProgram (.init []) [] n ∧ n ≤ 10 := by
  have h := zProgram_computesListInTime [] 1 (by decide) (by decide)
  have heq : zFunction ([] : List ℕ) = [] := rfl
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, heq] using h

example : ∃ n, ExecutesList 5 matchProgram
    (.init (MatchInput.encode ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩))
    [0, 2, 4] n ∧ n ≤ 39 * 3 + 50 * 7 + 23 := by
  have h := matchProgram_computesListInTime ⟨[1, 2, 1], [1, 2, 1, 2, 1, 2, 1]⟩ 5
    (by decide) (by decide)
  have heq : zMatches [1, 2, 1] [1, 2, 1, 2, 1, 2, 1] = [0, 2, 4] := by
    rw [zMatches_eq_filter_range]; decide
  simpa only [List.length_cons, List.length_nil, heq] using h

example : ∃ n, ExecutesList 3 matchProgram
    (.init (MatchInput.encode ⟨[], []⟩)) [0] n ∧ n ≤ 23 := by
  have h := matchProgram_computesListInTime ⟨[], []⟩ 3 (by decide) (by decide)
  have heq : zMatches ([] : List ℕ) [] = [0] := by
    rw [zMatches_eq_filter_range]; decide
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, heq] using h

example : ∃ n, ExecutesList 3 matchProgram
    (.init (MatchInput.encode ⟨[5], []⟩)) [] n ∧ n ≤ 39 * 1 + 23 := by
  have h := matchProgram_computesListInTime ⟨[5], []⟩ 3 (by decide) (by decide)
  have heq : zMatches [5] ([] : List ℕ) = [] := by
    rw [zMatches_eq_filter_range]; decide
  simpa only [List.length_cons, List.length_nil, Nat.mul_zero, Nat.add_zero, heq] using h

end Cslib.Algorithms.Lean.ZFunction.Tests
