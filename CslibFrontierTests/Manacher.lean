/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.Palindrome.Basic
import CslibFrontier.Algorithms.Lean.Palindrome.Manacher
import CslibFrontier.Algorithms.WordRAM.Manacher
meta import CslibFrontier.Algorithms.Lean.Palindrome.Manacher
meta import CslibFrontier.Algorithms.WordRAM.Manacher
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Manacher's Algorithm Tests

Kernel-checked (`decide`) and executable (`#guard`) instances for the maximal palindromic radii
`Cslib.Algorithms.Lean.Palindrome.radius`, the pure reference implementation
`CslibFrontier.Algorithms.Lean.Palindrome.Manacher`, and the linear-time Word-RAM implementation
`CslibFrontier.Algorithms.WordRAM.Manacher`, including module-encapsulated client checks,
boundary-width runs, and non-vacuity instantiations.
-/

set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.Palindrome.Tests

open Cslib.Algorithms.Lean.Palindrome
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Manacher

set_option linter.hashCommand false

/-! ## Radii at all centers, checked by the kernel through `manacher_eq` -/

-- "abacaba": the whole word is the palindrome of radius 3 about its middle letter (center 7).
example : manacher #['a', 'b', 'a', 'c', 'a', 'b', 'a'] =
    #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- "abba": an even palindrome of radius 2 about the middle gap (center 4).
example : manacher #['a', 'b', 'b', 'a'] = #[0, 0, 0, 0, 2, 0, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- All-equal letters: every center's palindrome reaches the nearer end of the word.
example : manacher #['a', 'a', 'a', 'a'] = #[0, 0, 1, 1, 2, 1, 1, 0, 0] := by
  rw [manacher_eq]; decide

-- No palindromic factor longer than one letter: every radius is `0`.
example : manacher #['a', 'b', 'c', 'd'] = #[0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [manacher_eq]; decide

-- Empty and one-letter words.
example : manacher (#[] : Array Char) = #[0] := by
  rw [manacher_eq]; decide

example : manacher #['a'] = #[0, 0, 0] := by
  rw [manacher_eq]; decide

-- Centers beyond `2 * w.length` have radius `0`.
example : radius ['a', 'a'] 5 = 0 := by decide

/-! ## Executable checks on pure `manacher`, `extend`, and `longestPalindromeSpan` -/

#guard manacher "abacaba".toList.toArray = #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]
#guard manacher "abaxabaxabb".toList.toArray =
  #[0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]
#guard manacher "aaaaaaaa".toList.toArray = #[0, 0, 1, 1, 2, 2, 3, 3, 4, 3, 3, 2, 2, 1, 1, 0, 0]

-- One extension phase about the middle of "abacaba", from radius `0`: three successful
-- extensions, stopping at the ends of the word.
#guard extend "abacaba".toList.toArray 3 4 = 3
#guard extend "abcd".toList.toArray 1 2 = 0

/-! ## Longest palindromic factor and palindromic prefixes -/

example : longestPalindrome ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] =
    ['a', 'b', 'a', 'c', 'a', 'b', 'a'] := by
  decide

#guard longestPalindromeSpan "xabacabay".toList.toArray = ⟨1, 8⟩
#guard longestPalindromeSpan "abcd".toList.toArray = ⟨0, 1⟩

-- `extract_longestPalindromeSpan` on a concrete word.
example : ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'].extract
      (longestPalindromeSpan #['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).start
      (longestPalindromeSpan #['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).stop =
    ['a', 'b', 'a', 'c', 'a', 'b', 'a'] := by
  rw [show ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] =
    (#['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y'] : Array Char).toList from rfl,
    extract_longestPalindromeSpan]
  decide

-- Non-vacuity of `length_le_longestPalindrome`: the palindromic factor "aca" of "xabacabay"
-- bounds the longest palindrome's length below by `3`.
example : 3 ≤ (longestPalindrome ['x', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'y']).length :=
  length_le_longestPalindrome (u := ['a', 'c', 'a'])
    ⟨['x', 'a', 'b'], ['b', 'a', 'y'], rfl⟩ (List.Palindrome.of_reverse_eq rfl)

-- `palindrome_extract_iff_le_radius` on "abacaba": the factor `[1, 6)` = "bacab" has center `7`.
example : (['a', 'b', 'a', 'c', 'a', 'b', 'a'].extract 1 6).Palindrome :=
  (palindrome_extract_iff_le_radius (by omega) (by decide)).mpr (by decide)

-- `palindrome_take_iff`: "aba" is a palindromic prefix of "abacaba", "ab" is not.
example : (['a', 'b', 'a', 'c', 'a', 'b', 'a'].take 3).Palindrome :=
  (palindrome_take_iff (by decide)).mpr (by decide)

example : ¬ (['a', 'b', 'a', 'c', 'a', 'b', 'a'].take 2).Palindrome := by
  rw [palindrome_take_iff (by decide)]
  decide

/-! ## Distinct palindromic factors -/

example : ([] : List Char).palindromicFactors = {[]} := by decide

-- Repeated occurrences of the same word count once; this word reaches the bound.
example : ['a', 'a', 'a'].palindromicFactors = {[], ['a'], ['a', 'a'], ['a', 'a', 'a']} := by
  decide

-- The final `a` has occurred before and introduces no new palindrome.
example : ['a', 'b', 'c', 'a'].palindromicFactors.card = 4 := by decide

/-! ## Word-RAM execution and linear running-time checks -/

private meta def evalRadii (w : ℕ) (xs : List ℕ) : Option (List ℕ × ℕ) :=
  (radiiCode.eval w (2 * xs.length + 2) (Data.init xs)).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.out), steps)

private meta def evalLongest (w : ℕ) (xs : List ℕ) : Option (Span × List ℕ × ℕ) :=
  (longestCode.eval w (2 * xs.length + 2) (Data.init xs)).map fun (y, steps) =>
    (⟨y.regs Reg.regl, y.regs Reg.regr⟩, outputList y.mem (y.regs Reg.out), steps)

-- "abacaba" = [1, 2, 1, 3, 1, 2, 1] at width 6 (2^6 = 64 > 4 * 7 + 4 = 32).
#guard match evalRadii 6 [1, 2, 1, 3, 1, 2, 1] with
  | some (rads, steps) =>
    rads == [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] && steps ≤ 87 * 7 + 15
  | none => false

#guard match evalLongest 6 [4, 1, 2, 1, 3, 1, 2, 1, 5] with
  | some (sp, pal, steps) =>
    sp == ⟨1, 8⟩ && pal == [1, 2, 1, 3, 1, 2, 1] && steps ≤ 116 * 9 + 36
  | none => false

-- Even-length palindrome "abba" = [1, 2, 2, 1].
#guard match evalLongest 6 [1, 2, 2, 1] with
  | some (sp, pal, steps) =>
    sp == ⟨0, 4⟩ && pal == [1, 2, 2, 1] && steps ≤ 116 * 4 + 36
  | none => false

-- All-equal letters [1, 1, 1, 1].
#guard match evalRadii 5 [1, 1, 1, 1] with
  | some (rads, steps) =>
    rads == [0, 0, 1, 1, 2, 1, 1, 0, 0] && steps ≤ 87 * 4 + 15
  | none => false

#guard match evalLongest 5 [1, 1, 1, 1] with
  | some (sp, pal, steps) =>
    sp == ⟨0, 4⟩ && pal == [1, 1, 1, 1] && steps ≤ 116 * 4 + 36
  | none => false

-- Distinct letters [1, 2, 3, 4]: tie-breaking selects first letter span ⟨0, 1⟩.
#guard match evalLongest 6 [1, 2, 3, 4] with
  | some (sp, pal, steps) =>
    sp == ⟨0, 1⟩ && pal == [1] && steps ≤ 116 * 4 + 36
  | none => false

-- Single-letter word [7] at width 4 (2^4 = 16 > 4 * 1 + 4 = 8).
#guard match evalRadii 4 [7] with
  | some (rads, steps) => rads == [0, 0, 0] && steps ≤ 87 + 15
  | none => false

#guard match evalLongest 4 [7] with
  | some (sp, pal, steps) => sp == ⟨0, 1⟩ && pal == [7] && steps ≤ 116 + 36
  | none => false

-- Empty word at minimal valid widths: w = 2 for `radiiCode` (3*0+2 = 2 < 4)
-- and w = 3 for `longestCode` (4*0+4 = 4 < 8).
#guard match evalRadii 2 [] with
  | some (rads, steps) => rads == [0] && steps ≤ 15
  | none => false

#guard match evalLongest 3 [] with
  | some (sp, pal, steps) => sp == ⟨0, 0⟩ && pal == [] && steps ≤ 36
  | none => false

-- Non-vacuity instantiations of `radiiProgram_computesListInTime` and
-- `longestProgram_computesListInTime`.
example : ∃ n, ExecutesList 6 radiiProgram (.init [1, 2, 1, 3, 1, 2, 1])
    [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] n ∧ n ≤ 87 * 7 + 16 := by
  have h := radiiProgram_computesListInTime [1, 2, 1, 3, 1, 2, 1] 6 (by decide) (by decide)
  have heq : (manacher #[1, 2, 1, 3, 1, 2, 1]).toList =
      [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] := by
    rw [manacher_eq]; decide
  simpa only [List.length_cons, List.length_nil, heq] using h

example : ∃ n, ExecutesList 6 longestProgram (.init [4, 1, 2, 1, 3, 1, 2, 1, 5])
    [1, 2, 1, 3, 1, 2, 1] n ∧ n ≤ 116 * 9 + 37 := by
  have h := longestProgram_computesListInTime [4, 1, 2, 1, 3, 1, 2, 1, 5] 6 (by decide) (by decide)
  have heq : longestPalindrome [4, 1, 2, 1, 3, 1, 2, 1, 5] = [1, 2, 1, 3, 1, 2, 1] := by decide
  simpa only [List.length_cons, List.length_nil, heq] using h

end Cslib.Algorithms.Lean.Palindrome.Tests
