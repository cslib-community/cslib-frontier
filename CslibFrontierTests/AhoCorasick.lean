/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
import CslibFrontier.Algorithms.Lean.AhoCorasick.Search
import CslibFrontier.Algorithms.Lean.AhoCorasick.KMP
import CslibFrontier.Algorithms.WordRAM.AhoCorasick
meta import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
meta import CslibFrontier.Algorithms.Lean.AhoCorasick.Search
meta import CslibFrontier.Algorithms.Lean.KMP.Basic
meta import CslibFrontier.Algorithms.Lean.KMP.Search
meta import CslibFrontier.Algorithms.WordRAM.AhoCorasick
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Aho–Corasick String Matching Tests

Executable `#guard` checks and kernel-checked theorem instantiations for
`Cslib.Algorithms.Lean.AhoCorasick` (`Basic.lean`, `Search.lean`, and `KMP.lean`) and the
Word-RAM realization in `Cslib.Algorithms.WordRAM.AhoCorasick`.
-/

set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.AhoCorasick.Tests

open Cslib.Algorithms.Lean.AhoCorasick
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.AhoCorasick

set_option linter.hashCommand false

/-! ## `[AhoCorasick1975]`, Figures 1 and 2: keywords `he`, `she`, `his`, `hers` on `ushers` -/

private def kw : List (List Char) := ["he", "she", "his", "hers"].map String.toList
private def ushers : List Char := "ushers".toList

-- Figure 2: `she` and `he` end at position 4 and `hers` at position 6.
#guard search kw ushers = [(4, "she".toList), (4, "he".toList), (6, "hers".toList)]
#guard search kw ushers = occurrences kw ushers

-- Figure 1(b): the failure function on the states 1, …, 9.
#guard ["h", "he", "s", "sh", "she", "hi", "his", "her", "hers"].map
    (fun s => (build kw).fail s.toList) =
  ["", "", "", "h", "he", "", "s", "", "s"].map String.toList

-- Figure 1(c): the output function.
#guard (build kw).out "he".toList = ["he".toList]
#guard (build kw).out "she".toList = ["she".toList, "he".toList]
#guard (build kw).out "his".toList = ["his".toList]
#guard (build kw).out "hers".toList = ["hers".toList]
#guard (build kw).out "sh".toList = []

-- With the constructed output table, a failure table that always fails to the start state
-- misses `hers`.
#guard scan kw ⟨fun _ => [], (build kw).out⟩ ushers = [(4, "she".toList), (4, "he".toList)]

/-! ## Pure edge cases -/

-- Empty text, empty keyword list, and the empty keyword (never reported).
#guard search kw [] = []
#guard search ([] : List (List ℕ)) [1, 2, 3] = []
#guard search [[]] [1, 2] = []
#guard search [[], [1]] [1, 2, 1] = [(1, [1]), (3, [1])]

-- A keyword listed twice is reported once per end position.
#guard search [[1, 1], [1, 1], [2]] [1, 1, 1, 2] = [(2, [1, 1]), (3, [1, 1]), (4, [2])]

-- Keywords that are suffixes of other keywords, and overlapping occurrences.
private def aaa : List (List Char) := ["a", "aa", "aaa"].map String.toList

#guard search aaa "aaaa".toList =
  [(1, "a"), (2, "aa"), (2, "a"), (3, "aaa"), (3, "aa"), (3, "a"), (4, "aaa"), (4, "aa"),
    (4, "a")].map fun (i, y) => (i, y.toList)

/-! ## One keyword: the Knuth–Morris–Pratt special case -/

private def aba : List Char := "aba".toList
private def ababaca : List Char := "ababaca".toList

#guard search [aba] "babababab".toList = [(4, aba), (6, aba), (8, aba)]
#guard search [aba] "babababab".toList =
  (KMP.kmpMatchesList aba "babababab".toList).map fun s => (s + aba.length, aba)
-- `[CLRS2009]`, Figure 32.11(a): π[5] = 3 for `ababaca`.
#guard failure [ababaca] (ababaca.take 5) = ababaca.take (KMP.borderLen ababaca 5)
#guard failure [ababaca] (ababaca.take 5) = "aba".toList

/-! ## Word-RAM `Code.eval` execution checks -/

private meta def evalSearch (w : ℕ) (inp : Input) : Option (List ℕ × ℕ) :=
  match searchCode.eval w (searchTime inp) (.init inp.encode) with
  | some (y, steps) => some (outputList y.mem (y.regs Reg.out), steps)
  | none => none

private meta def checkSearch (w : ℕ) (inp : Input) : Bool :=
  match evalSearch w inp with
  | some (words, steps) =>
    words == encodeOccurrences (occurrences inp.patterns inp.text) &&
      decodeOccurrences inp.text words == occurrences inp.patterns inp.text &&
      steps ≤ searchTime inp - 1
  | none => false

-- Paper's `he`/`she`/`his`/`hers` on `ushers` over `{e=0, h=1, i=2, r=3, s=4, u=5}` (`σ = 6`).
private def ushersInp : Input :=
  ⟨6, [[1, 0], [4, 1, 0], [1, 2, 4], [1, 0, 3, 4]], [5, 4, 1, 0, 3, 4]⟩

#guard (evalSearch 16 ushersInp).map Prod.fst = some [4, 3, 4, 2, 6, 4]
#guard checkSearch 16 ushersInp
#guard checkSearch 64 ushersInp
-- Width invariance across fitting word widths (`w = 16` vs `w = 64`).
#guard evalSearch 16 ushersInp = evalSearch 64 ushersInp
-- Fault check when word width is too narrow (`w = 4`, `2^4 = 16 < ushersInp.wordBound`).
#guard (evalSearch 4 ushersInp).isNone

-- Unary alphabet (`σ = 1`) with overlapping suffix keywords `["a", "aa", "aaa"]` on `"aaaa"`.
private def unaryInp : Input :=
  ⟨1, [[0], [0, 0], [0, 0, 0]], [0, 0, 0, 0]⟩

#guard (evalSearch 16 unaryInp).map (fun p => p.1.length) = some 18
#guard checkSearch 16 unaryInp

-- Duplicate keywords and empty keyword (`σ = 3`).
private def dupEmptyInp : Input :=
  ⟨3, [[], [1, 1], [1, 1], [2]], [1, 1, 1, 2]⟩

#guard checkSearch 16 dupEmptyInp

-- Non-terminal prefix state reaching a match through a multi-hop non-terminal failure chain
-- (exercises the `isTerm[s] = 0`, `outHead[s] := outHead[fail[s]]` arm of `bfsInnerStepCode`):
-- state `[0, 1, 2, 3]` is non-terminal, fails to non-terminal `[1, 2, 3]`, which fails to
-- terminal keyword `[2, 3]`.
private def nonTermChainInp : Input :=
  ⟨6, [[0, 1, 2, 3, 4], [1, 2, 3, 5], [2, 3]], [0, 1, 2, 3]⟩

#guard (evalSearch 16 nonTermChainInp).map Prod.fst = some [4, 2]
#guard checkSearch 16 nonTermChainInp

-- Boundary cases: empty text, empty pattern list, and `σ = 0`.
#guard checkSearch 16 ⟨6, ushersInp.patterns, []⟩
#guard checkSearch 16 ⟨4, [], [1, 2, 3]⟩
#guard checkSearch 16 ⟨0, [[]], []⟩

/-! ## Non-vacuity checks -/

-- `IsOccurrence` holds for `hers` at position 6 and fails at position 5.
example : IsOccurrence kw ushers 6 "hers".toList ∧ ¬ IsOccurrence kw ushers 5 "hers".toList :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, fun h => absurd h.2.2.2 (by decide)⟩

/-- `[AhoCorasick1975]`, Figure 1(b): `f(5) = 2`, i.e. the failure state of `she` is `he`. -/
private theorem failure_she : failure kw "she".toList = "he".toList :=
  ((eq_failure_iff (by decide)).mpr ⟨by decide, by decide, by decide, fun x _ hlt _ => by
    have h3 : "she".toList.length = 3 := by decide
    have h2 : "he".toList.length = 2 := by decide
    omega⟩).symm

-- The constructed machine is valid; a machine whose failure table always returns the start state
-- is not.
example : (build kw).IsValid kw ∧ (build kw).fail "she".toList = "he".toList ∧
    ¬ Machine.IsValid kw ⟨fun _ => [], (build kw).out⟩ :=
  ⟨isValid_build kw, ((isValid_build kw) _ (by decide)).1.trans failure_she,
    fun h => absurd ((h "she".toList (by decide)).1.trans failure_she) (by decide)⟩

-- Universe-polymorphic instantiation (`Type 1` via `ULift.{1} ℕ`).
example (P : List (List (ULift.{1} ℕ))) (t : List (ULift.{1} ℕ)) :
    search P t = occurrences P t :=
  search_eq P t

-- Kernel-checked Word-RAM execution and lossless decoding on `ushersInp` at `w = 16`.
private theorem ushersInp_valid : ushersInp.Valid := by decide
private theorem ushersInp_fits : Fits 16 ushersInp.wordBound :=
  Fits.of_le (by decide) (wordBound_le ushersInp)

example :
    (∃ t, ExecutesList 16 searchProgram (.init ushersInp.encode)
        (encodeOccurrences (occurrences ushersInp.patterns ushersInp.text)) t ∧
      t ≤ searchTime ushersInp) ∧
    decodeOccurrences ushersInp.text
      (encodeOccurrences (occurrences ushersInp.patterns ushersInp.text)) =
      occurrences ushersInp.patterns ushersInp.text :=
  ⟨searchProgram_executesList ushersInp 16 ushersInp_valid ushersInp_fits,
    decodeOccurrences_encodeOccurrences ushersInp.patterns ushersInp.text⟩

example :
    ∃ t, ExecutesList 16 searchProgram (.init unaryInp.encode)
        (encodeOccurrences (occurrences unaryInp.patterns unaryInp.text)) t ∧
      t ≤ searchTime unaryInp :=
  searchProgram_executesList unaryInp 16 (by decide)
    (Fits.of_le (by decide) (wordBound_le unaryInp))

example :
    ∃ t, ExecutesList 16 searchProgram (.init nonTermChainInp.encode)
        (encodeOccurrences (occurrences nonTermChainInp.patterns nonTermChainInp.text)) t ∧
      t ≤ searchTime nonTermChainInp :=
  searchProgram_executesList nonTermChainInp 16 (by decide)
    (Fits.of_le (by decide) (wordBound_le nonTermChainInp))

end Cslib.Algorithms.Lean.AhoCorasick.Tests
