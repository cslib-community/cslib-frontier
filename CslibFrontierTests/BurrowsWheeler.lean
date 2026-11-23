/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Basic
import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Decode
import CslibFrontier.Algorithms.WordRAM.BurrowsWheeler
import Mathlib.Data.Char
meta import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Basic
meta import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Decode
meta import CslibFrontier.Algorithms.WordRAM.BurrowsWheeler
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
meta import Mathlib.Data.Char

/-!
# Burrows–Wheeler Transform Tests

Executable `#guard` checks and non-vacuity instantiations for
`Cslib.Algorithms.Lean.BurrowsWheeler` (`Basic.lean` and `Decode.lean`) and the linear-time
Word-RAM decoder `Cslib.Algorithms.WordRAM.BurrowsWheeler`.
-/

set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.BurrowsWheeler.Tests

open Cslib.Algorithms.Lean.BurrowsWheeler
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.BurrowsWheeler

set_option linter.hashCommand false

/-! ## The running example of [BurrowsWheeler1994], Section 2 -/

-- Algorithm C on `S = abraca`: `L = caraab`, `I = 1`.
#guard bwt "abraca".toList = ("caraab".toList, 1)
-- Step D1: `F = aaabcr`.
#guard bwtFirst "abraca".toList = "aaabcr".toList
-- Step D2: `T = (4 0 5 1 2 3)`.
#guard (List.range 6).map (lfMap "caraab".toList) = [4, 0, 5, 1, 2, 3]
-- Section 4.2: the rank array `P` for `L = caraab`.
#guard rankTable "caraab".toList = [0, 0, 0, 1, 2, 0]
#guard inverseBwt ("caraab".toList, 1) = "abraca".toList
#guard inverseBwtTable "caraab".toList 1 (fun c => "caraab".toList.countP (· < c))
    (rankTable "caraab".toList) = "abraca".toList

/-! ## Further examples -/

#guard bwt "banana".toList = ("nnbaaa".toList, 3)
#guard inverseBwt ("nnbaaa".toList, 3) = "banana".toList
-- A periodic word, `(can)^2` (the remark after step D3).
#guard bwt "cancan".toList = ("ccnnaa".toList, 2)
#guard inverseBwtTable "ccnnaa".toList 2 (fun c => "ccnnaa".toList.countP (· < c))
    (rankTable "ccnnaa".toList) = "cancan".toList
-- The LF orbit of `I = 2` for `cancan` repeats with period 3: `[2, 4, 0, 2, 4, 0]`.
#guard (List.range 6).map (fun i => (lfMap "ccnnaa".toList)^[i] 2) = [2, 4, 0, 2, 4, 0]

/-! ## Edge cases -/

#guard bwt ([] : List Char) = ([], 0)
#guard inverseBwt (([] : List Char), 0) = []
#guard bwt "x".toList = ("x".toList, 0)
#guard bwt "aaaa".toList = ("aaaa".toList, 0)
#guard inverseBwt ("aaaa".toList, 0) = "aaaa".toList
-- Without the index, the transform is not injective: `ab` and `ba` share `L`.
#guard bwtLast "ab".toList = bwtLast "ba".toList
#guard bwt "ab".toList ≠ bwt "ba".toList
-- Natural-number alphabets: rotations share `L` and are told apart by the index.
#guard bwt [3, 1, 2] = ([3, 1, 2], 2)
#guard bwt [2, 3, 1] = ([3, 1, 2], 1)
#guard inverseBwt ([3, 1, 2], 2) = [3, 1, 2]
#guard inverseBwt ([3, 1, 2], 1) = [2, 3, 1]

/-! ## Word-RAM execution and running-time checks -/

private meta def evalDecode (w : ℕ) (inp : Input) : Option (List ℕ × ℕ) :=
  (decodeCode.eval w (2 * inp.last.length + inp.alphabetSize + 4)
    (Data.init inp.encode)).map fun (y, steps) =>
      (outputList y.mem (y.regs Reg.out), steps)

-- "abraca" as `[0, 1, 3, 0, 2, 0]` over `σ = 4`: `bwt` is `([2, 0, 3, 0, 0, 1], 1)`.
-- At width 5 (`2^5 = 32 > 3 * 6 + 4 + 4 = 26`).
#guard match evalDecode 5 ⟨[2, 0, 3, 0, 0, 1], 1, 4⟩ with
  | some (dec, steps) => dec == [0, 1, 3, 0, 2, 0] && steps ≤ 25 * 6 + 11 * 4 + 33
  | none => false

-- Periodic word "cancan" as `[1, 0, 2, 1, 0, 2]` over `σ = 3`: `bwt` is `([1, 1, 2, 2, 0, 0], 2)`.
#guard match evalDecode 5 ⟨[1, 1, 2, 2, 0, 0], 2, 3⟩ with
  | some (dec, steps) => dec == [1, 0, 2, 1, 0, 2] && steps ≤ 25 * 6 + 11 * 3 + 33
  | none => false

-- Single-symbol alphabet `σ = 1` on a constant word `[0, 0, 0, 0]`.
#guard match evalDecode 5 ⟨[0, 0, 0, 0], 0, 1⟩ with
  | some (dec, steps) => dec == [0, 0, 0, 0] && steps ≤ 25 * 4 + 11 * 1 + 33
  | none => false

-- Out-of-range starting row stops early cleanly (`inverseBwt ([2, 0, 1], 9) = []`).
#guard match evalDecode 5 ⟨[2, 0, 1], 9, 3⟩ with
  | some (dec, steps) => dec == [] && steps ≤ 25 * 3 + 11 * 3 + 33
  | none => false

-- Empty word at minimal valid width `w = 3` (`3 * 0 + 0 + 4 = 4 < 8`).
#guard match evalDecode 3 ⟨[], 0, 0⟩ with
  | some (dec, steps) => dec == [] && steps ≤ 33
  | none => false

/-! ## Non-vacuity of the main theorems -/

example : inverseBwt (bwt [2, 7, 1, 8, 2, 8]) = [2, 7, 1, 8, 2, 8] := inverseBwt_bwt _

example : bwt [1, 2] ≠ bwt [2, 1] := fun h => by
  have := bwt_injective h
  simp at this

example :
    inverseBwtTable (bwtLast [3, 1, 4, 1, 5, 9, 2, 6]) (bwtIndex [3, 1, 4, 1, 5, 9, 2, 6])
      (fun c => (bwtLast [3, 1, 4, 1, 5, 9, 2, 6]).countP (· < c))
      (rankTable (bwtLast [3, 1, 4, 1, 5, 9, 2, 6])) = [3, 1, 4, 1, 5, 9, 2, 6] :=
  inverseBwtTable_bwt _ fun _ _ => rfl

example : bwtFirst [3, 1, 2] = (bwtLast [3, 1, 2]).mergeSort (· ≤ ·) :=
  bwtFirst_eq_mergeSort_bwtLast _

example :
    ((List.range (bwtMatrix "cancan".toList).length).map (lfMap (bwtLast "cancan".toList))).Perm
      (List.range (bwtMatrix "cancan".toList).length) :=
  map_lfMap_range_perm _

example : ∃ t, ExecutesList 6 decodeProgram
    (.init (Input.mk (bwtLast [3, 1, 4, 1, 5, 9, 2, 6])
      (bwtIndex [3, 1, 4, 1, 5, 9, 2, 6]) 10).encode)
    [3, 1, 4, 1, 5, 9, 2, 6] t ∧ t ≤ 25 * 8 + 11 * 10 + 34 :=
  decodeProgram_bwt [3, 1, 4, 1, 5, 9, 2, 6] 10 6 (by decide) (by decide)

end Cslib.Algorithms.Lean.BurrowsWheeler.Tests
