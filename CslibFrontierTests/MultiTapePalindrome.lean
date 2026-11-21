/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Palindrome
import CslibFrontier.Computability.Machines.Turing.MultiTape.ToSingleTape.Correct

/-!
# Tests for the linear-time multi-tape palindrome decider

The decider accepts a palindrome, rejects a non-palindrome whose first mismatch is in the middle,
and accepts the empty word, each within `3n + 3` steps. Run through the single-tape simulation,
it decides palindromes on one tape in quadratic time, which the quadratic lower bound shows to be
optimal up to the constant.
-/

namespace CslibFrontierTests.MultiTapePalindrome

open Turing Turing.MultiTapeTM

example : (palindromeDecider.runFrom (palindromeDecider.initCfg [true, false, true]) 12).output =
    [true] :=
  (runFrom_palindromeDecider [true, false, true]).2.trans (by decide)

example :
    (palindromeDecider.runFrom (palindromeDecider.initCfg [true, true, false, true]) 15).output =
      [false] :=
  (runFrom_palindromeDecider [true, true, false, true]).2.trans (by decide)

example : (palindromeDecider.runFrom (palindromeDecider.initCfg []) 3).Halted ∧
    (palindromeDecider.runFrom (palindromeDecider.initCfg []) 3).output = [true] :=
  ⟨(runFrom_palindromeDecider []).1, (runFrom_palindromeDecider []).2.trans (by decide)⟩

/-- The single-tape simulation of the decider outputs `[true]` on `[true, false, true]`, within the
quadratic bound. -/
example : palindromeDecider.toSingleTape.OutputsWithinTime ([true, false, true].map .inl)
    ([true].map .inl) (4 * (2 * 1 + 10) ^ 2 * (12 + 1) * (3 + 12 + 1)) := by
  have h := palindromeDecider.outputsWithinTime_toSingleTape (runFrom_palindromeDecider
    [true, false, true]).1
  rwa [(runFrom_palindromeDecider [true, false, true]).2.trans
    (show [decide [true, false, true].Palindrome] = [true] by decide)] at h

/-- The single-tape simulation decides every palindrome instance in time quadratic in its length.
-/
example (x : List Bool) : palindromeDecider.toSingleTape.OutputsWithinTime (x.map .inl)
    ([decide x.Palindrome].map .inl)
    (4 * (2 * 1 + 10) ^ 2 * (3 * x.length + 3 + 1) * (x.length + (3 * x.length + 3) + 1)) :=
  (runFrom_palindromeDecider x).2 ▸
    palindromeDecider.outputsWithinTime_toSingleTape (runFrom_palindromeDecider x).1

end CslibFrontierTests.MultiTapePalindrome
