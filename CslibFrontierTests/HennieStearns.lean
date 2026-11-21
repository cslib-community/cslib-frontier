/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Correct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Palindrome

/-!
# Tests for the Hennie–Stearns simulation

The levels of three moves of a blank track sum to `2 ^ 0 + 2 ^ 1 + 2 ^ 0`. Run through the
Hennie–Stearns machine, the linear-time palindrome decider decides palindromes on two work tapes
in time `O(n log n)`.
-/

namespace CslibFrontierTests.HennieStearns

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.HennieStearns

/-- Two moves to the right reach levels `0` and `1`, and a move back to the left level `0`. -/
example : (blankTrack (Symbol := Bool)).cost 0 [.R, .R, .L] = 4 := by decide

/-- The two-tape simulation of the decider outputs `[true]` on `[true, false, true]`, within the
`O(t log t)` bound. -/
example : ∃ T ≤ (80 * 1 + 2) * (12 + 1) * (Nat.log 2 (12 + 1) + 1),
    ((hennieStearns palindromeDecider).runFrom
      ((hennieStearns palindromeDecider).initCfg ([true, false, true].map .inl)) T).Halted ∧
    ((hennieStearns palindromeDecider).runFrom
      ((hennieStearns palindromeDecider).initCfg ([true, false, true].map .inl)) T).output =
      [true].map .inl := by
  have h := hennieStearns_spec palindromeDecider (runFrom_palindromeDecider [true, false, true]).1
  rwa [(runFrom_palindromeDecider [true, false, true]).2.trans
    (show [decide [true, false, true].Palindrome] = [true] by decide)] at h

/-- The two-tape simulation decides every palindrome instance in time `O(n log n)`. -/
example (x : List Bool) : ∃ T ≤ (80 * 1 + 2) * (3 * x.length + 3 + 1) *
      (Nat.log 2 (3 * x.length + 3 + 1) + 1),
    ((hennieStearns palindromeDecider).runFrom
      ((hennieStearns palindromeDecider).initCfg (x.map .inl)) T).Halted ∧
    ((hennieStearns palindromeDecider).runFrom
      ((hennieStearns palindromeDecider).initCfg (x.map .inl)) T).output =
      [decide x.Palindrome].map .inl :=
  (runFrom_palindromeDecider x).2 ▸
    hennieStearns_spec palindromeDecider (runFrom_palindromeDecider x).1

end CslibFrontierTests.HennieStearns
