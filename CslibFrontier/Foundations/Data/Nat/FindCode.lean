/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.Range

/-!
# First match in a bounded natural-number range

`Cslib.findCode` visits consecutive candidates in order and returns the first passing one,
with no allocated list of candidates. Its specification uses the existing `List.find?`.

## Main definitions

* `Cslib.findCode`: a bounded first-match loop over consecutive natural numbers.

## Main results

* `Cslib.findCode_eq`: the loop agrees with first-match lookup in the corresponding range.
-/

public section

namespace Cslib

/-- Search `count` consecutive natural numbers from `start`, returning the first match.
The implementation keeps only the current candidate and remaining count. -/
@[expose] def findCode (p : ℕ → Bool) : (start count : ℕ) → Option ℕ
  | _, 0 => none
  | i, fuel + 1 => if p i then some i else findCode p (i + 1) fuel

/-- The bounded search agrees with first-match lookup in the corresponding range. -/
theorem findCode_eq (p : ℕ → Bool) (i fuel : ℕ) :
    findCode p i fuel = (List.range' i fuel).find? p := by
  induction fuel generalizing i with
  | zero => simp [findCode]
  | succ fuel ih => cases hp : p i <;> simp [findCode, List.range'_succ, ih, hp]

end Cslib
