/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Data.BitString.FieldEnumeration

/-!
# Padded binary-field enumeration examples

The examples check field order, the no-choice code, invalid padding, the exact number of
legitimate assignments, and the zero-width and zero-row boundaries.
-/

open Cslib.BitString

-- The word `0110` has first field `01` and second field `10`.
example : binaryField 2 2 6 0 = 1 ∧ binaryField 2 2 6 1 = 2 := by decide

example : fieldChoice 2 0 = none ∧ fieldChoice 2 1 = some 0 ∧
    fieldChoice 2 2 = some 1 ∧ fieldChoice 2 3 = none := by decide

-- There are nine legitimate two-row choices; the other seven four-bit words are padding.
example : (∑ a ∈ Finset.range 16,
    if ∀ j : Fin 2, binaryField 2 2 a j ≤ 2 then 1 else 0) = (9 : ℕ) := by decide

-- The general weighted theorem gives the exact number of valid assignments for every size.
example (modes rows width : ℕ) (h : modes + 1 ≤ 2 ^ width) :
    (∑ a ∈ Finset.range (2 ^ (rows * width)),
      if ∀ j : Fin rows, binaryField rows width a j ≤ modes then 1 else 0) =
        (modes + 1) ^ rows := by
  simpa using sum_binaryFields modes rows width h (fun _ => (1 : ℕ))

-- No rows leave one empty choice, whose weight need not be one.
example : (∑ a ∈ Finset.range (2 ^ (0 * 3)),
    if ∀ j : Fin 0, binaryField 0 3 a j ≤ 7 then 17 else 0) = (17 : ℕ) := by decide

-- With no modes, zero bits suffice for every field and there is still one assignment.
example : (∑ a ∈ Finset.range (2 ^ (4 * 0)),
    if ∀ j : Fin 4, binaryField 4 0 a j ≤ 0 then 1 else 0) = (1 : ℕ) := by decide
