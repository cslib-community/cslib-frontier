/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Units
import Mathlib.Data.Fin.VecNotation

/-! Tests of the units of a bit string, as a client that sees only the public statements, on
small strings: a string that does not fill its last unit, a string of whole units (which gets one
more unit, holding the `1`), the empty string, and the bits of a word. -/

namespace CslibFrontierTests.SeparationUnits

open Cslib.Circuits.Arithmetic.Separation.Cut

/-- One bit in units of two bits: a single unit, the bit followed by the `1`. -/
example : unitCount 2 [true] = 1 := rfl
example : unitsOf 2 [false] 0 = some ![false, true] := by decide
example : unitsOf 2 [false] 1 = none := by decide

/-- Two bits fill a unit, so the `1` goes into a second unit, followed by a zero. -/
example : unitCount 2 [true, true] = 2 := rfl
example : unitsOf 2 [true, true] 0 = some ![true, true] := by decide
example : unitsOf 2 [true, true] 1 = some ![true, false] := by decide

/-- The empty string has one unit, which distinguishes it from the string `[false]` above. -/
example : unitsOf 2 [] 0 = some ![true, false] := by decide

/-- The two strings above with the same number of units differ in a unit. -/
example : unitsOf 2 [] ≠ unitsOf 2 [false] :=
  (unitsOf_injective Nat.zero_lt_two).ne (by decide)

/-- The bits of a word over `Fin 2`, each letter coded by two bits. -/
example : bitsOf (fun a : Fin 2 => ![a = 1, true]) [0, 1] = [false, true, true, true] := by
  decide

/-- Two words with the same bits under an injective code of two bits are equal. -/
example {X Y : List (Fin 2)} (h : bitsOf (fun a : Fin 2 => ![a = 1, true]) X =
    bitsOf (fun a : Fin 2 => ![a = 1, true]) Y) : X = Y :=
  bitsOf_injective (by decide) Nat.zero_lt_two h

end CslibFrontierTests.SeparationUnits
