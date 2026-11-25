/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Codes
import Mathlib.Data.Fin.VecNotation

/-! Tests of strings on a side and their code words, as a client that sees only the public
statements: the string on a side and its code word for two blocks, the bits of a unit, the
injectivity of code words that are long enough, and a code word that is too short to determine
the strings. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationCodes

open Cslib.Circuits.Arithmetic.Separation.Cut

/-- Labels of one bit for the indices `Bool`. -/
private def lab : Bool → Cslib.BitString 1 := fun b => ![b]

/-- The index `true` has strings of two bits, and the index `false` has the empty string. -/
private def len : Bool → ℕ := fun b => if b then 2 else 0

/-- Two blocks with the indices `true` and `false`. -/
private def idx : Fin 2 → Bool := ![true, false]

/-- The string on the side: the label `1`, the string `11`, the label `0`, the empty string. -/
example : sideString lab len idx (fun _ _ => true) = [true, true, true, false] := by decide

/-- Its three units of two bits; the last one holds the `1` that ends the string. -/
example : codeWord lab len 2 3 idx (fun _ _ => true) =
    ![some ![true, true], some ![true, false], some ![true, false]] := by decide

example : (codeWord lab len 2 3 idx (fun _ _ => true) 1).bits = [true, false] := by decide

/-- Strings of two blocks have at most `2 * (2 + 1) / 2 + 1 = 4` units, so the first four units
determine the indices and the strings. -/
example {p p' : Σ i : Fin 2 → Bool, ∀ k, Cslib.BitString (len (i k))}
    (h : codeWord lab len 2 4 p.1 p.2 = codeWord lab len 2 4 p'.1 p'.2) : p = p' :=
  codeWord_injective (lab := lab) (by decide) Nat.zero_lt_two (m := 2) (by decide) (by decide) h

/-- The first unit alone does not: it holds the label and the first bit of the first block. -/
example : codeWord lab len 2 1 idx (fun _ _ => true) =
    codeWord lab len 2 1 idx (fun k b => k = 0 ∧ b.1 = 0) := by decide

end CslibFrontierTests.SeparationCodes
