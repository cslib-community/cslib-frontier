/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition

/-!
# Native codes for the half-split balanced De Morgan circuit

Specializes `Cslib.Circuits.Circuit.balancedCode` from
`CslibFrontier.Computability.Circuit.Encoding.Combinators` to De Morgan circuit codes.

## Main definitions

* `Cslib.Circuits.Boolean.balancedCode`: the complete raw code of a balanced De Morgan circuit.

## Main results

* `Cslib.Circuits.Boolean.balancedCode_eq_code`: exact agreement with `Circuit.balanced`.
* `Cslib.Circuits.Boolean.computableInPolyTime_balancedCode`: uniform construction from
  binary input arity and native generators of the operator, fallback and leaf codes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- Generate the half-split balanced De Morgan circuit code on shared inputs. -/
abbrev balancedCode (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : List (Op × List ℕ) × List ℕ :=
  Circuit.balancedCode n op unit leaves

/-- Exact raw-code agreement with `Circuit.balanced`. -/
theorem balancedCode_eq_code {n r : ℕ} (op : Circuit signature (r + r) r)
    (unit : Circuit signature n r) (leaves : List (Circuit signature n r)) :
    balancedCode n op.code unit.code (leaves.map Circuit.code) =
      (Circuit.balanced op unit leaves).code :=
  (Circuit.code_balanced op unit leaves).symm

/-- Uniform native generation from the binary shared-input count and the complete operator,
fallback and leaf codes. -/
@[fun_prop]
theorem computableInPolyTime_balancedCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {op unit : α → List (Op × List ℕ) × List ℕ}
    {leaves : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime op enc encCode)
    (hu : ComputableInPolyTime unit enc encCode)
    (hl : ComputableInPolyTime leaves enc (encList encCode)) :
    ComputableInPolyTime (fun a => balancedCode (n a) (op a) (unit a) (leaves a))
      enc encCode :=
  Circuit.computableInPolyTime_balancedCode hn hop hu hl

end Cslib.Circuits.Boolean
