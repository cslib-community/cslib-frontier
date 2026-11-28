/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition

/-!
# Codes of replicated De Morgan circuits

Specializes `Cslib.Circuits.Circuit.replicateCode` from
`CslibFrontier.Computability.Circuit.Encoding.Combinators` to De Morgan circuits.

## Main definitions

* `Cslib.Circuits.Boolean.replicateCode`: the code of disjoint De Morgan copies.

## Main results

* `Cslib.Circuits.Boolean.replicateCode_code`: agreement with `Circuit.replicate`.
* `Cslib.Circuits.Boolean.length_replicateCode`: the gate count is multiplied by the number of
  copies.
* `Cslib.Circuits.Boolean.computableInPolyTime_replicateCode`: constructor efficiency.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- The code of `k` disjoint copies of the De Morgan circuit with code `code` on `n` inputs. -/
abbrev replicateCode (n k : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.replicateCode n k code

/-- Replicating a raw code multiplies its gate count by `k`. -/
theorem length_replicateCode (n k : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (replicateCode n k code).1.length = k * code.1.length :=
  Circuit.length_replicateCode n k code

/-- Replicating the code of a circuit gives the code of its disjoint copies. -/
theorem replicateCode_code {n m : ℕ} (c : Circuit signature n m) (k : ℕ) :
    replicateCode n k c.code = (c.replicate k).code :=
  (c.code_replicate k).symm

/-- Replicating a raw code is polynomial-time, with a binary input count and a unary number of
copies. -/
@[fun_prop]
theorem computableInPolyTime_replicateCode {α : Type} {enc : α ↪ List Bool}
    {n k : α → ℕ} {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hk : ComputableInPolyTime k enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun a => replicateCode (n a) (k a) (code a)) enc encCode :=
  Circuit.computableInPolyTime_replicateCode hn hk hcode

end Cslib.Circuits.Boolean
