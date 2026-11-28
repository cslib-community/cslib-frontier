/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Circuit.Encoding.PolyTime

/-!
# Reading an encoded De Morgan circuit

The De Morgan form of `Cslib.Circuits.Circuit.computableInPolyTime_arity_code`: an encoded circuit
read as the pair of its number of inputs and its code.

## Main results

* `Cslib.Circuits.Boolean.computableInPolyTime_arity_code`: an encoded De Morgan circuit as the
  pair of its number of inputs and its code.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- Read an encoded De Morgan circuit as the pair of its number of inputs, in unary, and its code
(`Cslib.Circuits.Circuit.computableInPolyTime_arity_code`). -/
theorem computableInPolyTime_arity_code (m : ℕ) :
    ComputableInPolyTime (fun c : Σ n, Circuit signature n m => (c.1, c.2.code)) (encCircuit m)
      (encPair encUnary encCode) :=
  Circuit.computableInPolyTime_arity_code (σ := signature) encOp m

end Cslib.Circuits.Boolean
