/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sigma

/-!
# Reading an encoded circuit

`Cslib.Circuits.Circuit.encCircuit` encodes a circuit as a dependent pair of its number of inputs
and the circuit (`Turing.MultiTapeTM.encSigma`), whose second component is encoded by its code.
Reading it as the plain pair of the number of inputs and the code is therefore free, after which the
pair projections read either part.

## Main results

* `Cslib.Circuits.Circuit.computableInPolyTime_arity_code`: an encoded circuit as the pair of its
  number of inputs and its code.
-/

public section

namespace Cslib.Circuits.Circuit

open Turing.MultiTapeTM

variable {σ : Signature}

/-- Read an encoded circuit as the pair of its number of inputs, in unary, and its code. The
encoded words are the same. -/
theorem computableInPolyTime_arity_code (encOp : σ.Op ↪ List Bool) (m : ℕ) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n m => (c.1, c.2.code)) (encCircuit encOp m)
      (encPair encUnary (encCode encOp)) := by
  unfold encCircuit
  exact ComputableInPolyTime.sigmaView encUnary (encCode encOp)
    (fun n (c : Circuit σ n m) => c.code) fun _ _ => rfl

end Cslib.Circuits.Circuit
