/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Iteration.EndpointInput
import CslibFrontier.Computability.Circuit.Boolean.Iteration.LiveShort

/-!
# Boundary cases for powering with an input exponent
-/

namespace CslibFrontierTests.EndpointInput

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

private def fourCycle (x : BitString 2) : BitString 2 := ![x 1, !x 0]

-- At the cutoff the short branch needs a return. The first return is exactly four steps.
example : ¬LiveShortReady fourCycle 2 (fun _ => false) 2 := by
  unfold LiveShortReady
  decide

example : LiveShortReady fourCycle 4 (fun _ => false) 100 := by
  unfold LiveShortReady
  decide

-- Before the cutoff the prefix already supplies the answer, even on a longer cycle.
example : LiveShortReady fourCycle 2 (fun _ => false) 1 := Or.inl (by decide)

-- The last three input wires encode three, least significant bit first.
example : inputTimeIterate fourCycle 3 ![false, false, true, true, false] = ![true, false] := by
  decide

end CslibFrontierTests.EndpointInput
