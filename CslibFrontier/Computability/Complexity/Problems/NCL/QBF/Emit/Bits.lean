/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation.Bits

/-!
# Emitting initial and target configurations

Each fixed fragment contributes a fixed bit list. The output fragment carries the record bit;
the remaining fragments initialize quantifier memories and the inactive matrix network.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.configurationBits`: concatenate fragment configurations.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.configurationBits_body`: canonical expanded body configurations.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

/-- Concatenate canonical primitive configurations of the shared source instructions. -/
@[expose] def configurationBits (recorded : Bool) : Program → List Bool :=
  Interpretation.configurationBits Gate.bitMap recorded

/-- Chain and terminal instruction bits agree with the canonical expanded body configuration. -/
theorem configurationBits_body (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    configurationBits recorded (chain 0 qs ++ terminal 0 qs.length ms) =
      Gate.extendedBits (Matrix.body qs ms) (Initial.body qs ms).orient :=
  Interpretation.configurationBits_body Gate.bitMap recorded qs ms

end Cslib.Complexity.NCL.QBF.Emit
