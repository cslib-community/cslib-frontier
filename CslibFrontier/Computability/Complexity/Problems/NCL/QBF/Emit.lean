/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation

/-!
# Emitting source circuits as fixed instructions

An instruction places one fixed circuit fragment at a wire offset. Indexed list scans emit the
quantifier chain, clause rows and terminal. Expanding instructions gives the existing primitive
word, including its edge creation order.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Opcode`: the finite table of circuit fragments.
* `Cslib.Complexity.NCL.QBF.Emit.Program`: fragment names paired with wire offsets.
* `Cslib.Complexity.NCL.QBF.Emit.expand`: expand instructions to primitive layers.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.expand_circuit`: expansion preserves the circuit word.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open Diagram

private def primitiveTarget : Interpretation.Target where
  map D := D.subst Gate.expand
  map_id _ := rfl
  map_comp _ _ := rfl
  map_tensor _ _ := rfl

/-- Expanding the circuit instructions preserves the source diagram and its edge order. -/
theorem expand_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    expand (circuit qs ms) =
      ((OutputLatch.diagram.comp (Matrix.body qs ms)).subst Gate.expand).toWord Prim.interp 0 :=
  Interpretation.expand_circuit primitiveTarget qs ms

end Cslib.Complexity.NCL.QBF.Emit
