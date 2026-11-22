/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteBounds

/-!
The native router is exercised on an asymmetric signed product operand and a finishing-adder
edge. Canonicalization clears unrelated arithmetic storage, and both empty and nonempty root
preparation satisfy the invariant used by the fixed alternating controller.
-/

namespace CslibFrontierTests.StoppingProductRouting

open Cslib.Circuits.Frontier.FastContraction StoppingQuery Product ProductRouting

private def parameters : Parameters := ⟨0, 3, 16⟩

private def operandPath : List Bool := [false, false, false, false, true, false, true]

private def rightOperand : NodeData := portData 4 2 3 operandPath false 2 1

-- Right-operand selection changes both the block offset and the coefficient coordinate.
example : Product.source parameters rightOperand 0 = some (valueData 8 2 2 1) := rfl

example : (ProductRouting.next (atNode parameters rightOperand true) false).data =
    valueData 8 2 2 1 := rfl

-- Moving down the finishing adder produces a canonical address with no stale round field.
example : Product.source parameters (finishData 4 2 3 ⟨11, 0, 2⟩) 0 =
    some (finishData 4 2 3 ⟨8, 0, 2⟩) := rfl

private def staleOperand : NodeData :=
  { rightOperand with address := ⟨3, 100, 100⟩, remaining := 17 }

example : ofNode (node staleOperand) = rightOperand := rfl

example : ¬ Canonical staleOperand := by
  unfold Canonical
  decide

example : Canonical (ofNode (node staleOperand)) := canonical_ofNode _

private theorem rightOperand_valid :
    Valid parameters 12 3 (atNode parameters rightOperand true) := by
  constructor
  · rfl
  · exact canonical_ofNode (.product 0 4 2 3 (.port operandPath false 2 1))
  · change ProductWellFormed 0 3 16 0 12 3
      (.product 0 4 2 3 (.port operandPath false 2 1))
    unfold ProductWellFormed SignedValueGame.WellFormed
    decide

example : Valid parameters 12 3
    (ProductRouting.next (atNode parameters rightOperand true) false) :=
  rightOperand_valid.next false

example : (encPosition (ProductRouting.next (atNode parameters rightOperand true) false)).length ≤
    ProductRouting.metadataBound parameters 12 3 :=
  (rightOperand_valid.next false).length_encPosition_le

example : Valid parameters (2 ^ Nat.clog 2 parameters.vertices) (Nat.clog 2 parameters.vertices)
    (ProductRouting.root parameters 3 2 true) :=
  valid_root parameters (by decide) (by decide) true

example : Valid ⟨0, 3, 0⟩ 1 0 (ProductRouting.root ⟨0, 3, 0⟩ 0 0 true) :=
  valid_root ⟨0, 3, 0⟩ (by decide) (by decide) true

end CslibFrontierTests.StoppingProductRouting
