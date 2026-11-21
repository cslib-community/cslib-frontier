/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.BQP.Space
import CslibFrontier.Computability.Complexity.Classes.BQP.TensorContraction
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! # Checked unitary space-bounded circuit generation -/

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumSpace

open Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM

private def inputGates (b : Bool) : List GateCode :=
  if b then [(false, 0, [])] else []

private def inputDescription (b : Bool) : UnitarySpaceCircuitDescription :=
  ⟨1, (inputGates b).map fun g => (false, g)⟩

/-- The generator reads the input bit and emits a different circuit for each value. Both
circuits start on the same one-qubit all-zero state. -/
private def inputFamily : UnitarySpaceCircuitFamily encBool (fun n => Nat.log2 n + 1) where
  description := inputDescription
  generator := by
    obtain ⟨u, hzero⟩ := computableInTimeAndSpace_of_finite
      (encIn := encBool) (encOut := encUnitarySpaceCircuitDescription) inputDescription
    exact ⟨u, hzero.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)⟩
  width_le b := by simp [inputDescription]
  width_pos b := by simp [inputDescription]
  wellFormed b g hg := by
    cases b
    · exact False.elim (List.not_mem_nil hg)
    · obtain rfl := List.mem_singleton.mp hg
      decide

private theorem inputFamily_acceptProb (b : Bool) :
    inputFamily.acceptProb b = if b then 1 else 0 := by
  change PhaseGateCode.acceptProb 1 ((inputGates b).map fun g => (false, g)) [] = _
  rw [PhaseGateCode.acceptProb_ofCodes]
  cases b
  · change acceptProb 1 [] [] = 0
    rw [acceptProb_eq_acceptGap _ (by decide : ∀ g ∈ ([] : List GateCode), g.WellFormed 1),
      show List.ofFn (inputState 1 []) = [false] by decide,
      show acceptGap [] [false] = 0 by decide]
    norm_num
  · change acceptProb 1 [(false, 0, [])] [] = 1
    rw [acceptProb_eq_acceptGap _ (by decide), show List.ofFn (inputState 1 []) = [false] by decide,
      show acceptGap [(false, 0, [])] [false] = 1 by decide]
    norm_num [hadamardCount]

example : {b : Bool | b = true} ∈ BQL encBool := by
  let F := inputFamily.enlargeSpace (space' := fun n => 1 * (Nat.log2 n + 1))
    (fun n => by simp)
  refine ⟨1, F, fun b => ?_⟩
  rw [show F.acceptProb b = inputFamily.acceptProb b from
    inputFamily.acceptProb_enlargeSpace _ _, inputFamily_acceptProb]
  cases b <;> norm_num

end CslibFrontierTests.QuantumSpace
