/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.QMIP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Quantum.Bell

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumMultiprover

open Cslib.Quantum Turing.MultiTapeTM

private abbrev twoProvers : UniformMultiproverVerifier where
  privateWidth n := n + 1
  messageWidth _ := 2
  turns _ := ([], [])
  computableInPolyTime_privateWidth := .unary_succ
  computableInPolyTime_messageWidth := .const 2
  computableInPolyTime_turns := .const _
  le_privateWidth n := Nat.le_succ n
  privateWidth_pos n := Nat.succ_pos n
  wellFormed := by simp
  proverCount _ := 2
  messagePerProver _ := 1
  computableInPolyTime_proverCount := .const 2
  computableInPolyTime_messagePerProver := .const 1
  proverCount_pos _ := by decide
  messageWidth_eq _ := rfl

/-- The two local registers have interleaved indices in the joint register. -/
example : (twoProvers.proverWires 0 1 0 0 : Fin 5) = 1 ∧
    twoProvers.proverWires 0 1 0 1 = 3 ∧
    twoProvers.proverWires 0 1 1 0 = 2 ∧
    twoProvers.proverWires 0 1 1 1 = 4 := by decide

private noncomputable def sharedBell : Qubits 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finTwoArrowEquiv Bool).symm bell

example : ‖sharedBell‖ = 1 := by simp [sharedBell]

/-- Giving the parties an entangled private state leaves the initial verifier bit at zero. -/
example : twoProvers.acceptProb [] (p := 1) sharedBell (fun _ _ => 1) = 0 := by
  let wires : Fin 2 ↪ Fin 5 := Fin.natAddEmb 3
  change measureProb (Circuit.eval [] (embedState wires (inputState 5 []) sharedBell))
    (accepting 5) = 0
  rw [Circuit.eval_nil, measureProb]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [embedState_apply]
  have hoff : ¬ AgreeOff wires y (inputState 5 []) := by
    intro h
    have h0 := h (0 : Fin 5) (by decide)
    have hy0 := (mem_accepting (by decide)).mp hy
    change y 0 = false at h0
    change y 0 = true at hy0
    rw [hy0] at h0
    contradiction
  simp [hoff]

end CslibFrontierTests.QuantumMultiprover
