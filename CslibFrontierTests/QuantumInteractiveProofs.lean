/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Circuit.Quantum.Classical
import CslibFrontier.Computability.Complexity.Classes.QIP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumInteractiveProofs

open Cslib.Quantum Turing.MultiTapeTM

/-- On empty input there is one verifier qubit and one message qubit. The final turn
copies the returned message bit to the verifier's output qubit. -/
private abbrev verifier : UniformInteractiveVerifier where
  privateWidth n := n + 1
  messageWidth _ := 1
  turns _ := ([[]], [(false, false, 0, [1])])
  computableInPolyTime_privateWidth := .unary_succ
  computableInPolyTime_messageWidth := .const 1
  computableInPolyTime_turns := .const _
  le_privateWidth n := Nat.le_succ n
  privateWidth_pos n := Nat.succ_pos n
  wellFormed n gs hgs g hg := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · simp at hg
    · simp only [List.mem_singleton] at hg
      subst g
      simp [PhaseGateCode.WellFormed, GateCode.WellFormed]

private theorem interaction_flip :
    verifier.interaction 0 (p := 0) (fun _ => Gate.not) =
      Circuit.ofCodes 2 [(false, 1, []), (false, 0, [1])] := by
  have hV : verifier.verifierWires 0 0 = Function.Embedding.refl (Fin 2) := by
    ext i
    rfl
  change [⟨1, Gate.not, verifier.proverWires 0 0⟩] ++
    (Circuit.ofPhaseCodes 2 [(false, false, 0, [1])]).mapWires
      (verifier.verifierWires 0 0) = _
  rw [hV]
  have hP : verifier.proverWires 0 0 =
      (⟨![1], fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 2) := by
    ext i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl
  rw [hP]
  simp [Circuit.ofPhaseCodes, PhaseGateCode.toPlacedGate?, Circuit.ofCodes,
    GateCode.toPlacedGate?, Circuit.mapWires, PlacedGate.mapWires]

/-- The prover can send a one, which the verifier reads on its final turn. -/
example : verifier.acceptProb [] (p := 0) (fun _ => Gate.not) = 1 := by
  have hclass : GateCode.IsClassical 2 [(false, 1, []), (false, 0, [1])] := by
    simp [GateCode.IsClassical, GateCode.WellFormed]
  change measureProb ((verifier.interaction 0 (p := 0) (fun _ => Gate.not)).run
    (inputState 2 [])) (accepting 2) = 1
  rw [interaction_flip, Circuit.run_ofCodes hclass, measureProb_ket]
  have hmem : GateCode.classicalRun [(false, 1, []), (false, 0, [1])] (inputState 2 [])
      ∈ accepting 2 := by
    rw [mem_accepting (by decide)]
    decide
  simp only [hmem, ↓reduceIte]

end CslibFrontierTests.QuantumInteractiveProofs
