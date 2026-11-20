/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Circuit.Boolean.RandomizedDepth
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-! # Checked uniform randomized circuit -/

set_option linter.privateModule false

namespace CslibFrontierTests.RandomizedDepth

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-- For nonempty inputs the first wire is the first input bit. For empty input it is the coin. -/
private def firstWire (n : ℕ) : Circuit signature (n + 1) 1 :=
  Circuit.wiring signature fun _ => 0

private def firstWireLanguage : Language Bool :=
  Language.ofSlices fun _ x => Fin.append x (fun _ : Fin 1 => true) 0

private theorem firstWire_logspace :
    ComputableInLogSpace (fun n => ⟨n + 1, firstWire n⟩) encUnary (encCircuit 1) := by
  have hsucc : ComputableInLogSpace (fun n : ℕ => n + 1) encUnary encUnary :=
    ComputableInLogSpace.of_cons_true fun n => List.replicate_succ
  refine (hsucc.pair (ComputableInLogSpace.const (encMid := encCode)
    (([], [0]) : List (Op × List ℕ) × List ℕ))).congr fun n => ?_
  rw [encCircuit_apply]
  rfl

private theorem firstWire_succeeds (n : ℕ) :
    HasOneSidedError (n := n) (r := 1) (firstWire n) firstWireLanguage := by
  intro x
  simp only [firstWireLanguage, Language.slice_ofSlices, firstWire, Circuit.eval_wiring,
    Function.comp_apply]
  cases n with
  | zero =>
    have h : x = Fin.elim0 := Subsingleton.elim _ _
    subst x
    decide
  | succ n =>
    have read (coins : Fin 1 → Bool) : Fin.append x coins 0 = x 0 :=
      Fin.append_left x coins 0
    simp only [read]
    constructor
    · intro h
      simp [h]
    · intro h _
      exact h

example : firstWireLanguage ∈ LogSpaceUniformRNC1 := by
  refine ⟨0, fun _ => 0, fun _ => 1, ⟨0, Filter.Eventually.of_forall (by simp)⟩,
    ⟨0, Filter.Eventually.of_forall (by simp)⟩,
    firstWire, firstWire_logspace, fun n => ⟨?_, ?_, firstWire_succeeds n⟩⟩
  · simp [firstWire]
  · simp [firstWire]

end CslibFrontierTests.RandomizedDepth
