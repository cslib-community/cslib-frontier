/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Complexity.Problems.SPACETM

set_option linter.privateModule false

/-!
# Smoke tests for `SPACETM` (Arora–Barak Exercise 4 §3)

Exercises:
1. `SPACETMInstance`, `encSPACETMInstance`, and `SPACETMInstance.decoder`.
2. Concrete evaluation of `SPACETMInstance.Accepts` on an accepting description and rejection of a
   looping description via the configuration-count clock (`SPACETM.mem_iff_accepts_clock`).
3. `SPACETM.mem_PSPACE`, `SPACETM.pspaceHard`, and `SPACETM.pspaceComplete`.
-/

namespace CslibFrontierTests.SPACETM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Halt at once, emitting the symbol `1` (`eBit true`), whatever the input head reads. -/
private def acceptAct : Act := ⟨0, [], some 1, none⟩

/-- A machine with no work tapes that accepts every input in one step. -/
private def acceptDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, acceptAct), (⟨0, some 0, []⟩, acceptAct), (⟨0, some 1, []⟩, acceptAct)]⟩

/-- Stay in state `0` forever without emitting output or moving the input head. -/
private def loopAct : Act := ⟨0, [], none, some 0⟩

/-- A machine with no work tapes that loops forever on every input. -/
private def loopDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, loopAct), (⟨0, some 0, []⟩, loopAct), (⟨0, some 1, []⟩, loopAct)]⟩

example :
    SPACETMInstance.decoder.decode (encSPACETMInstance ⟨acceptDesc, [true], 2⟩) =
      ⟨acceptDesc, [true], 2⟩ :=
  SPACETMInstance.decoder.decode_enc _

example : (⟨acceptDesc, [true], 0⟩ : SPACETMInstance).Accepts 1 := by decide

example : (⟨acceptDesc, [true], 0⟩ : SPACETMInstance) ∈ SPACETM :=
  ⟨1, by decide⟩

example : (⟨acceptDesc, [true], 0⟩ : SPACETMInstance).Accepts
    (2 ^ ((⟨acceptDesc, [true], 0⟩ : SPACETMInstance).cfgBudget + 1)) :=
  (SPACETM.mem_iff_accepts_clock _).mp ⟨1, by decide⟩

example (d : Desc) (x : List Bool) (n : ℕ) :
    ¬ (⟨d, x, n⟩ : SPACETMInstance).Accepts 0 := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd h)

example : ¬ (⟨loopDesc, [true], 0⟩ : SPACETMInstance).Accepts 3 := by decide

example : SPACETM ∈ PSPACE encSPACETMInstance :=
  SPACETM.mem_PSPACE

example : PSPACEComplete encSPACETMInstance SPACETM :=
  SPACETM.pspaceComplete

example {α : Type} (enc : α ↪ List Bool) {A : Set α} (hA : A ∈ P enc) :
    PolyTimeReducible enc encSPACETMInstance A SPACETM :=
  SPACETM.pspaceHard enc A (P_subset_PSPACE hA)

end CslibFrontierTests.SPACETM
