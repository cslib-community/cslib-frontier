/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Complexity.Problems.NEXPBoundedAcceptance

set_option linter.privateModule false

/-!
# Smoke tests for `NEXPBoundedAcceptance` (Arora–Barak Exercise 2 §9, 4 §3)

Exercises:
1. `NEXPBoundedAcceptanceInstance`, `encNEXPBoundedAcceptanceInstance`, and
   `NEXPBoundedAcceptanceInstance.decoder`.
2. Concrete evaluation of `NEXPBoundedAcceptanceInstance.Accepts` and
   `NEXPBoundedAcceptance.verifier` on accepting and zero-step instances.
3. `NEXPBoundedAcceptance.mem_NE`, `NEXPBoundedAcceptance.mem_NEXP`,
   `NEXPBoundedAcceptance.polyTimeComplete_NE`, `NEXPBoundedAcceptance.polyTimeComplete_NEXP`, and
   the collapse equivalence `NEXPBoundedAcceptance.NEXP_eq_EXP_iff`.
-/

namespace CslibFrontierTests.NEXPBoundedAcceptance

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Halt at once, emitting the symbol `1` (`eBit true`), whatever the input head reads. -/
private def acceptAct : Act := ⟨0, [], some 1, none⟩

/-- A machine with no work tapes that accepts every input in one step. -/
private def acceptDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, acceptAct), (⟨0, some 0, []⟩, acceptAct), (⟨0, some 1, []⟩, acceptAct)]⟩

example :
    NEXPBoundedAcceptanceInstance.decoder.decode
      (encNEXPBoundedAcceptanceInstance ⟨acceptDesc, [true, false], 5⟩) =
      ⟨acceptDesc, [true, false], 5⟩ :=
  NEXPBoundedAcceptanceInstance.decoder.decode_enc _

example : (⟨acceptDesc, [true], 1⟩ : NEXPBoundedAcceptanceInstance).Accepts [false] := by
  decide

example : (⟨acceptDesc, [true], 1⟩ : NEXPBoundedAcceptanceInstance) ∈ NEXPBoundedAcceptance :=
  NEXPBoundedAcceptance.mem_iff.mpr ⟨[false], by decide, by decide⟩

example :
    NEXPBoundedAcceptance.verifier (⟨acceptDesc, [true], 1⟩, frame [false] ++ [false]) = true :=
  (NEXPBoundedAcceptance.verifier_eq_true_iff _).mpr (by decide)

example (d : Desc) (x c : List Bool) :
    ¬ (⟨d, x, 0⟩ : NEXPBoundedAcceptanceInstance).Accepts c := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd h)

example : NEXPBoundedAcceptance ∈ NE encNEXPBoundedAcceptanceInstance ∧
    NEXPBoundedAcceptance ∈ NEXP encNEXPBoundedAcceptanceInstance :=
  ⟨NEXPBoundedAcceptance.mem_NE, NEXPBoundedAcceptance.mem_NEXP⟩

example : PolyTimeComplete @NE encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance ∧
    PolyTimeComplete @NEXP encNEXPBoundedAcceptanceInstance NEXPBoundedAcceptance :=
  ⟨NEXPBoundedAcceptance.polyTimeComplete_NE, NEXPBoundedAcceptance.polyTimeComplete_NEXP⟩

example :
    PolyTimeReducible encBits encNEXPBoundedAcceptanceInstance
      {x | diagonal x = true} NEXPBoundedAcceptance :=
  NEXPBoundedAcceptance.polyTimeHard_NEXP encBits _
    (EXP_subset_NEXP setOf_diagonal_mem_EXP)

example :
    (∀ {α : Type} (enc : α ↪ List Bool), NEXP enc = EXP enc) ↔
      NEXPBoundedAcceptance ∈ EXP encNEXPBoundedAcceptanceInstance :=
  NEXPBoundedAcceptance.NEXP_eq_EXP_iff

end CslibFrontierTests.NEXPBoundedAcceptance
