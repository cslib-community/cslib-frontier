/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Problems.SPACETM

set_option linter.privateModule false

/-!
# Smoke tests for `SPACETM` in the native visited-space model

After Arora and Barak, Chapter 4, Section 4.3, display (2) (printed p. 79 / PDF p. 95) and
Exercise 4 §3 (printed p. 89 / PDF p. 105). In the library's native visited-space model, `SPACETM`
enforces the exact visited work-tape cell budget `simSpace a.machine (a.input.map eBit) t ≤ a.space`
via `Turing.MultiTapeTM.Universal.spaceBoundedUniversal`.

Exercises:
1. `SPACETMInstance`, `encSPACETMInstance`, and `SPACETMInstance.decoder`.
2. Concrete evaluation of `SPACETMInstance.Accepts` on an accepting description, rejection of a
   looping description via the configuration-count clock (`SPACETM.mem_iff_accepts_clock`), and a
   regression test separating `space = 1` (rejected) from `space = 2` (accepted) on a 1-work-tape
   machine that visits two work-tape cells before accepting (`simSpace = 2`).
3. `SPACETM.desc_mem_iff`, `SPACETM.mem_PSPACE`, `SPACETM.pspaceHard`, and
   `SPACETM.pspaceComplete`.
-/

namespace CslibFrontierTests.SPACETM

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

example := @Turing.MultiTapeTM.Universal.exists_simSpace_le_and_universal_eq_true_iff
example := @Turing.MultiTapeTM.Universal.computableInPolySpace_spaceBoundedUniversal
example := @SPACETM.desc_mem_iff

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

/-- Step 0 on a 1-work-tape machine: move the work-tape head right (`+1`) and transition to state
`1` without halting. -/
private def moveRightAct : Act := ⟨0, [(none, 1)], none, some 1⟩

/-- Step 1 on a 1-work-tape machine: halt and emit `1` (`eBit true`). -/
private def haltOneTapeAct : Act := ⟨0, [(none, 0)], some 1, none⟩

/-- A 1-work-tape machine that moves its work-tape head from `0` to `1` on step 1 (visiting `2`
cells) and halts accepting on step 2. -/
private def twoCellAcceptDesc : Desc :=
  ⟨1, 0,
    [(⟨0, none, [none]⟩, moveRightAct),
     (⟨0, some 0, [none]⟩, moveRightAct),
     (⟨0, some 1, [none]⟩, moveRightAct),
     (⟨1, none, [none]⟩, haltOneTapeAct),
     (⟨1, some 0, [none]⟩, haltOneTapeAct),
     (⟨1, some 1, [none]⟩, haltOneTapeAct)]⟩

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
  exact Bool.false_ne_true (congrArg Prod.snd h.2)

example : ¬ (⟨loopDesc, [true], 0⟩ : SPACETMInstance).Accepts 3 := by decide

/-- `twoCellAcceptDesc` visits `2` work-tape cells on `[true]` by step `2`, so it accepts at
visited-cell budget `space = 2` and is rejected at `space = 1` even though its encoded
configuration fits well within `(⟨twoCellAcceptDesc, [true], 1⟩ : SPACETMInstance).cfgBudget`. -/
example : (⟨twoCellAcceptDesc, [true], 2⟩ : SPACETMInstance).Accepts 2 := by decide

example : (⟨twoCellAcceptDesc, [true], 2⟩ : SPACETMInstance) ∈ SPACETM :=
  ⟨2, by decide⟩

example : ¬ (⟨twoCellAcceptDesc, [true], 1⟩ : SPACETMInstance).Accepts 2 := by decide

example : (⟨twoCellAcceptDesc, [true], 1⟩ : SPACETMInstance) ∉ SPACETM := by
  rintro ⟨t, ht⟩
  rcases t with _ | _ | t
  · revert ht; decide
  · revert ht; decide
  · have h2 : ¬ simSpace twoCellAcceptDesc ([true].map eBit) 2 ≤ 1 := by decide
    exact h2 ((simSpace_mono twoCellAcceptDesc ([true].map eBit) (Nat.le_add_left 2 t)).trans ht.1)

example : SPACETM ∈ PSPACE encSPACETMInstance :=
  SPACETM.mem_PSPACE

example : PSPACEComplete encSPACETMInstance SPACETM :=
  SPACETM.pspaceComplete

example {α : Type} (enc : α ↪ List Bool) {A : Set α} (hA : A ∈ P enc) :
    PolyTimeReducible enc encSPACETMInstance A SPACETM :=
  SPACETM.pspaceHard enc A (P_subset_PSPACE hA)

end CslibFrontierTests.SPACETM
