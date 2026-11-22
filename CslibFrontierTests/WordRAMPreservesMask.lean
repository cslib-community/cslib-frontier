/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.PreservesMask

/-!
# Reflected register-preservation and width-read checks

Regression tests for `CslibFrontier.Computability.WordRAM.PreservesMask`: single-pass `Bool`
preservation checks (`Code.preservesAll`, `Code.preserves_of_preservesAllPred`), register-write
interval bounds (`Code.writeStart`, `Code.writeEnd`), width-read reflection
(`Code.readsWidthBool`, `Code.not_readsWidth_of_readsWidthBool`), and compositional `Code.rename`
lemmas across data instructions, branches, loops, stores, and `Code.rand` over large register
banks without raising `maxRecDepth`.
-/

namespace CslibFrontierTests.WordRAMPreservesMask

open Cslib.WordRAM

private abbrev r0 : Fin 8 := 0
private abbrev r1 : Fin 8 := 1
private abbrev r2 : Fin 8 := 2
private abbrev r3 : Fin 8 := 3
private abbrev r4 : Fin 8 := 4
private abbrev r5 : Fin 8 := 5

/-- Sample loop-and-branch kernel writing only registers `2`, `3`, and `4` (plus a memory store). -/
private def sampleKernel : Code .standard 8 := ram[
  r2 ← #1;
  r3 ← r0 + r1;
  while r2 < r3 do [
    if r2 = r1 then [ r4 ← *r0 ] else [ *r0 ← r3 ];
    r2 ← r2 + r2 ] ]

example : sampleKernel.writeStart = 2 := rfl
example : sampleKernel.writeEnd = 5 := rfl
example : sampleKernel.readsWidthBool = false := rfl

example (i : Fin 8) (hi : i.val < 2) : sampleKernel.Preserves i :=
  Code.preserves_of_writeStart (by decide) hi

example (i : Fin 8) (hi : 5 ≤ i.val) : sampleKernel.Preserves i :=
  Code.preserves_of_writeEnd (by decide) hi

example : ∀ i : Fin 8, (i.val < 2 ∨ i = r5) → sampleKernel.Preserves i :=
  Code.preserves_of_preservesAllPred rfl

example : ¬sampleKernel.ReadsWidth :=
  Code.not_readsWidth_of_readsWidthBool rfl

/-- `Code.rand` writes its destination register without reading width. -/
private def randSample : Code .standard 8 :=
  .seq sampleKernel (.rand r5 r0)

example : randSample.writeStart = 2 := rfl
example : randSample.writeEnd = 6 := rfl
example : ¬randSample.ReadsWidth :=
  Code.not_readsWidth_of_readsWidthBool rfl

example : ∀ i : Fin 8, (i.val < 2 ∨ 6 ≤ i.val) → randSample.Preserves i :=
  Code.preserves_of_preservesAllPred rfl

/-- `Op.width` sets `readsWidthBool = true`. -/
private def widthSample : Code .standard 8 :=
  .seq sampleKernel (.op (.width r4))

example : widthSample.readsWidthBool = true := rfl
example : widthSample.ReadsWidth :=
  (widthSample.readsWidthBool_eq_true_iff).mp rfl

/-- Store-only programs preserve all registers (`writeStart = r`, `writeEnd = 0`). -/
private def storeOnly : Code .standard 8 := ram[ *r0 ← r1; *r2 ← r3 ]

example : storeOnly.writeStart = 8 := rfl
example : storeOnly.writeEnd = 0 := rfl
example (i : Fin 8) : storeOnly.Preserves i :=
  Code.preserves_of_writeEnd (by decide : storeOnly.writeEnd ≤ 0) (Nat.zero_le _)

/-- Compositional `rename` rules on a 400-register caller bank with default `maxRecDepth`. -/
private def highBank (j : Fin 8) : Fin 400 := ⟨320 + j.val, by omega⟩

private def callerProg : Code .standard 400 :=
  .seq (randSample.rename highBank) (.op (.const ⟨350, by decide⟩ 7))

example (i : Fin 400) (hi : i.val < 320) : callerProg.Preserves i := by
  have h1 : 320 ≤ (randSample.rename highBank).writeStart :=
    Code.offset_le_writeStart_rename (fun _ => rfl) (by decide) randSample
  have h2 : 320 ≤ callerProg.writeStart := le_min h1 (by decide)
  exact Code.preserves_of_writeStart h2 hi

example (i : Fin 400) (hi : 351 ≤ i.val) : callerProg.Preserves i := by
  have h1 : (randSample.rename highBank).writeEnd ≤ 320 + 8 :=
    Code.writeEnd_rename_le_offset (fun _ => rfl) randSample
  have h2 : callerProg.writeEnd ≤ 351 := max_le (h1.trans (by decide)) (by decide)
  exact Code.preserves_of_writeEnd h2 hi

example : ∀ i : Fin 400, (i.val < 320 ∨ (330 ≤ i.val ∧ i.val < 350) ∨ 351 ≤ i.val) →
    callerProg.Preserves i := by
  apply Code.preserves_of_preservesAllPred
  simp only [callerProg, Code.preservesAll]
  rw [Code.preservesAll_rename_of_false (f := highBank)]
  · rfl
  · decide

example : ¬callerProg.ReadsWidth := by
  simp only [callerProg, Code.ReadsWidth, Code.readsWidth_rename, Op.ReadsWidth]
  exact fun h => h.elim (Code.not_readsWidth_of_readsWidthBool rfl) False.elim

end CslibFrontierTests.WordRAMPreservesMask
