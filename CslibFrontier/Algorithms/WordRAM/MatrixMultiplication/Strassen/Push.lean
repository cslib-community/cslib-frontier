/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native Strassen child layout and explicit frame push

The six buffer calculations and the parent/child frame stores are actual native execution.
The frame readback is proved from `Cslib.WordRAM.storeRecord_exec`; it is not supplied as an
algorithm input. Only one parent phase cell and seven newly pushed frame words change memory.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

private def LocateChildLocal (i : Fin 64) : Prop :=
  i = Reg.quarter ∨ i = Reg.formA ∨ i = Reg.formB ∨ i = Reg.product ∨
    i = Reg.childScratch ∨ i = Reg.childDepth

private instance (i : Fin 64) : Decidable (LocateChildLocal i) :=
  inferInstanceAs (Decidable
    (i = Reg.quarter ∨ i = Reg.formA ∨ i = Reg.formB ∨ i = Reg.product ∨
      i = Reg.childScratch ∨ i = Reg.childDepth))

private theorem locateChild_preserves (i : Fin 64) :
    ¬LocateChildLocal i → locateChild.Preserves i := by decide +kernel +revert

/-- Six native arithmetic/copy instructions derive every child buffer and depth. -/
theorem exec_locateChild {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (h4 : x.regs Reg.four = 4)
    (hw : Fits w (x.regs Reg.scratch + x.regs Reg.size + x.regs Reg.depth + 4)) :
    ∃ y, ExecWithin w locateChild x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.quarter = x.regs Reg.size / 4 ∧
      y.regs Reg.formA = x.regs Reg.scratch ∧
      y.regs Reg.formB = x.regs Reg.scratch + x.regs Reg.size / 4 ∧
      y.regs Reg.product = x.regs Reg.scratch + 2 * (x.regs Reg.size / 4) ∧
      y.regs Reg.childScratch = x.regs Reg.scratch + 3 * (x.regs Reg.size / 4) ∧
      y.regs Reg.childDepth = x.regs Reg.depth - 1 ∧
      ∀ i, i ≠ Reg.quarter → i ≠ Reg.formA → i ≠ Reg.formB → i ≠ Reg.product →
        i ≠ Reg.childScratch → i ≠ Reg.childDepth → y.regs i = x.regs i := by
  refine WP.exists_execWithin_preserves locateChild_preserves ?_
  wram_exec [locateChild, h1, h4]
  intro hregs
  wram_simp
  refine ⟨by omega, by omega, fun i h1' h2' h3' h4' h5' h6' => hregs i ?_⟩
  rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> contradiction

/-- Only current frame fields, its pointer, address scratch and dispatch tag change on push. -/
@[expose] def PushLocal (i : Fin 64) : Prop :=
  (32 ≤ i.val ∧ i.val ≤ 39) ∨ i = Reg.address ∨ i = Reg.tag

instance (i : Fin 64) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable ((32 ≤ i.val ∧ i.val ≤ 39) ∨ i = Reg.address ∨ i = Reg.tag))

private theorem push_preserves (phase : Fin 8) (i : Fin 64) :
    ¬PushLocal i → (push phase.val).Preserves i := by decide +kernel +revert

/-- Push a real child in twenty-six instructions, preserving the old parent fields except
its phase and writing the entire new frame. All child fields come from actual controller words. -/
theorem exec_push {w : ℕ} (phase : Fin 8) (x : Data 64)
    (h1 : x.regs Reg.one = 1) (h7 : x.regs Reg.frameWidth = 7)
    (hw : Fits w (x.regs Reg.frame + 14)) :
    ∃ y, ExecWithin w (push phase.val) x y 26 ∧
      y.regs Reg.frame = x.regs Reg.frame + 7 ∧
      y.regs Reg.inputA = x.regs Reg.formA ∧ y.regs Reg.inputB = x.regs Reg.formB ∧
      y.regs Reg.output = x.regs Reg.product ∧ y.regs Reg.scratch = x.regs Reg.childScratch ∧
      y.regs Reg.depth = x.regs Reg.childDepth ∧ y.regs Reg.size = x.regs Reg.quarter ∧
      y.regs Reg.phase = 0 ∧
      (∀ j : Fin 7, y.mem (y.regs Reg.frame + j.val) = y.regs (field j)) ∧
      y.mem (x.regs Reg.frame + 6) = phase.val ∧
      (∀ a, a < x.regs Reg.frame + 6 ∨ x.regs Reg.frame + 14 ≤ a → y.mem a = x.mem a) ∧
      ∀ i, ¬PushLocal i → y.regs i = x.regs i := by
  have hstore : storeFrame = storeRecord Reg.frame Reg.address Reg.one field := rfl
  refine WP.exists_execWithin_preserves (push_preserves phase) ?_
  unfold push pushArguments
  rw [hstore]
  wram_exec [h1, h7]
  refine WP.of_exec_spec
    (storeRecord_exec Reg.frame Reg.address Reg.one field _
      (by decide) (by decide)
      (by wram_simp; exact h1)
      (by wram_simp; exact hw.of_le (by omega))) ?_
  rintro y ⟨hymem, hymod, _, hyregs⟩
  wram_simp at hymem hymod
  have hfield_ne (j : Fin 7) : field j ≠ Reg.address := by revert j; decide
  have hyframe : y.regs Reg.frame = x.regs Reg.frame + 7 :=
    (hyregs Reg.frame (by decide)).trans (by wram_simp)
  refine ⟨by omega, fun hregs => ⟨hyframe,
    (hyregs Reg.inputA (by decide)).trans (by wram_simp),
    (hyregs Reg.inputB (by decide)).trans (by wram_simp),
    (hyregs Reg.output (by decide)).trans (by wram_simp),
    (hyregs Reg.scratch (by decide)).trans (by wram_simp),
    (hyregs Reg.depth (by decide)).trans (by wram_simp),
    (hyregs Reg.size (by decide)).trans (by wram_simp),
    (hyregs Reg.phase (by decide)).trans (by wram_simp), ?_, ?_, ?_, hregs⟩⟩
  · intro j
    rw [hymem, hyframe, writeWords_add_fin, hyregs (field j) (hfield_ne j)]
  · rw [hymod (x.regs Reg.frame + 6) (by simp only [Block.mem_footprint, Block.Owns]; omega),
      Function.update_self]
  · intro a ha
    rw [hymod a (by simp only [Block.mem_footprint, Block.Owns]; omega),
      Function.update_of_ne (by omega)]

end Cslib.Algorithms.WordRAM.Strassen
