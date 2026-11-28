/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
import CslibFrontier.Computability.WordRAM.Record

/-!
# Actual seven-word Strassen stack access

The frame lemmas read and write actual memory via `Cslib.WordRAM.storeRecord` and
`Cslib.WordRAM.loadRecord`. They expose only internal composition APIs for the native controller
proof; a caller does not supply a frame layout or execution oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- The fixed order of the seven register fields stored in an explicit frame. -/
@[expose] def field : Fin 7 → Fin 64
  | 0 => Reg.inputA
  | 1 => Reg.inputB
  | 2 => Reg.output
  | 3 => Reg.scratch
  | 4 => Reg.depth
  | 5 => Reg.size
  | 6 => Reg.phase

/-- Store every current field, charge all seven stores and all seven address instructions,
and preserve memory outside exactly this frame. -/
theorem exec_storeFrame {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7)) :
    ∃ y, ExecWithin w storeFrame x y 14 ∧
      (∀ j : Fin 7, y.mem (x.regs Reg.frame + j.val) = x.regs (field j)) ∧
      (∀ a, a < x.regs Reg.frame ∨ x.regs Reg.frame + 7 ≤ a → y.mem a = x.mem a) ∧
      ∀ i, i ≠ Reg.address → y.regs i = x.regs i := by
  obtain ⟨y, hy, hymem, hymod, _, hyregs⟩ :=
    storeRecord_exec Reg.frame Reg.address Reg.one field x
      (by decide) (by decide) h1 (hfit.of_le (by omega))
  refine ⟨y, hy.within, fun j => by rw [hymem, writeWords_add_fin], fun a ha => ?_, hyregs⟩
  exact hymod a (by simp only [Block.mem_footprint, Block.Owns]; omega)

/-- Registers loaded by the actual frame-read block, including its address temporary. -/
@[expose] def LoadLocal (i : Fin 64) : Prop := i = Reg.address ∨ 32 ≤ i.val ∧ i.val ≤ 38

instance (i : Fin 64) : Decidable (LoadLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ 32 ≤ i.val ∧ i.val ≤ 38))

/-- Read every field from the actual current frame in fourteen instructions, without stores. -/
theorem exec_loadFrame {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7)) :
    ∃ y, ExecWithin w loadFrame x y 14 ∧ y.mem = x.mem ∧
      (∀ j : Fin 7, y.regs (field j) = x.mem (x.regs Reg.frame + j.val)) ∧
      ∀ i, ¬LoadLocal i → y.regs i = x.regs i := by
  obtain ⟨y, hy, hymem, hyfields, _, hyregs⟩ :=
    loadRecord_exec Reg.frame Reg.address Reg.one field x
      (by decide) (by decide) (by decide) (by decide) h1 (hfit.of_le (by omega))
  refine ⟨y, hy.within, hymem, hyfields, fun i hi => hyregs i ?_⟩
  rintro (rfl | ⟨j, rfl⟩)
  · exact hi (Or.inl rfl)
  · revert hi; revert j; decide

/-- Loading a frame just stored by the controller restores the same current parameters.
This assertion is produced by native setup/push and maintained by the node proof. -/
theorem exec_loadCurrent {w : ℕ} (x : Data 64) (h1 : x.regs Reg.one = 1)
    (hfit : Fits w (x.regs Reg.frame + 7))
    (hframe : ∀ j : Fin 7, x.mem (x.regs Reg.frame + j.val) = x.regs (field j)) :
    ∃ y, ExecWithin w loadFrame x y 14 ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.address → y.regs i = x.regs i := by
  obtain ⟨y, hy, hymem, hyregs⟩ :=
    loadRecord_exec_self Reg.frame Reg.address Reg.one field x
      (by decide) (by decide) (by decide) (by decide) h1 hframe (hfit.of_le (by omega))
  exact ⟨y, hy.within, hymem, hyregs⟩

end Cslib.Algorithms.WordRAM.Strassen
