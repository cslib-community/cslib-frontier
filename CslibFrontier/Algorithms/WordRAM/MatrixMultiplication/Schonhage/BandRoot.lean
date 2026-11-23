/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCount
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native integer square root for the band block size

## Main results

* `BandPreparation.exec_root`: reuse `NatSqrt.exec_rename` and one final multiplication to
  compute the ordinary natural square root and its square within `5 * Nat.sqrt k + 8`
  native instructions.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM

/-- The six-register square-root assignment is injective. -/
theorem rootRegisters_injective : Function.Injective rootRegisters := by decide

/-- Compute the floor square root and its square by renaming `NatSqrt.program` and charging one
final multiplication. The only intermediate bound is `4*k+4`, which covers `(sqrt k + 1)²`. -/
theorem exec_root {w : ℕ} (k : ℕ) (x : Data 96)
    (hk : x.regs count = k) (ho : x.regs one = 1) (hfit : Fits w (4 * k + 4)) :
    ∃ y, ExecWithin w rootCode x y (5 * Nat.sqrt k + 8) ∧
      y.regs root = Nat.sqrt k ∧ y.regs square = Nat.sqrt k * Nat.sqrt k ∧ y.mem = x.mem ∧
      (∀ i, i ≠ root → i ≠ square → i ≠ temporary → i ≠ limit → y.regs i = x.regs i) := by
  have hsq_le : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  refine WP.exists_execWithin ?_
  unfold rootCode
  wram_call (NatSqrt.exec_rename rootRegisters rootRegisters_injective x
    (by simpa only [rootRegisters, NatSqrt.arg, Matrix.cons_val_zero, hk] using hfit))
    with z ⟨hzroot, _, hzmem, hzone⟩
  have hpres (i : Fin 96) (hr : i ≠ root) (hs : i ≠ square) (ht : i ≠ temporary)
      (hl : i ≠ limit) (hone : i ≠ one) : z.regs i = x.regs i :=
    ‹ExecWithin _ _ _ z _›.regs_eq (by decide +revert)
  simp only [rootRegisters, NatSqrt.arg, NatSqrt.root, NatSqrt.one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hk] at *
  wram_exec *
  wram_simp [hzroot, hzmem]
  intro i hr hs ht hl
  wram_simp [hs]
  by_cases hone : i = one
  · subst hone; exact hzone.trans ho.symm
  · exact hpres i hr hs ht hl hone

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
