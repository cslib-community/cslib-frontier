/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Powers
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Ready
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native headers, powers and evaluator pointers

## Main results

* `PrunedQuery.exec_initialize`: load both actual headers, compute the encoding-array length,
  derive every evaluator pointer, and establish the ordinary register calling convention.

The prefix uses `4L+27` instructions, including its power loop. Its continuation is the existing
structured sequence rule, so composing it with evaluation gives the original fixed program.
This continuation lemma is an internal implementation API for the complete initialized-run
theorems in `Pruned.Flat` and `Pruned.Width`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Initialization derives all pointers from the two ordinary scalar headers. Its output
assertion contains no execution or fit fields; the charged native composition is proved here. -/
theorem exec_initialize {w L Q : ℕ} (x : Data registers) (hL : x.mem 1 = L)
    (hQ : x.mem 2 = Q) (hfit : Fits w (addressBound L Q)) :
    ∃ y, y.mem = x.mem ∧ KernelRegs L (scratchBase L Q) 3 (3 + 10 ^ L) y ∧
      y.regs queryCount = Q ∧ y.regs queries = 3 + 2 * 10 ^ L ∧
      y.regs output = outputBase L Q ∧ y.regs epoch = 0 ∧
      ∀ (tail : Code .standard registers) z T, ExecWithin w tail y z T →
        ExecWithin w (ram[ ⟪header⟫; ⟪powers⟫; ⟪parameters⟫; ⟪locate⟫; ⟪tail⟫ ])
          x z (4 * L + 27 + T) := by
  have hp : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hs : Fits w (3 + 10 ^ L + 10 ^ L + Q + Q) :=
    hfit.of_le (by rw [addressBound]; nlinarith only [hp])
  have hf {k : ℕ} (hk : k ≤ 3 + 10 ^ L + 10 ^ L + Q + Q := by omega) : Fits w k := hs.of_le hk
  let h := (((x.set address 1).set inputDepth L).set address 2).set queryCount Q
  have hheader : ExecWithin w header x h 4 := by
    wram_exec [header, hL, hQ, hf (k := 1), hf (k := 2)]
  obtain ⟨p, hpower, hpmem, hpL, hspan, _, hnil, hone, _, hten, hnine, hfour, _⟩ :=
    exec_powers h (by regs_frame) hfit
  have hpQ : p.regs queryCount = Q := by regs_frame
  let u := ((((((p.set arrayA 3).set arrayB (3 + 10 ^ L)).set queries (3 + 10 ^ L + 10 ^ L)).set
    output (3 + 10 ^ L + 10 ^ L + Q)).set scratch (3 + 10 ^ L + 10 ^ L + Q + Q)).set epoch 0)
  have hparameters : ExecWithin w parameters p u 6 := by
    wram_exec [parameters,
      hspan, hpQ, hf (k := 3), hf (k := 3 + 10 ^ L), hf (k := 3 + 10 ^ L + 10 ^ L),
      hf (k := 3 + 10 ^ L + 10 ^ L + Q), hs]
  have huL : u.regs inputDepth = L := by regs_frame
  have huspan : u.regs span = 10 ^ L := by regs_frame
  have hus : u.regs scratch = scratchBase L Q := by
    dsimp only [u]
    wram_simp
    simp only [scratchBase, outputBase, two_mul, Nat.add_assoc]
  obtain ⟨y, hlocate, hymem, hyf, hyl, hyv, hys, _⟩ := exec_locate u (by regs_frame)
    (by regs_frame)
    (hfit.of_le (by
      rw [hus, huL, huspan]
      unfold scratchBase outputBase addressBound
      nlinarith only [hp, Nat.le_mul_of_pos_right L (show 0 < 10 ^ L by positivity)]))
  refine ⟨y, hymem.trans hpmem, by regs_frame, by regs_frame, ?_, ?_, by regs_frame,
    fun tail z T htail =>
      (hheader.seq (hpower.seq (hparameters.seq (hlocate.seq htail)))).mono (by omega)⟩
  · exact (by regs_frame : y.regs queries = 3 + 10 ^ L + 10 ^ L).trans (by omega)
  · exact (by regs_frame : y.regs output = 3 + 10 ^ L + 10 ^ L + Q).trans
      (by unfold outputBase; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
