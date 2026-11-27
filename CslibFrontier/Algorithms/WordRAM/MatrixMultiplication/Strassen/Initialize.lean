/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Power.Rename
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame
import Mathlib.Tactic.FinCases
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual initialized Strassen root and power call

The existing native `Power.program` computes `4^L`; a real multiplication by p computes the
coefficient-array length. Actual additions locate the root frame, and all its fields are
stored. Only original numeric parameters occur in the admission bound. No power, stack
layout, initialized scratch or intermediate execution certificate is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Compute the runtime length, constants and explicit root frame in at most `4L+30`
instructions, including the actual power call and every frame store. -/
theorem exec_setup {w : ℕ} (x : Data 64)
    (hw : Fits w (x.regs Reg.scratch + x.regs Reg.modulus * 4 ^ x.regs Reg.depth +
      4 ^ x.regs Reg.depth + x.regs Reg.depth + 16)) :
    ∃ y, ExecWithin w setup x y (4 * x.regs Reg.depth + 30) ∧
      y.regs Reg.size = x.regs Reg.modulus * 4 ^ x.regs Reg.depth ∧
      y.regs Reg.frames = x.regs Reg.scratch + x.regs Reg.modulus * 4 ^ x.regs Reg.depth ∧
      y.regs Reg.frame = y.regs Reg.frames ∧ y.regs Reg.phase = 0 ∧ y.regs Reg.active = 1 ∧
      y.regs Reg.zero = 0 ∧ y.regs Reg.one = 1 ∧ y.regs Reg.four = 4 ∧
      y.regs Reg.frameWidth = 7 ∧
      (∀ i, i ∈ [Reg.inputA, Reg.inputB, Reg.output, Reg.scratch, Reg.depth, Reg.modulus] →
        y.regs i = x.regs i) ∧
      (∀ j : Fin 7, y.mem (y.regs Reg.frame + j.val) = y.regs (field j)) ∧
      ∀ a, a < y.regs Reg.frame ∨ y.regs Reg.frame + 7 ≤ a → y.mem a = x.mem a := by
  have hpow : 0 < 4 ^ x.regs Reg.depth := by positivity
  have h7 : Fits w 7 := hw.of_le (by omega)
  have hmul := Nat.mul_comm (4 ^ x.regs Reg.depth) (x.regs Reg.modulus)
  have hsize : Fits w (4 ^ x.regs Reg.depth * x.regs Reg.modulus) := by fits [hpow, hmul]
  have hframe_fit : Fits w (x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus) := by
    fits [hpow, hmul]
  apply WP.exists_execWithin
  unfold setup powerArguments locateRoot
  wram_exec
  refine WP.name fun r hr => ?_
  let f : Fin 5 → Fin 64 := Fin.castLE (by decide)
  wram_call (Power.exec_rename f (Fin.castLE_injective _) 4 (x.regs Reg.depth) (by decide) r
    (by simp +decide [hr, f, Power.base, Reg.powerBase, Reg.powerExponent])
    (by simp [hr, f, Power.exponent, Reg.powerExponent]) (hw.of_le (by omega)))
    with s ⟨hsvalue, _, _, hsmem, _, _, hframe⟩
  have hsval : s.regs Reg.powerValue = 4 ^ x.regs Reg.depth := hsvalue
  wram_exec * [hr]
  refine WP.name fun u hu => ?_
  wram_call (exec_storeFrame u (by rw [hu]; regs_frame)
    (by wram_simp [hu]; exact hw.of_le (by omega)))
    with y ⟨values, frame, regs⟩
  have hyframe : y.regs Reg.frame =
      x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus := by rw [hu] at *; regs_frame
  have hyframes : y.regs Reg.frames =
      x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus := by rw [hu] at *; regs_frame
  refine ⟨by omega, ?_, by simpa only [Nat.mul_comm] using hyframes, hyframe.trans hyframes.symm,
    by rw [hu] at *; regs_frame, by rw [hu] at *; regs_frame,
    by rw [hu, hr] at *; regs_frame, by rw [hu, hr] at *; regs_frame,
    by rw [hu, hr] at *; regs_frame, by rw [hu, hr] at *; regs_frame, ?_, ?_, ?_⟩
  · have : y.regs Reg.size = 4 ^ x.regs Reg.depth * x.regs Reg.modulus := by
      rw [hu] at *; regs_frame
    simpa only [Nat.mul_comm] using this
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [hu, hr] at *; regs_frame)
  · intro j
    rw [regs Reg.frame (by decide), values j, regs (field j) (by fin_cases j <;> decide)]
  · intro a ha
    have huframe : u.regs Reg.frame =
        x.regs Reg.scratch + 4 ^ x.regs Reg.depth * x.regs Reg.modulus := by wram_simp [hu]
    rw [frame a (by simpa only [hyframe, huframe] using ha)]
    simpa only [hu, hr, Data.set_mem] using congrFun hsmem a

end Cslib.Algorithms.WordRAM.Strassen
