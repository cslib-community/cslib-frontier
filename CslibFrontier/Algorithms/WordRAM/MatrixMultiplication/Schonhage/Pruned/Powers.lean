/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Power.Rename
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Charged initialization and encoding-array size

## Main results

* `PrunedQuery.exec_powers`: compute `10^L` by renaming `Power.program` after the five
  retained constant initializations, preserving all caller parameters and memory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The scalar registers initialized or advanced by the power routine. -/
def PowersLocal (i : Fin registers) : Prop :=
  i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index

instance (i : Fin registers) : Decidable (PowersLocal i) :=
  inferInstanceAs (Decidable
    (i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index))

/-- The five-register power assignment is injective. -/
theorem powerRegisters_injective : Function.Injective powerRegisters := by decide

/-- The power routine charges its five constant initializations and the renamed `4*L+5`
`Power.program` execution. The only width premise is a bound on ordinary input-derived
natural numbers. -/
theorem exec_powers {w L Q : ℕ} (x : Data registers) (hL : x.regs inputDepth = L)
    (hbound : Fits w (addressBound L Q)) :
    ∃ y, ExecWithin w powers x y (4 * L + 10) ∧ y.mem = x.mem ∧
      y.regs inputDepth = L ∧ y.regs span = 10 ^ L ∧ y.regs index = L ∧
      y.regs nil = 0 ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs ten = 10 ∧
      y.regs nine = 9 ∧ y.regs frameWidth = 4 ∧
      (∀ i, ¬PowersLocal i → y.regs i = x.regs i) := by
  have hspan : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hscalar : L + 128 + 128 * 10 ^ L ≤ addressBound L Q := by
    have hm := Nat.mul_le_mul_left L hspan
    unfold addressBound
    nlinarith
  have hbase := hbound.of_le hscalar
  have h10 : Fits w 10 := hbase.of_le (by omega)
  have hfit_pow : Fits w (10 ^ L + L + 2) := hbase.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold powers powerSetup
  wram_exec [h10]
  wram_call (Power.exec_rename powerRegisters powerRegisters_injective 10 L (by decide) _
    (by change Data.regs _ ten = 10; wram_simp)
    (by change Data.regs _ inputDepth = L; wram_simp [hL]) hfit_pow)
    with y ⟨hv, hc, ho, hm, hb', hd', hframe⟩
  refine ⟨by omega, hm, hd', hv, hc, by regs_frame, ho, by regs_frame, hb', by regs_frame,
    by regs_frame, fun i hi => ?_⟩
  by_cases hid : i = inputDepth
  · subst hid
    exact (hd' : y.regs inputDepth = L).trans hL.symm
  · simp only [PowersLocal, not_or] at hi
    rcases hi with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    rw [hframe i fun j => by fin_cases j <;> simp [powerRegisters] <;> tauto]
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
