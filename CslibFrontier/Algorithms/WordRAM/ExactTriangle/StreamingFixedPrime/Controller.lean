/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Program
import CslibFrontier.Computability.WordRAM.Record

/-!
# Charged one-slot controller setup and reclamation

The logical limit is read from the producer's total register before any pair is produced.
The slot is reclaimed by one native copy after verification; no memory is cleared.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM
open FixedPrime (recordBank)

private theorem setup_preserves : ∀ i : Fin 416, i.val < 400 → setup.Preserves i := by
  decide +kernel

/-- Read the total logical count and charge all five controller initialization instructions. -/
theorem exec_setup {w : ℕ} (x : Data 416) (h1 : Fits w 1) :
    ∃ y, ExecWithin w setup x y 5 ∧ y.mem = x.mem ∧
      y.regs FixedPrime.Reg.index = 0 ∧
      y.regs FixedPrime.Reg.limit = x.regs (producerBank Instances.total) ∧
      y.regs FixedPrime.Reg.found = 0 ∧ y.regs FixedPrime.Reg.scans = 0 ∧
      y.regs FixedPrime.Reg.one = 1 ∧
      ∀ j : Fin 416, j.val < 400 → y.regs j = x.regs j := by
  refine WP.exists_execWithin_preserves (fun j hj => setup_preserves j hj) ?_
  wram_exec [setup]
  intro hpres
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, hpres⟩

/-- Reclaim the slot by an actual charged heap copy, retaining every word and other register. -/
theorem exec_reset {w : ℕ} (x : Data 416) :
    ExecWithin w reset x
      (x.set (producerBank Instances.heap) (x.regs (producerBank Instances.output))) 1 :=
  ExecWithin.copy

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
