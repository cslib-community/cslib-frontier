/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Charged timestamp insertion for native child queries

## Main results

* `PrunedQuery.exec_emit`: one native membership test and optional unique suffix insertion,
  within nine instructions, with the complete memory update and register frame.

This kernel does not assume that a child request set was computed elsewhere. The surrounding
native scan supplies each tested suffix and uses the returned timestamp/list updates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Exactly the registers a timestamp insertion can modify. -/
def EmitLocal (i : Fin registers) : Prop :=
  i = address ∨ i = marker ∨ i = temporary ∨ i = childCount

instance (i : Fin registers) : Decidable (EmitLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = marker ∨ i = temporary ∨ i = childCount))

/-- Timestamp insertion performs its real load, comparison, optional stores and increment.
The result states the exact memory update even before a caller supplies array separation. -/
theorem exec_emit {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (hs : Fits w (x.regs stamps + x.regs suffix))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w emit x y 9 ∧
      y.regs childCount =
        (if x.mem (x.regs stamps + x.regs suffix) = x.regs epoch then
          x.regs childCount else x.regs childCount + 1) ∧
      y.mem =
        (if x.mem (x.regs stamps + x.regs suffix) = x.regs epoch then x.mem else
          Function.update
            (Function.update x.mem (x.regs childList + x.regs childCount) (x.regs suffix))
            (x.regs stamps + x.regs suffix) (x.regs epoch)) ∧
      (∀ i, ¬EmitLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  unfold emit
  wram_exec [h1, hs, hl, hn]
  all_goals
    refine ⟨by wram_simp; simp [hc], by wram_simp; simp [hc], fun i hi => ?_⟩
    simp only [EmitLocal, not_or] at hi
    rcases hi with ⟨h1', h2', h3', h4'⟩
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
