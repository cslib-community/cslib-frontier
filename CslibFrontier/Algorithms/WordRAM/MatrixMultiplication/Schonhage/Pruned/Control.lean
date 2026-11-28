/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native return and term-advance transitions

## Main results

* `PrunedQuery.exec_pop`: return to the parent's accumulation phase or terminate the root.
* `PrunedQuery.exec_advance`: store the incremented term counter in the actual parent frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by a return transition. -/
def PopLocal (i : Fin registers) : Prop := i = active ∨ i = level ∨ i = mode

instance (i : Fin registers) : Decidable (PopLocal i) :=
  inferInstanceAs (Decidable (i = active ∨ i = level ∨ i = mode))

/-- The return decision is the program's real comparison with zero. Both branches preserve
memory and all registers outside the three controller fields. -/
theorem exec_pop {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (hw : Fits w (x.regs level + 2)) :
    ∃ y, ExecWithin w pop x y 4 ∧ y.mem = x.mem ∧
      y.regs level = (if x.regs level = 0 then 0 else x.regs level - 1) ∧
      y.regs mode = (if x.regs level = 0 then x.regs mode else 2) ∧
      y.regs active = (if x.regs level = 0 then 0 else x.regs active) ∧
      (∀ i, ¬PopLocal i → y.regs i = x.regs i) := by
  have h2 : Fits w 2 := hw.of_le (by omega)
  have hd : Fits w (x.regs level - 1) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [pop, h0, h1, h2, hd]
  all_goals
    refine ⟨rfl, by wram_simp; simp [hc], by wram_simp; simp [hc], by wram_simp; simp [hc],
      fun i hi => ?_⟩
    simp only [PopLocal, not_or] at hi
    rcases hi with ⟨h1', h2', h3'⟩
    wram_simp

/-- Registers changed by advancing and storing a term counter. -/
def AdvanceLocal (i : Fin registers) : Prop := i = term ∨ i = address ∨ i = mode

instance (i : Fin registers) : Decidable (AdvanceLocal i) :=
  inferInstanceAs (Decidable (i = term ∨ i = address ∨ i = mode))

/-- Store a term already in its register and switch to dispatch, charging all four operations. -/
theorem exec_storeTerm {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w storeTerm x y 4 ∧ y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) (x.regs term) ∧
      (∀ i, i ≠ address → i ≠ mode → y.regs i = x.regs i) := by
  have hmode : Fits w 1 := hf.of_le (by omega)
  have hadd : Fits w (x.regs frame + 3) := hf.of_le (by omega)
  have hsub : x.regs frame + 4 - 1 = x.regs frame + 3 := by omega
  refine WP.exists_execWithin ?_
  wram_exec [storeTerm, h1, h4, hf, hmode, hadd, hsub]
  exact ⟨by wram_simp, by wram_simp, fun i ha hm => by wram_simp⟩

/-- The term increment, frame-word address computation, store and phase assignment take five
instructions. Only the fourth frame word changes in memory. -/
theorem exec_advance {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (ht : Fits w (x.regs term + 1))
    (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w advance x y 5 ∧ y.regs term = x.regs term + 1 ∧
      y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) (x.regs term + 1) ∧
      (∀ i, ¬AdvanceLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [advance, h1, ht]
  wram_call (exec_storeTerm _ (by wram_simp [h1]) (by wram_simp [h4]) (by wram_simp; exact hf))
    with y ⟨hmode, hmem, hregs⟩
  wram_simp at hmem
  refine ⟨by omega, by rw [hregs term (by decide) (by decide)]; wram_simp, hmode, hmem,
    fun i hi => ?_⟩
  simp only [AdvanceLocal, not_or] at hi
  rcases hi with ⟨h1', h2', h3'⟩
  rw [hregs i h2' h3']
  wram_simp

/-- Initialization uses the same actual frame store as advancement, with a zero term counter. -/
theorem exec_clearValuesFinish {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4) (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w clearValuesFinish x y 5 ∧ y.regs term = 0 ∧ y.regs mode = 1 ∧
      y.mem = Function.update x.mem (x.regs frame + 3) 0 ∧
      (∀ i, ¬AdvanceLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [clearValuesFinish]
  wram_call (exec_storeTerm _ (by wram_simp [h1]) (by wram_simp [h4]) (by wram_simp; exact hf))
    with y ⟨hmode, hmem, hregs⟩
  wram_simp at hmem
  refine ⟨by omega, by rw [hregs term (by decide) (by decide)]; wram_simp, hmode, hmem,
    fun i hi => ?_⟩
  simp only [AdvanceLocal, not_or] at hi
  rcases hi with ⟨h1', h2', h3'⟩
  rw [hregs i h2' h3']
  wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
