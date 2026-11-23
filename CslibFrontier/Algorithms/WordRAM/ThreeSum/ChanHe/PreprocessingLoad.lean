/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingEntries
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Native frontend descriptor loads

The controller executes all six memory reads and the fuel copy. The semantic entry is obtained
from the existing frontend output relation, including empty compact arrays.

## Main results

* `loadRoot_exec`: exact native descriptor loading, charged execution and memory/register frame.

These representation and native execution proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- A descriptor load changes only the seven current-record slots and its address scratch. -/
theorem loadRoot_preserves : ∀ i : Fin 128,
    (i.val < 64 ∨ 71 ≤ i.val) → i ≠ address → loadRoot.Preserves i := by decide

/-- Execute all descriptor arithmetic, six native memory reads and the runtime fuel copy. -/
theorem loadRoot_exec {w U f t : ℕ} {l : Frontend.Layout} {rs : List (ℕ × ℕ)}
    (x : Data 128) (hx : x.Bounded w) (ht : t < l.count)
    (hc : x.regs current = t) (hd : x.regs descriptors = l.descriptors)
    (hf : x.regs levels = f) (hs : x.regs stride = 6) (ho : x.regs one = 1)
    (hfit : Fits w (l.descriptors + 6 * t + 5))
    (houtput : Frontend.Output l U rs x.mem) :
    ∃ y, Exec w loadRoot x y 14 ∧ (entry l U f rs t).Loaded y ∧ y.mem = x.mem ∧
      ∀ i : Fin 128, (i.val < 64 ∨ 71 ≤ i.val) → i ≠ address → y.regs i = x.regs i := by
  have ha' (k : ℕ) (hk : k ≤ 5) : Fits w (l.descriptors + (t * 6 + k)) :=
    hfit.of_le (by omega)
  have hbase : Fits w (l.descriptors + t * 6) := by
    simpa only [Nat.add_zero] using ha' 0 (by decide)
  have hmul : Fits w (t * 6) := hfit.of_le (by omega)
  have hF : Fits w f := hf ▸ hx.1 levels
  have hread (j : Fin 3) := houtput (3 * t + j.val) (entry_slot ht j)
  have h₀ := hread 0
  have h₁ := hread 1
  have h₂ := hread 2
  have ha₀ : l.descriptors + 2 * (3 * t + 0) = l.descriptors + t * 6 := by omega
  have ha₁ : l.descriptors + 2 * (3 * t + 1) = l.descriptors + (t * 6 + 2) := by omega
  have ha₂ : l.descriptors + 2 * (3 * t + 2) = l.descriptors + (t * 6 + 4) := by omega
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, ha₀, ha₁, ha₂] at h₀ h₁ h₂
  obtain ⟨y, he, hy⟩ :
      ∃ y, Exec w loadRoot x y 14 ∧ (entry l U f rs t).Loaded y ∧ y.mem = x.mem := by
    refine WP.Exact.exists_exec ?_
    unfold loadRoot
    wram_exec [hc, hd, hf, hs, ho, hmul, hbase, hF, hx.2, Nat.add_assoc,
      ha' 1 (by decide), ha' 2 (by decide), ha' 3 (by decide), ha' 4 (by decide),
      ha' 5 (by decide)]
    refine ⟨⟨by wram_simp [entry], fun j => ?_, fun j => ?_⟩, by wram_simp⟩
    · fin_cases j <;>
        (wram_simp [entry, Traversal.arraySource, Traversal.slot, Nat.add_assoc];
          first | exact h₀.2.1 | exact h₁.2.1 | exact h₂.2.1)
    · fin_cases j <;>
        (wram_simp [entry, Traversal.arrayLength, Traversal.slot, List.length_map,
          Nat.add_assoc]; first | exact h₀.1 | exact h₁.1 | exact h₂.1)
  exact ⟨y, he, hy.1, hy.2, fun i hi hj => he.within.regs_eq (loadRoot_preserves i hi hj)⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
