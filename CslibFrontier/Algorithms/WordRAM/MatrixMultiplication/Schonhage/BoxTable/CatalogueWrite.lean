/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.DigitScan
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueState
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Charged native stores of box geometry

Both rejected and accepted slots execute a real directory store. Accepted slots also
write their three descriptor words at the actual computed compact rank. No zeroed
directory or precomputed compact-rank certificate is used by the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Scalar registers changed by the native stores and counter updates. -/
@[expose] def WriteLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.temporary ∨ i = Reg.count ∨ i = Reg.slot

instance (i : Fin registers) : Decidable (WriteLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.temporary ∨
    i = Reg.count ∨ i = Reg.slot))

/-- Execute the exact stores after the actual digit scan. -/
theorem exec_writeSlot {w L H D R s : ℕ} (x : Data registers)
    (hd : x.regs Reg.directory = D) (hr : x.regs Reg.records = R)
    (hs : x.regs Reg.slot = s) (hh : x.regs Reg.height = H)
    (hc : x.regs Reg.count = Nat.count (Eligible L H) s)
    (hcode : x.regs Reg.completion = recordCode L s)
    (he : x.regs Reg.stars = recordStars L s)
    (hp : x.regs Reg.population = population (recordCode L s) L)
    (hstride : x.regs Reg.starPower = recordStride L s)
    (h1 : x.regs Reg.one = 1) (h3 : x.regs Reg.three = 3) (h0 : x.regs Reg.nil = 0)
    (hfit : Fits w (D + R + 6 * (s + 1) + 12)) :
    ∃ y, ExecWithin w writeSlot x y 17 ∧
      y.mem = catalogueWrite L H D R s x.mem ∧ y.regs Reg.slot = s + 1 ∧
      y.regs Reg.count = Nat.count (Eligible L H) (s + 1) ∧
      (∀ i, ¬WriteLocal i → y.regs i = x.regs i) := by
  have hcnt := hc
  have hrc : Nat.count (Eligible L H) s ≤ s := Nat.count_le _
  suffices ∃ y, ExecWithin w writeSlot x y 17 ∧
      y.mem = catalogueWrite L H D R s x.mem ∧ y.regs Reg.slot = s + 1 ∧
      y.regs Reg.count = Nat.count (Eligible L H) (s + 1) by
    obtain ⟨y, hy, hm, hs', hc'⟩ := this
    exact ⟨y, hy, hm, hs', hc', fun i hi => hy.regs_eq (by unfold WriteLocal at hi; decide +revert)⟩
  unfold writeSlot emit
  wram_exec [*]
  · have hv : ¬Eligible L H s := fun h => (Nat.not_lt_of_ge h.2) hc
    wram_simp [catalogueWrite, hv, directoryWord, hcnt, Nat.count_succ_eq_count hv]
  · rename_i hlarge
    have hv : ¬Eligible L H s := fun h => (Nat.not_lt_of_ge h.1) hc
    wram_simp [catalogueWrite, hv, directoryWord, hcnt, Nat.count_succ_eq_count hv]
  · rename_i hlarge
    have hv : Eligible L H s := ⟨Nat.le_of_not_lt hc, Nat.le_of_not_lt hlarge⟩
    have hm3 : Nat.count (Eligible L H) s * 3 = 3 * Nat.count (Eligible L H) s :=
      Nat.mul_comm _ _
    refine ⟨?_, by wram_simp, by wram_simp [hcnt, Nat.count_succ_eq_succ_count hv]⟩
    simp only [Data.set_mem, Data.write_mem, catalogueWrite, hv, directoryWord, ↓reduceIte,
      Function.update_idem, hm3, Nat.add_assoc]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
