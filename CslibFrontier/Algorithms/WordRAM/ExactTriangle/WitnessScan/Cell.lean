/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WitnessScan.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged original-weight zero-sum test

The internal cell rule composes the actual two loads, their address calculations and both
existing signed additions. Its result is the exact sum of the three original weights; no
modular product or candidate certificate can make a nonzero original sum pass this test.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

/-- Actual signed verification of one original candidate vertex, with every address and
arithmetic instruction charged. The first partial sum must fit the next kernel's signed
source range; the complete initialized caller derives this from the original weight bound. -/
theorem exec_testVertex {w rb ra c : ℕ} {ab bc ac : ℤ} (x : Data 32)
    (hrowB : x.regs Reg.rowB = rb) (hrowA : x.regs Reg.rowA = ra)
    (hindex : x.regs Reg.index = c) (hwab : x.regs Reg.wab = Signed.encode ab)
    (hBC : x.mem (rb + c) = Signed.encode bc)
    (hAC : x.mem (ra + c) = Signed.encode ac)
    (haddr : Fits (w + 2) (rb + ra + c + 1))
    (hab : GenericRAM.Signed.Fits w ab) (hbc : GenericRAM.Signed.Fits w bc)
    (hac : GenericRAM.Signed.Fits w ac) (hpartial : GenericRAM.Signed.Fits w (ab + bc)) :
    ∃ y, ExecWithin (w + 2) testVertex x y 36 ∧
      y.regs Signed.result = Signed.encode (ab + bc + ac) ∧ y.mem = x.mem ∧
      ∀ i : Fin 32, 9 ≤ i.val → i ≠ Reg.address → y.regs i = x.regs i := by
  refine WP.exists_execWithin ?_
  unfold testVertex loadBC loadAC
  wram_exec [hrowB, hindex, hwab, hBC]
  wram_call (Signed.exec_add hab hbc _ (by wram_simp) (by wram_simp))
    with b ⟨bsum, bmem, bframe⟩
  change b.regs Signed.result = Signed.encode (ab + bc) at bsum
  wram_simp at bmem
  have bra : b.regs Reg.rowA = ra :=
    (bframe _ (Or.inr (by decide))).trans (by wram_simp [hrowA])
  have bindex : b.regs Reg.index = c :=
    (bframe _ (Or.inr (by decide))).trans (by wram_simp [hindex])
  have hAC' : b.mem (ra + c) = Signed.encode ac := bmem ▸ hAC
  wram_exec [bsum, bra, bindex, hAC']
  wram_call (Signed.exec_add hpartial hac _ (by wram_simp) (by wram_simp))
    with y ⟨ysum, ymem, yframe⟩
  wram_simp at ymem
  refine ⟨by decide, ysum, ymem.trans bmem, fun i hi hne => ?_⟩
  have h1 : i ≠ Signed.left := fun h => by subst h; exact absurd hi (by decide)
  have h2 : i ≠ Signed.right := fun h => by subst h; exact absurd hi (by decide)
  have hloadA : (b.set Signed.left (Signed.encode (ab + bc)) |>.set Reg.address (ra + c)
      |>.set Signed.right (Signed.encode ac)).regs i = b.regs i := by
    wram_simp [h1, h2, hne]
  have hloadB : (x.set Signed.left (Signed.encode ab) |>.set Reg.address (rb + c)
      |>.set Signed.right (Signed.encode bc)).regs i = x.regs i := by
    wram_simp [h1, h2, hne]
  exact (yframe i (Or.inr hi)).trans (hloadA.trans ((bframe i (Or.inr hi)).trans hloadB))

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
