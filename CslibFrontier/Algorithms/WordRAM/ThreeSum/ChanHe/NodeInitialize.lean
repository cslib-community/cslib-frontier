/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.NodeSetup
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.NodeMemory
import CslibFrontier.Computability.WordRAM.Call

/-!
# Complete native initialization of a Chan–He node

## Main results

* `NodePacking.exec_initialize`: exact runtime layout, encoded constants and all `4N` padding
  writes, charged within `12N+33` native instructions.

## References

This native composition proof is original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

/-- All setup and padding are real instructions, starting from arbitrary old output memory. -/
theorem exec_initialize {w : ℕ} (x : Data 64) (hfit : Fits w (layout x).budget) :
    ∃ y, ExecWithin w initializeCode x y (12 * (layout x).N + 33) ∧ Parameters x y ∧
      Prepared (layout x) y ∧ y.mem = paddingMemory (layout x) x.mem := by
  set L := layout x
  obtain ⟨a, ha, har, ham, hap, hak, hah, ha1, ha4, ha3⟩ := exec_layout x hfit
  obtain ⟨b, hb, hbr, hbm, hready, hbd, hbn, hbp₀, hbp₁, hbp₂, hbp₃⟩ :=
    exec_constants L a hfit (har magnitude (by decide)) (har groups (by decide))
      hak hah hap ha1 ha4 ha3
  have hargs : Parameters x b := fun i hi => (hbr i hi).trans (har i hi)
  have hf4 : Fits w 4 := hfit.of_le (by have := L.bounds.2.2; omega)
  have hpend : Fits w ((b.comap paddingRegisters).regs Padding.dst +
      4 * (b.comap paddingRegisters).regs Padding.len) := by
    change Fits w (b.regs pdst + 4 * b.regs plen)
    rw [hbd, hbn]
    exact (hfit.of_le L.bounds.1).of_le (by
      dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
      omega)
  obtain ⟨y, hy, ⟨hcm, _⟩, hregs⟩ := ExecWithin.rename_post (f := paddingRegisters)
    (fun _ _ he => Fin.ext (congrArg (fun k : Fin 64 => k.val) he))
    (Padding.exec (b.comap paddingRegisters) hf4 hpend)
  have hframe : Frame b y := fun i _ _ => hregs i fun j he => by
    have := congrArg Fin.val he
    dsimp only [paddingRegisters] at this
    omega
  have hsteps : 12 + (16 + (12 * (b.comap paddingRegisters).regs Padding.len + 5)) ≤
      12 * L.N + 33 := by
    rw [show (b.comap paddingRegisters).regs Padding.len = L.N from hbn]
    omega
  refine ⟨y, (ha.seq (hb.seq hy)).mono hsteps, hargs.of_frame hframe, hready.of_frame hframe, ?_⟩
  simp only [Data.comap_mem, hbm, ham] at hcm
  rw [hcm]
  change Padding.memory x.mem (b.regs pdst) (b.regs pad0) (b.regs pad1) (b.regs pad2)
    (b.regs pad3) (b.regs plen) = _
  rw [hbd, hbn, hbp₀, hbp₁, hbp₂, hbp₃]
  rfl

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
