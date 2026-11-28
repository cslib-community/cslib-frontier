/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.NodeProgram
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Charged runtime layout and tag setup for one Chan–He node

## Main definitions

* `NodePacking.Prepared`: exact computed layout, encoded tags and fixed constants.

## Main results

* `NodePacking.exec_layout`: all address calculations are native instructions.

## References

These native setup proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

/-- The immutable caller arguments survive every phase of the node program. -/
def Parameters (x y : Data 64) : Prop :=
  ∀ i, 46 ≤ i.val ∧ i.val ≤ 55 → y.regs i = x.regs i

/-- Runtime arguments, computed bases, encoded tags and constants retained by every round.
Register 61 is the sole setup scratch register in this range. -/
def Frame (x y : Data 64) : Prop :=
  ∀ i, 46 ≤ i.val → i ≠ temporary → y.regs i = x.regs i

/-- The computed runtime layout and encoded tag constants. -/
def Prepared (L : Layout) (y : Data 64) : Prop :=
  y.regs scratch = L.scratch ∧ y.regs histogram = L.hist ∧ y.regs packed = L.packed ∧
    y.regs gap = 2 * L.gap ∧ y.regs padding = 4 * L.U + 2 ∧
    y.regs one = 1 ∧ y.regs four = 4

/-- A caller frame transports the prepared address/tag interface. -/
theorem Prepared.of_frame {L : Layout} {x y : Data 64} (hx : Prepared L x) (hr : Frame x y) :
    Prepared L y := by
  obtain ⟨hk, hh, hp, hg, hpad, h1, h4⟩ := hx
  exact ⟨(hr scratch (by decide) (by decide)).trans hk,
    (hr histogram (by decide) (by decide)).trans hh,
    (hr packed (by decide) (by decide)).trans hp,
    (hr gap (by decide) (by decide)).trans hg,
    (hr padding (by decide) (by decide)).trans hpad,
    (hr one (by decide) (by decide)).trans h1, (hr four (by decide) (by decide)).trans h4⟩

/-- A caller frame transports the immutable input/size interface. -/
theorem Parameters.of_frame {x y z : Data 64} (hy : Parameters x y) (hr : Frame y z) :
    Parameters x z := by
  intro i hi
  have hne : i ≠ temporary := by intro h; subst i; norm_num [temporary] at hi
  exact (hr i hi.1 hne).trans (hy i hi)

/-- Exact native arguments for writing the four-column padding pattern. -/
def PaddingReady (L : Layout) (y : Data 64) : Prop :=
  y.regs pdst = L.packed ∧ y.regs plen = L.N ∧
    y.regs pad0 = 120 * L.U + 80 ∧ y.regs pad1 = 16 * L.U + 10 ∧
    y.regs pad2 = 40 * L.U + 26 ∧ y.regs pad3 = 44 * L.U + 30

/-- Compute the disjoint addresses from the supplied runtime lengths and fresh base. -/
theorem exec_layout {w : ℕ} (x : Data 64) (hfit : Fits w (layout x).budget) :
    ∃ y, ExecWithin w layoutCode x y 12 ∧ Parameters x y ∧ y.mem = x.mem ∧
      y.regs packed = (layout x).packed ∧ y.regs scratch = (layout x).scratch ∧
      y.regs histogram = (layout x).hist ∧ y.regs one = 1 ∧ y.regs four = 4 ∧
      y.regs temporary = 3 := by
  have hpres : ∀ i : Fin 64, 46 ≤ i.val ∧ i.val ≤ 55 → layoutCode.Preserves i :=
    by decide +kernel
  have hb : Fits w (layout x).endpoint := hfit.of_le (layout x).bounds.1
  have hc : Fits w 16 := hfit.of_le (by have := (layout x).bounds.2.2; omega)
  dsimp only [layout, Layout.endpoint, Layout.hist, Layout.scratch, Layout.packed,
    Layout.total] at hb
  obtain ⟨y, he, hm, hp, hs, hh, h1, h4, h3⟩ :
      ∃ y, ExecWithin w layoutCode x y 12 ∧ y.mem = x.mem ∧
        y.regs packed = (layout x).packed ∧ y.regs scratch = (layout x).scratch ∧
        y.regs histogram = (layout x).hist ∧ y.regs one = 1 ∧ y.regs four = 4 ∧
        y.regs temporary = 3 := by
    refine WP.exists_execWithin ?_
    unfold layoutCode
    wram_exec
    refine ⟨by wram_simp, ?_, ?_, ?_, by wram_simp, by wram_simp, by wram_simp⟩
    · wram_simp; dsimp only [layout, Layout.packed, Layout.total]; omega
    · wram_simp; dsimp only [layout, Layout.scratch, Layout.packed, Layout.total]; omega
    · wram_simp
      dsimp only [layout, Layout.hist, Layout.scratch, Layout.packed, Layout.total]
      omega
  exact ⟨y, he, fun i hi => he.regs_eq (hpres i hi), hm, hp, hs, hh, h1, h4, h3⟩

/-- Compute encoded tags and signed padding through native arithmetic in sixteen instructions.
The single envelope supplies every intermediate fit, including the third-column subtraction. -/
theorem exec_constants {w : ℕ} (L : Layout) (x : Data 64)
    (hfit : Fits w L.budget) (hU : x.regs magnitude = L.U) (hN : x.regs groups = L.N)
    (hk : x.regs scratch = L.scratch) (hh : x.regs histogram = L.hist)
    (hp : x.regs packed = L.packed) (h1 : x.regs one = 1) (h4 : x.regs four = 4)
    (h3 : x.regs temporary = 3) :
    ∃ y, ExecWithin w constantsCode x y 16 ∧ Parameters x y ∧ y.mem = x.mem ∧
      Prepared L y ∧ PaddingReady L y := by
  have hpres : ∀ i : Fin 64, 46 ≤ i.val ∧ i.val ≤ 55 → constantsCode.Preserves i :=
    by decide +kernel
  have hb : Fits w (120 * L.U + 80) := hfit.of_le L.bounds.2.1
  obtain ⟨y, he, hm, hprep, hpad⟩ :
      ∃ y, ExecWithin w constantsCode x y 16 ∧ y.mem = x.mem ∧
        Prepared L y ∧ PaddingReady L y := by
    refine WP.exists_execWithin ?_
    unfold constantsCode
    wram_exec [hU, hN, hp, h1, h4, h3]
    refine ⟨by wram_simp,
      ⟨by wram_simp [hk], by wram_simp [hh], by wram_simp [hp],
        by wram_simp [Layout.gap]; omega, by wram_simp; omega,
        by wram_simp [h1], by wram_simp [h4]⟩,
      ⟨by wram_simp, by wram_simp, by wram_simp; omega, by wram_simp; omega,
        by wram_simp; omega, by wram_simp; omega⟩⟩
  exact ⟨y, he, fun i hi => he.regs_eq (hpres i hi), hm, hprep, hpad⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
