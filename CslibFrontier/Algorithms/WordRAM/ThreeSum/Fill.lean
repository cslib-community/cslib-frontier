/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Cell
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Memory

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Native matrix-building loop for Convolution-3SUM

This is a fixed native word-RAM program for one tripartite instance. Its parameters are supplied
in registers. Every row/column calculation, index calculation, guarded input read, store and loop
instruction is charged. The three matrices follow the input in disjoint blocks.

The construction directly adapts Anthropic's `convFillBody` and its prefix invariant at
[`formal-math@16a5ce4`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean).
The graph builder does not invoke an Exact Triangle solver.

## Main definitions

* `Fill.body`: one matrix cell and the loop-counter increment.
* `Fill.program`: initialize counters and fill all three matrices.

## Main results

* `Fill.exec`: the complete matrix builder with charged time and memory correctness.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Fill

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Register holding the number of cells in each matrix. -/
abbrev area : Fin 28 := 20
/-- Loop increment. -/
abbrev one : Fin 28 := 21

/-- Write all three weights at the current cell and advance the counter. -/
def body : Code .standard 28 := ram[
  ⟪Cell.step⟫; Cell.cell ← Cell.cell + one ]

/-- Initialize the counter and matrix area, then write each row-major cell. -/
def program : Code .standard 28 :=
  .seq (ram[ Cell.cell ← #0; one ← #1; area ← Cell.side * Cell.side ])
    (.loop (.lt Cell.cell area) body)

/-- Fill three disjoint matrices within `131t² + 5` native instructions, excluding the halt.
All matrix addresses and the one-past-end addresses fit target words. The signed index bound
and both signs of the filler fit the source width. The program keeps its input and parameters. -/
theorem exec {w : ℕ} (A : Args) (x : Data 28)
    (ht : x.regs Cell.side = A.t) (hs : x.regs Cell.inst = A.s)
    (hab : x.regs Cell.matAB = A.ab) (hbc : x.regs Cell.matBC = A.bc)
    (hac : x.regs Cell.matAC = A.ac) (hlen : x.regs Cell.len = A.N)
    (hbase : x.regs Cell.base = A.base) (hf : x.regs Cell.filler = encode A.filler)
    (hmem : ∀ i < A.N, x.mem (A.base + i) = encode (A.values i))
    (hidx : GenericRAM.Signed.Fits w ((2 * (A.t * A.t) + A.s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w A.filler) (hnF : GenericRAM.Signed.Fits w (-A.filler))
    (hμ : ∀ i < A.N, GenericRAM.Signed.Fits w (A.values i))
    (haddr : Fits (w + 2) (A.base + A.N))
    (habfit : Fits (w + 2) (A.ab + A.t * A.t))
    (hbcfit : Fits (w + 2) (A.bc + A.t * A.t))
    (hacfit : Fits (w + 2) (A.ac + A.t * A.t))
    (hbelow : A.base + A.N ≤ A.ab)
    (hABBC : A.ab + A.t * A.t ≤ A.bc) (hBCAC : A.bc + A.t * A.t ≤ A.ac) :
    ∃ y, ExecWithin (w + 2) program x y (131 * (A.t * A.t) + 5) ∧
      y.mem = A.filled x.mem (A.t * A.t) ∧
      y.regs Cell.side = A.t ∧ y.regs Cell.inst = A.s ∧
      y.regs Cell.matAB = A.ab ∧ y.regs Cell.matBC = A.bc ∧ y.regs Cell.matAC = A.ac ∧
      y.regs Cell.len = A.N ∧ y.regs Cell.base = A.base ∧
      y.regs Cell.filler = encode A.filler := by
  let P (i : Fin 28) : Prop := i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨
    (15 ≤ i.val ∧ i.val ≤ 19)
  let Inv (j : ℕ) (y : Data 28) : Prop :=
    (∀ i, P i → y.regs i = x.regs i) ∧ y.regs one = 1 ∧
    y.regs area = A.t * A.t ∧
    y.mem = A.filled x.mem j
  have hbody (y : Data 28) (hy : Inv (y.regs Cell.cell) y) (hlt : y.regs Cell.cell < A.t * A.t) :
      ∃ z, ExecWithin (w + 2) body y z 129 ∧ Inv (y.regs Cell.cell + 1) z ∧
        z.regs Cell.cell = y.regs Cell.cell + 1 := by
    obtain ⟨hr, ho, ha, hm⟩ := hy
    have hinput : ∀ i < A.N, y.mem (A.base + i) = encode (A.values i) := fun i hi => by
      rw [hm, A.input_filled x.mem _ hbelow (by omega) (by omega) hi]; exact hmem i hi
    have hinc : Fits (w + 2) (y.regs Cell.cell + 1) := hacfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    wram_exec [body]
    wram_call (Cell.exec_step y rfl
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame)
      hinput hlt hidx hF hnF hμ haddr (habfit.of_le (by omega))
      (hbcfit.of_le (by omega)) (hacfit.of_le (by omega)) hbelow (by omega))
      framed with v m ⟨hzmem, hzf, hzreg⟩
    wram_exec [ho]
    refine ⟨⟨?_, by wram_simp [ho], by wram_simp [ha], ?_⟩, by wram_simp⟩
    · intro i hi
      have hne : i ≠ Cell.cell := Fin.ne_of_val_ne (by dsimp only [P, Cell.cell] at hi ⊢; omega)
      rw [Data.set_regs_of_ne hne]
      by_cases hif : i = Cell.filler
      · subst i; wram_simp [hzf, hr _ hi]
      · have hiv : i.val ≠ 12 := fun hv => hif (Fin.ext hv)
        exact (hzreg i (by dsimp only [P] at hi; omega)).trans (hr i hi)
    · wram_simp
      rw [A.filled_succ x.mem hABBC hBCAC hlt, ← hm]
      simpa only [Args.valueAB, Args.valueBC, Args.valueAC] using hzmem
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [program, ht]
  wram_call (ExecWithin.loop_count Inv (fun _ hy => hy.2.2.1) hbody (by wram_simp; omega)
    ⟨fun i hi => by
      have hne : i ≠ area ∧ i ≠ one ∧ i ≠ Cell.cell := by
        dsimp only [P] at hi
        refine ⟨?_, ?_, ?_⟩ <;>
          (intro h; have := congrArg Fin.val h; norm_num [area, one, Cell.cell] at this; omega)
      wram_simp [hne.1, hne.2.1, hne.2.2],
      by wram_simp, by wram_simp, by wram_simp [Args.filled_zero]⟩)
    with y ⟨⟨hr, _, _, hm⟩, _⟩
  exact ⟨by wram_simp; omega, hm, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Fill
