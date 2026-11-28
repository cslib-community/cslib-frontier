/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandHeader
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCount
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandRoot
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.BandBounds
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete computed scalar parameters for native bands

## Main results

* `BandPreparation.exec_countCode`: compute binomial count, block count and band count
  from actual scalar parameters, retaining the previously computed header layout.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Registers containing the persistent header and concrete layout. -/
def headerRegisters : Finset (Fin 96) :=
  {levels, inner, rows, columns, outerSize, masks, cells, leaves, prefixSize,
    snapshot, inverse, table, catalogue, zero, one, two, three, four, seven, ten}

/-- The concrete layout survives any native execution that preserves its scalar registers. -/
theorem headerPost_reframe {L m N : ℕ} {x y : Data 96} (hx : HeaderPost L m N x)
    (h : ∀ i ∈ headerRegisters, y.regs i = x.regs i) : HeaderPost L m N y := by
  regs_frame

/-- Persistent concrete layout and the additional scalar results actually computed by
the mask-count/root/band-count code. No fit or execution bound is bundled here. -/
structure BandParameters (L m N : ℕ) (x : Data 96) : Prop extends HeaderPost L m N x where
  /-- Computed floor square root of the binomial count. -/
  root : x.regs root = K0 L m
  /-- Number of selected subset masks. -/
  square : x.regs square = K0 L m * K0 L m
  /-- Computed number of shared bands per side. -/
  bands : x.regs bands = numBands L m N

/-- All scalar parameters retained throughout preparation and encoder calls. -/
def parameterRegisters : Finset (Fin 96) := headerRegisters ∪ {root, square, bands}

/-- Preserve the computed parameters by preserving their actual registers. -/
theorem parameters_reframe {L m N : ℕ} {x y : Data 96} (hx : BandParameters L m N x)
    (h : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) : BandParameters L m N y := by
  regs_frame

/-- A convenient local numerical bound, derived from the original global word budget. -/
theorem local_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (16 * (L + N + N * D m + 2 ^ L + 10 ^ L + 1)) := by
  apply hfit.of_le
  unfold wordBudget
  nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- Compute the root and band counts with the actual native loops. -/
theorem exec_countCode {w L m N : ℕ} (x : Data 96)
    (hx : HeaderPost L m N x) (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w countCode x y ((6 * L + 16) * 2 ^ L + 16) ∧
      BandParameters L m N y ∧ y.mem = x.mem := by
  have hl := local_fits hfit
  have hK : K L m ≤ 2 ^ L := Nat.choose_le_two_pow _ _
  have hsqrt : Nat.sqrt (K L m) ≤ 2 ^ L := (Nat.sqrt_le_self _).trans hK
  have hB : K0 L m * N0 L m ≤ 7 ^ L := bandSize_le_seven_pow L m
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  refine WP.exists_execWithin ?_
  unfold countCode bandCount
  wram_call (exec_countMasks L m x hx.fixed.levels hx.fixed.inner hx.masks hx.fixed.one
    hx.fixed.two (by fits)) with c ⟨hcount, _, hcmem, _⟩
  wram_call (exec_root (K L m)) with r ⟨hroot, hsquare, hrmem, _⟩
  have hroot0 : r.regs root = K0 L m := by simpa only [K0] using hroot
  have hdivle : (N + K0 L m * N0 L m - 1) / (K0 L m * N0 L m) ≤ N + K0 L m * N0 L m :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  wram_exec *
  refine ⟨by nlinarith, ⟨by regs_frame, ?_, ?_, ?_⟩, hrmem.trans hcmem⟩
  · wram_simp [hroot0]
  · wram_simp [hsquare, K0]
  · wram_simp [numBands, bandSize]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
