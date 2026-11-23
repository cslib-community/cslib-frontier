/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Host.Loop
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Caller-owned Convolution-3SUM input and workspace

The caller supplies raw length, magnitude, input pointer and matrix-workspace pointer in the
existing host registers. Initialization reuses the existing square-root and layout code without
reading header zero. The input pointer is restored before the unchanged instance loop runs.

## Main definitions

* `prepareAt`: prepare the actual caller-owned source and matrix blocks.

## Main results

* `exec_prepare_at`: charged setup with exact parameters and a complete memory frame.

These native ABI composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM

/-- Saved caller input pointer; the existing layout and square-root banks do not change it. -/
abbrev savedSource : Fin 64 := 50

/-- Adapt the existing adjacent-block layout to the caller's chosen matrix start. -/
def callerSetup : Code .standard 64 := ram[
  savedSource ← base; base ← matAB - len; one ← #1; sqrtArg ← len ]

/-- Restore the actual source pointer after computing the caller's matrix layout. -/
def restoreSource : Code .standard 64 := ram[ base ← savedSource ]

/-- Initialize from actual register arguments, without touching any memory cell. -/
def prepareAt : Code .standard 64 :=
  .seq callerSetup (.seq (NatSqrt.program.rename sqrtRegisters) (.seq layout restoreSource))

/-- Every source/layout operation is charged. The source and all other caller memory are kept. -/
theorem exec_prepare_at {w N U src workspace : ℕ} (x : Data 64)
    (hN : x.regs len = N) (hU : x.regs upper = U)
    (hb : x.regs base = src) (hab : x.regs matAB = workspace)
    (hbelow : src + N ≤ workspace)
    (hsize : Fits w (workspace + 3 * (sideLength N * sideLength N)))
    (hfill : Fits w (4 * U + 2)) (hsqrt : Fits w (4 * N + 4)) :
    ∃ y, ExecWithin w prepareAt x y (5 * Nat.sqrt N + 24) ∧
      ParametersAt N U src workspace y ∧ y.regs inst = 0 ∧ y.regs found = 0 ∧
      y.mem = x.mem := by
  have hd : Fits w (workspace - N) := hsize.of_le (by omega)
  have h1 : Fits w 1 := hfill.of_le (by omega)
  have hw : N + (workspace - N) = workspace := by omega
  have hsi : sqrtRegisters.Injective := fun i j h => by
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [sqrtRegisters] at this
    omega
  refine WP.exists_execWithin ?_
  unfold prepareAt callerSetup restoreSource
  wram_exec [hb, hab, hN, h1]
  wram_call (NatSqrt.exec _ (by wram_simp [sqrtRegisters, NatSqrt.arg]; exact hsqrt))
    canonical hsi with s ⟨hsr, _, hsm, _⟩
  refine WP.seq ?_
  wram_call (exec_layout_at (N := N) (U := U) (src := workspace - N) _
    (by wram_simp [hN]) (by wram_simp [hU]) (by wram_simp) (by wram_simp)
    (by wram_simp [sqrtRegisters, NatSqrt.root, hsr, NatSqrt.arg])
    (by simpa only [hw] using hsize) hfill) framed with v m ⟨hp, hi, hf, hcm⟩
  wram_exec
  rw [hw] at hp
  refine ⟨?_, by wram_simp [hi], by wram_simp [hf], by wram_simp [hcm, hsm]⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := hp
  constructor
  all_goals first | (wram_simp; done) | rwa [Data.set_regs_of_ne (by decide)]

end Cslib.Algorithms.WordRAM.ThreeSum.Host
