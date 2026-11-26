/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WitnessScan.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.StrideOmega

/-!
# Native interval-verifier initialization

The actual header caches one original weight and computes two original row pointers. Its
numeric address bound covers every intermediate product/sum, including empty intervals at
the one-past-end boundary. These are internal rules for composing the verifier loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

/-- Initialize the actual verifier in fifteen instructions, preserving the original arguments
and memory. In particular the weight is loaded from the original A–B array, not supplied as
an accepted modular candidate. -/
theorem exec_setup {W : ℕ} (A : Args) (x : Data 32) (v : ℤ)
    (hx : A.InRegisters x) (ha : A.a < A.n) (hb : A.b < A.n)
    (hc : A.first + A.length ≤ A.n)
    (hread : x.mem (A.ab + (A.a * A.n + A.b)) = Signed.encode v)
    (hfit : Fits W A.addressBound) :
    ∃ y, ExecWithin W setup x y 15 ∧ A.InRegisters y ∧ y.mem = x.mem ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧ y.regs Reg.found = 0 ∧
      y.regs Reg.index = 0 ∧ y.regs Reg.rowB = A.bc + A.b * A.n + A.first ∧
      y.regs Reg.rowA = A.ac + A.a * A.n + A.first ∧
      y.regs Reg.wab = Signed.encode v := by
  obtain ⟨hab, hbc, hac, hn, ha', hb', hf, hl⟩ := hx
  have hiab : A.a * A.n + A.b < A.n * A.n := by stride_omega
  have hrowB : A.b * A.n + A.first ≤ A.n * A.n := by stride_omega
  have hrowA : A.a * A.n + A.first ≤ A.n * A.n := by stride_omega
  have hread' : x.mem (A.a * A.n + A.b + A.ab) = Signed.encode v := by
    simpa only [Nat.add_comm] using hread
  dsimp only [Args.addressBound] at hfit
  refine WP.exists_execWithin ?_
  unfold setup
  wram_exec [hab, hbc, hac, hn, ha', hb', hf, hl, hread']
  unfold Args.InRegisters
  wram_simp [hab, hbc, hac, hn, ha', hb', hf, hl]
  exact ⟨by omega, by omega⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
