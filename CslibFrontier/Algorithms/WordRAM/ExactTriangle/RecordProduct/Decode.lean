/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Kernel
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Actual record selection and depth recovery

These internal lemmas account for the actual original-header and six descriptor loads, every
stride/address calculation, and the existing floor-logarithm loop. The final producer client
derives each loaded word from its actual readback theorem.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

/-- The actual binary logarithm recovers twice the power-of-four exponent. -/
theorem log_two_four_pow (m : ℕ) : Nat.log 2 (4 ^ m) = 2 * m := by
  rw [show 4 ^ m = 2 ^ (2 * m) by rw [Nat.pow_mul], Nat.log_pow (by decide)]

private theorem logBank_injective : Function.Injective logBank := by
  intro i j h
  apply Fin.ext
  simpa only [logBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

private theorem log_preserves : ∀ i : Fin 320,
    i.val < 96 ∨ 100 ≤ i.val → logarithm.Preserves i := by decide +kernel

/-- The computed logarithm is read from the actual existing loop, with no logarithm input
certificate. Its charge is `8m+5` at a power of four. -/
theorem exec_logarithm {W m : ℕ} (x : Data 320)
    (hD : x.regs Reg.source = 4 ^ m) (hfit : Fits W (4 ^ m + 2 * m + 3)) :
    ∃ y, ExecWithin W logarithm x y (8 * m + 5) ∧
      y.regs Reg.destination = 2 * m ∧ y.mem = x.mem ∧
      ∀ i : Fin 320, i.val < 96 ∨ 100 ≤ i.val → y.regs i = x.regs i := by
  have harg : x.regs (logBank NatLog.arg) = 4 ^ m := hD
  have hlog : Nat.log 2 (x.regs (logBank NatLog.arg)) = 2 * m := by
    rw [harg, log_two_four_pow]
  obtain ⟨y, hy, hr, hm, -, -⟩ := NatLog.exec_rename logBank logBank_injective x
    (hfit.of_le (by omega)) (harg ▸ hfit.of_le (by omega)) (hlog ▸ hfit.of_le (by omega))
  refine ⟨y, ?_, hr.trans hlog, hm, fun i hi => hy.regs_eq (log_preserves i hi)⟩
  have he : 4 * Nat.log 2 (x.regs (logBank NatLog.arg)) + 5 = 8 * m + 5 := by omega
  simpa only [logarithm, he] using hy

/-- Read an actual six-word producer record at its computed ordinal. The input memory is
unchanged; arbitrary source words are loaded, rather than supplied as predecoded registers. -/
theorem exec_readRecord {W n D i out b : ℕ} (x : Data 320) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D)) + 6 ≤ b)
    (hv : ∀ k : Fin 6, x.mem (out + i * (6 + 2 * (n * D)) + k.val) = v k)
    (hfit : Fits W (b + 2 * (n * D) + D + n + 128)) :
    ∃ y, ExecWithin W readRecord x y 28 ∧ y.mem = x.mem ∧
      y.regs Reg.dimension = D ∧ y.regs Reg.size = n ∧
      y.regs Reg.area = n * D ∧ y.regs Reg.twiceArea = 2 * (n * D) ∧
      y.regs Reg.base = b ∧ y.regs Reg.record = out + i * (6 + 2 * (n * D)) ∧
      y.regs Reg.rho = v 0 ∧ y.regs Reg.piece = v 1 ∧ y.regs Reg.queries = v 2 ∧
      y.regs Reg.count = v 3 ∧ y.regs Reg.left = v 4 ∧ y.regs Reg.right = v 5 ∧
      y.regs Reg.source = D ∧ y.regs Reg.one = 1 ∧ y.regs Reg.two = 2 ∧
      y.regs Reg.nineteen = 19 ∧ y.regs Reg.four = 4 := by
  let r := out + i * (n * D + n * D + 6)
  have hmul : n * D + n * D + 6 = 6 + 2 * (n * D) := by omega
  have hv' : ∀ k : Fin 6, x.mem (r + k.val) = v k := by simpa only [r, hmul] using hv
  have hrec' : r + 6 ≤ b := by simpa only [r, hmul] using hrec
  have hv0 : x.mem r = v 0 := hv' 0
  have hv1 : x.mem (r + 1) = v 1 := hv' 1
  have hv2 : x.mem (r + 1 + 1) = v 2 := hv' 2
  have hv3 : x.mem (r + 1 + 1 + 1) = v 3 := hv' 3
  have hv4 : x.mem (r + 1 + 1 + 1 + 1) = v 4 := hv' 4
  have hv5 : x.mem (r + 1 + 1 + 1 + 1 + 1) = v 5 := hv' 5
  dsimp only [r] at hrec' hv0 hv1 hv2 hv3 hv4 hv5
  refine WP.exists_execWithin ?_
  unfold readRecord
  wram_exec [hi, hout, hb, hD, hn, hv0, hv1, hv2, hv3, hv4, hv5]
  wram_simp [hmul]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
