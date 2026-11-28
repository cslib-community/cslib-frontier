/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Access
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Actual selected-coefficient read and accumulation

This internal stage reads the computed AB residue, computes its additive inverse modulo p,
loads the actual cyclic-product coefficient and decodes its nonnegative canonical word.
The complete counter derives this readback from its real residue and Strassen executions.
No instruction performs a free coefficient lookup, signed decoding or summation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The scan modifies only its result and the shared coordinate/address temporaries. -/
@[expose] def ScanLocal (j : Fin 128) : Prop := j = Reg.result ∨ 87 ≤ j.val ∧ j.val ≤ 97

instance (j : Fin 128) : Decidable (ScanLocal j) :=
  inferInstanceAs (Decidable (j = Reg.result ∨ 87 ≤ j.val ∧ j.val ≤ 97))

private theorem countStep_preserves (j : Fin 128) (hj : ¬ScanLocal j) :
    countStep.Preserves j := by decide +kernel +revert

/-- One actual selected coefficient, including the real zero/nonzero residue branch and
signed-to-unsigned division. The sum and all addresses fit by the displayed numerical bound. -/
theorem exec_countStep {w n p k i r value total : ℕ} (x : Data 128)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hi : x.regs Reg.index = i) (hlt : i < n * n) (hpadding : n ≤ 2 ^ k)
    (hr : x.mem (x.regs Reg.residueAB + i) = r) (hrlt : r < p)
    (hvalue : x.mem (x.regs Reg.matrixR + Nat.Morton.index (i / n) (i % n) * p +
      (if r = 0 then 0 else p - r)) = encode (value : ℤ))
    (hbound : value ≤ n) (hresult : x.regs Reg.result = total) (htotal : total ≤ i * n)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + x.regs Reg.residueAB + x.regs Reg.matrixR +
      4 ^ k * p + 4 ^ k + 2 ^ k + n * n * n + n * n + p + 16)) :
    ∃ y, ExecWithin w countStep x y 20 ∧ y.mem = x.mem ∧
      y.regs Reg.index = i + 1 ∧ y.regs Reg.result = total + value ∧
      ∀ j, ¬ScanLocal j → y.regs j = x.regs j := by
  have hnpos : 0 < n := by nlinarith
  have hrow : i / n < n := (Nat.div_lt_iff_lt_mul hnpos).mpr hlt
  have hcol : i % n < n := Nat.mod_lt _ hnpos
  have hposition := Nat.Morton.index_lt (hrow.trans_le hpadding) (hcol.trans_le hpadding)
  have hprod := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hposition)
  rw [Nat.succ_mul] at hprod
  have hsum : total + value ≤ n * n * n := by
    have he := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at he; omega
  have kv : encode (value : ℤ) / 2 = value := by simp [encode_div_two]
  refine WP.exists_execWithin_preserves (fun j hj => countStep_preserves j hj) ?_
  wram_exec [countStep, hi, hn]
  wram_call (exec_morton (k := k) _ (by wram_simp [h2])
    (by wram_simp; exact hrow.trans_le hpadding)
    (by wram_simp; exact hcol.trans_le hpadding)
    (by wram_simp; exact htable)
    (by wram_simp; exact hw.of_le (by omega))) with s ⟨sm, sp, sr⟩
  wram_simp at sm sp
  have sab : s.regs Reg.residueAB = x.regs Reg.residueAB := by regs_frame
  have si : s.regs Reg.index = i := by regs_frame
  have szero : s.regs Reg.zero = 0 := by regs_frame
  have smod : s.regs Reg.modulus = p := by regs_frame
  have smat : s.regs Reg.matrixR = x.regs Reg.matrixR := by regs_frame
  have stwo : s.regs Reg.two = 2 := by regs_frame
  have sone : s.regs Reg.one = 1 := by regs_frame
  have sres : s.regs Reg.result = total := by regs_frame
  by_cases hz : r = 0
  · simp only [hz, ↓reduceIte, Nat.add_zero] at hvalue
    wram_exec [sab, si, sm, hr, hz, szero, sp, smod, smat, hvalue, kv, stwo, sres, sone]
    exact fun hpres => ⟨sm, by wram_simp, by wram_simp, hpres⟩
  · simp only [hz, ↓reduceIte] at hvalue
    wram_exec [sab, si, sm, hr, hz, szero, sp, smod, smat, hvalue, kv, stwo, sres, sone]
    exact fun hpres => ⟨sm, by wram_simp, by wram_simp, hpres⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
