/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.MatrixResidue
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Monomial
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Actual native padded coefficient-matrix cell

One cell executes its runtime division/remainder, actual spread-table reads and Morton
address arithmetic, both padding guards, real residue read when admitted, every coefficient
write and index increment. The table is constructed by the preceding native spread stage;
this internal execution theorem describes its current-state meaning for composition.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Exactly the row/column/scan/coefficient/address temporaries used by a matrix cell. -/
@[expose] def MatrixLocal (i : Fin 128) : Prop := 87 ≤ i.val ∧ i.val ≤ 97

instance (i : Fin 128) : Decidable (MatrixLocal i) :=
  inferInstanceAs (Decidable (87 ≤ i.val ∧ i.val ≤ 97))

private theorem matrixStep_preserves (transpose : Bool) (i : Fin 128) (hi : ¬MatrixLocal i) :
    (matrixStep transpose).Preserves i := by
  cases transpose <;> decide +kernel +revert

/-- Construct one complete padded p-coefficient cell from actual current source/table words.
All address, division, comparison, coefficient and control fits follow from a numerical
envelope; no matrix cell, residue answer, table lookup or running time is supplied by an oracle. -/
theorem exec_matrixStep {w n p k source destination table i : ℕ}
    (transpose : Bool) (x : Data 128)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hN : x.regs Reg.paddedSide = 2 ^ k) (hindex : x.regs Reg.index = i) (hi : i < 4 ^ k)
    (hsrc : x.regs Reg.residueSource = source) (hdst : x.regs Reg.destination = destination)
    (ht : x.regs Reg.spread = table)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (table + j) = Nat.Morton.spread j)
    (hw : Fits w (destination + 4 ^ k * p + table + 4 ^ k + 2 ^ k +
      source + n * n + p + 16)) :
    ∃ y, ExecWithin w (matrixStep transpose) x y (7 * p + 22) ∧
      y.regs Reg.index = i + 1 ∧
      (∀ j < p, y.mem (destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p + j) =
        if j = (if i / 2 ^ k < n ∧ i % 2 ^ k < n then x.mem (source +
          if transpose then i % 2 ^ k * n + i / 2 ^ k else i / 2 ^ k * n + i % 2 ^ k)
        else p) then 2 else 0) ∧
      (∀ d, (d < destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p ∨
        destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p + p ≤ d) →
        y.mem d = x.mem d) ∧
      ∀ r, ¬MatrixLocal r → y.regs r = x.regs r := by
  have hpos : 0 < 2 ^ k := by positivity
  have hsquare : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; rfl
  have hrlt : i / 2 ^ k < 2 ^ k :=
    (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa only [hsquare] using hi)
  have hclt : i % 2 ^ k < 2 ^ k := Nat.mod_lt i hpos
  have hzlt : Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) < 4 ^ k :=
    Nat.Morton.index_lt hrlt hclt
  have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hzlt)
  rw [Nat.succ_mul] at hmul
  refine WP.exists_execWithin_preserves (fun j hj => matrixStep_preserves transpose j hj) ?_
  unfold matrixStep
  wram_exec [hindex, hN]
  wram_call (exec_morton (k := k) _ (by wram_simp [h2]) (by wram_simp; exact hrlt)
    (by wram_simp; exact hclt) (by wram_simp [ht]; exact htable)
    (by wram_simp [ht]; exact hw.of_le (by omega))) with s ⟨sm, spos, sr⟩
  wram_simp at sm spos
  have smod : s.regs Reg.modulus = p := by regs_frame
  have sdst : s.regs Reg.destination = destination := by regs_frame
  wram_exec [spos, smod, sdst]
  have tsrc : s.regs Reg.residueSource = source := by regs_frame
  have tside : s.regs Reg.side = n := by regs_frame
  have trow : s.regs Reg.row = i / 2 ^ k := by regs_frame
  have tcol : s.regs Reg.column = i % 2 ^ k := by regs_frame
  wram_call (exec_matrixResidue transpose _
    (by wram_simp [tsrc, tside, smod]; exact hw.of_le (by omega))) with r ⟨rm, key, rr⟩
  wram_simp [tsrc, tside, smod, trow, tcol, sm] at rm key
  have rblock : r.regs Reg.block =
      destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p := by regs_frame
  have rmod : r.regs Reg.modulus = p := by regs_frame
  refine WP.seq ?_
  wram_call (exec_writeCoefficients r (by regs_frame) (by regs_frame) (by regs_frame)
    (by rw [rblock, rmod]; exact hw.of_le (by omega))) with s' ⟨values, memory, regs⟩
  have s'index : s'.regs Reg.index = i := by regs_frame
  have s'one : s'.regs Reg.one = 1 := by regs_frame
  wram_exec [s'index, s'one]
  intro hpres
  refine ⟨by wram_simp, ?_, ?_, hpres⟩
  · intro j hj
    have hv := values j (by simpa only [rmod] using hj)
    simpa only [Data.set_mem, rblock, key] using hv
  · intro d hd
    exact (memory d (by simpa only [rblock, rmod] using hd)).trans (congrFun rm d)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
