/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Quadrant
public import CslibFrontier.Computability.WordRAM.Signed.ArrayArithmetic.Exec

/-!
# Native in-place Strassen product accumulation

The actual selected output quarter is both the first input and destination of the existing
signed vector loop. Its exact-alias theorem is essential here. The child product buffer is
disjoint; dirty words outside this one output quarter retain their previous values.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Add/subtract one actual child result in place, charging the selected-quadrant address,
all three argument copies, and the complete signed vector loop. -/
theorem exec_accumulate {w q t A B : ℕ} (subtract : Bool) (x : Data 64) (u v : ℕ → ℤ)
    (hq : x.regs Reg.quarter = q) (ht : t < 4)
    (hbound : GenericRAM.Signed.Fits w ((A + B : ℕ) : ℤ))
    (hu : ∀ j < q, (u j).natAbs ≤ A) (hv : ∀ j < q, (v j).natAbs ≤ B)
    (hout : ∀ j < q, x.mem (x.regs Reg.output + t * q + j) = encode (u j))
    (hprod : ∀ j < q, x.mem (x.regs Reg.product + j) = encode (v j))
    (hw : Fits (w + 2) (x.regs Reg.output + 4 * q + x.regs Reg.product + q + 8))
    (hsep : x.regs Reg.product + q ≤ x.regs Reg.output ∨
      x.regs Reg.output + 4 * q ≤ x.regs Reg.product) :
    ∃ y, ExecWithin (w + 2) (accumulate t subtract) x y (26 * q + 10) ∧
      (∀ j < q, y.mem (x.regs Reg.output + t * q + j) =
        encode (if subtract then u j - v j else u j + v j)) ∧
      (∀ a, a < x.regs Reg.output + t * q ∨ x.regs Reg.output + t * q + q ≤ a →
        y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqfit : Fits (w + 2) (x.regs Reg.output + 4 * x.regs Reg.quarter + 4) := by
    rw [hq]; fits
  have hquarter : t * q + q ≤ 4 * q := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht)
  apply WP.exists_execWithin
  unfold accumulate
  wram_call (exec_quadrant Reg.output Reg.operandA x (by decide) ht hqfit) with s ⟨hsm, hsrc, hsr⟩
  have hsa : s.regs Reg.operandA = x.regs Reg.output + t * q := by simpa only [hq] using hsrc
  wram_exec *
  refine WP.name fun z hz => ?_
  let f : Fin 16 → Fin 64 := Fin.castLE (by decide)
  have hza : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputA = x.regs Reg.output + t * q := by
    simpa +decide [hz, f, Data.comap, Reg.operandA, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.inputA] using hsa
  have hzb : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputB = x.regs Reg.product := by
    simp +decide [hz, f, Data.comap, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.inputB]
  have hzo : (z.comap f).regs Signed.ArrayArithmetic.Reg.output = x.regs Reg.output + t * q := by
    simp +decide [hz, f, Data.comap, Reg.operandB, Reg.target, Reg.length,
      Signed.ArrayArithmetic.Reg.output]
  have hzl : (z.comap f).regs Signed.ArrayArithmetic.Reg.length = q := by
    simp [hz, f, Data.comap, Reg.length, Signed.ArrayArithmetic.Reg.length]
  have hzm : (z.comap f).mem = x.mem := by simpa only [hz, Data.comap_mem, Data.set_mem] using hsm
  wram_call (Signed.ArrayArithmetic.exec subtract (z.comap f) u v hzl hbound hu hv
      (fun j hj => by rw [hzm, hza]; exact hout j hj)
      (fun j hj => by rw [hzm, hzb]; exact hprod j hj)
      (by rw [hza]; fits [hquarter]) (by rw [hzb]; fits) (by rw [hzo]; fits [hquarter])
      (Or.inr (Or.inr (hza.trans hzo.symm))) (by rw [hzb, hzo]; omega))
    renamed (Fin.castLE_injective _)
    with y ⟨⟨values, frame, _⟩, hframe⟩
  refine ⟨by omega, fun j hj => by simpa only [hzo] using values j hj,
    fun a ha => (frame a (by simpa only [hzo] using ha)).trans (congrFun hzm a), ?_⟩
  intro i hi htemp
  have hyi : y.regs i = z.regs i := hframe i (fun j hj => by
    have hv := congrArg Fin.val hj; change j.val = i.val at hv; omega)
  have hib : i ≠ Reg.operandB := Fin.ne_of_val_ne (by change i.val ≠ 10; omega)
  have hit : i ≠ Reg.target := Fin.ne_of_val_ne (by change i.val ≠ 11; omega)
  have hil : i ≠ Reg.length := Fin.ne_of_val_ne (by change i.val ≠ 12; omega)
  exact hyi.trans (by
    wram_simp [hz]
    exact hsr i (Fin.ne_of_val_ne (by change i.val ≠ 9; omega)) htemp)

end Cslib.Algorithms.WordRAM.Strassen
