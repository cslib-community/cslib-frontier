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
# Actual two-quadrant Strassen operand forms

Both source pointers are computed by native quadrant address blocks. The existing signed
array loop then reads, adds/subtracts and stores every coefficient. Original matrix bounds
imply operand fits; the output may be dirty. This internal composition lemma does not assume
the recursively computed matrix product or its execution/time contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Materialize a signed sum/difference of two actual matrix quarters in a disjoint buffer,
charging all address multiplication, argument copies and vector instructions. -/
theorem exec_arithmeticForm {w q t₁ t₂ A : ℕ} (base dst : Fin 64) (sign : ℤ)
    (x : Data 64) (u : ℕ → ℤ)
    (hb : 32 ≤ base.val) (hd : 32 ≤ dst.val)
    (hbt : base ≠ Reg.temporary) (hdt : dst ≠ Reg.temporary)
    (hq : x.regs Reg.quarter = q) (ht₁ : t₁ < 4) (ht₂ : t₂ < 4) (hsign : sign ≠ 0)
    (hbound : GenericRAM.Signed.Fits w ((A + A : ℕ) : ℤ))
    (hu : ∀ j < 4 * q, (u j).natAbs ≤ A)
    (hinput : ∀ j < 4 * q, x.mem (x.regs base + j) = encode (u j))
    (hw : Fits (w + 2) (x.regs base + 4 * q + x.regs dst + q + 8))
    (hsep : x.regs base + 4 * q ≤ x.regs dst ∨ x.regs dst + q ≤ x.regs base) :
    ∃ y, ExecWithin (w + 2) (form base dst t₁ t₂ sign) x y (26 * q + 12) ∧
      (∀ j < q, y.mem (x.regs dst + j) = encode
        (if sign < 0 then u (t₁ * q + j) - u (t₂ * q + j)
          else u (t₁ * q + j) + u (t₂ * q + j))) ∧
      (∀ a, a < x.regs dst ∨ x.regs dst + q ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 32 ≤ i.val → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hqfit : Fits (w + 2) (x.regs base + 4 * x.regs Reg.quarter + 4) := by
    rw [hq]; fits
  have hquarter (t : ℕ) (ht : t < 4) : t * q + q ≤ 4 * q := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right q (Nat.succ_le_of_lt ht)
  have hq₁ := hquarter t₁ ht₁
  have hq₂ := hquarter t₂ ht₂
  apply WP.exists_execWithin
  simp only [form, ite_eq_right hsign]
  wram_call (exec_quadrant base Reg.operandA x hbt ht₁ hqfit) with r ⟨hrmem, hra, hrr⟩
  have hrq : r.regs Reg.quarter = q := by regs_frame
  have hrbase : r.regs base = x.regs base :=
    hrr base (by intro he; subst base; contradiction) hbt
  wram_call (exec_quadrant base Reg.operandB r hbt ht₂
      (by simpa only [hrbase, hrq, hq] using hqfit))
    with s ⟨hsmem, hsb, hsr⟩
  have hsd : s.regs dst = x.regs dst :=
    (hsr dst (by intro he; subst dst; contradiction) hdt).trans
      (hrr dst (by intro he; subst dst; contradiction) hdt)
  have hsa : s.regs Reg.operandA = x.regs base + t₁ * q := by
    rw [hsr Reg.operandA (by decide) (by decide), hra, hq]
  have hsb' : s.regs Reg.operandB = x.regs base + t₂ * q := by simpa only [hrbase, hrq] using hsb
  wram_exec *
  refine WP.name fun z hz => ?_
  let f : Fin 16 → Fin 64 := Fin.castLE (by decide)
  have hza : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputA = x.regs base + t₁ * q := by
    simpa +decide [hz, f, Data.comap, Reg.target, Reg.length, Reg.operandA,
      Signed.ArrayArithmetic.Reg.inputA] using hsa
  have hzb : (z.comap f).regs Signed.ArrayArithmetic.Reg.inputB = x.regs base + t₂ * q := by
    simpa +decide [hz, f, Data.comap, Reg.target, Reg.length, Reg.operandB,
      Signed.ArrayArithmetic.Reg.inputB] using hsb'
  have hzo : (z.comap f).regs Signed.ArrayArithmetic.Reg.output = x.regs dst := by
    simp +decide [hz, f, Data.comap, Reg.target, Reg.length, Signed.ArrayArithmetic.Reg.output]
  have hzl : (z.comap f).regs Signed.ArrayArithmetic.Reg.length = q := by
    simp [hz, f, Data.comap, Reg.length, Signed.ArrayArithmetic.Reg.length]
  have hzm : (z.comap f).mem = x.mem := by
    simpa only [hz, Data.comap_mem, Data.set_mem] using hsmem.trans hrmem
  have hdisj (t : ℕ) (ht : t * q + q ≤ 4 * q) :
      x.regs base + t * q + q ≤ x.regs dst ∨ x.regs dst + q ≤ x.regs base + t * q ∨
        x.regs base + t * q = x.regs dst := by omega
  wram_call (Signed.ArrayArithmetic.exec
      (decide (sign < 0)) (z.comap f) (fun j => u (t₁ * q + j)) (fun j => u (t₂ * q + j))
      hzl hbound (fun _ hj => hu _ (by omega)) (fun _ hj => hu _ (by omega))
      (fun j hj => by rw [hzm, hza, Nat.add_assoc]; exact hinput _ (by omega))
      (fun j hj => by rw [hzm, hzb, Nat.add_assoc]; exact hinput _ (by omega))
      (by rw [hza]; fits [hq₁]) (by rw [hzb]; fits [hq₂]) (by rw [hzo]; fits)
      (by rw [hza, hzo]; exact hdisj t₁ hq₁)
      (by rw [hzb, hzo]; exact hdisj t₂ hq₂)) renamed (Fin.castLE_injective _)
    with y ⟨⟨values, frame, _⟩, hframe⟩
  refine ⟨by omega, fun j hj => by simpa only [hzo, decide_eq_true_eq] using values j hj,
    fun a ha => (frame a (by simpa only [hzo] using ha)).trans (congrFun hzm a),
    fun i hi htemp => ?_⟩
  have hyi : y.regs i = z.regs i := hframe i (fun j hj => by
    have hv := congrArg Fin.val hj; change j.val = i.val at hv; omega)
  have hit : i ≠ Reg.target := Fin.ne_of_val_ne (by change i.val ≠ 11; omega)
  have hil : i ≠ Reg.length := Fin.ne_of_val_ne (by change i.val ≠ 12; omega)
  exact hyi.trans (by
    wram_simp [hz]
    exact (hsr i (Fin.ne_of_val_ne (by change i.val ≠ 10; omega)) htemp).trans
      (hrr i (Fin.ne_of_val_ne (by change i.val ≠ 9; omega)) htemp))

end Cslib.Algorithms.WordRAM.Strassen
