/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Compiler

/-!
# Compiled allocation

The allocator writes null pointer fields and undefined scalar fields into the next unused
record, preserves all existing records, and advances the allocation pointer. Its running time
depends only on the fixed record layout.
-/

public section

namespace Cslib.PointerMachine.WordRAM.Scalars

open Cslib.WordRAM (ExecWithin)

variable {M : Model} {L : Layout}

private theorem initialize_spec (base : Fin (regCount L))
    (hbase : base.val < L.ptrRegs + L.dataRegs + 2) (fields : List (ℕ × ℕ))
    (values : ℕ → ℕ) {w b : ℕ} (y : Cslib.WordRAM.Data (regCount L))
    (hb : y.regs base = b)
    (hfields : ∀ offset value, (offset, value) ∈ fields →
      Cslib.WordRAM.Fits w (b + offset) ∧ Cslib.WordRAM.Fits w value ∧
        value = values offset) :
    ∃ z, ExecWithin w (initializeFields base fields) y z (4 * fields.length + 1) ∧
      (∀ r : Fin (regCount L), r.val < L.ptrRegs + L.dataRegs + 2 →
        z.regs r = y.regs r) ∧
      (∀ offset value, (offset, value) ∈ fields → z.mem (b + offset) = value) ∧
      ∀ a, (∀ offset value, (offset, value) ∈ fields → a ≠ b + offset) →
        z.mem a = y.mem a := by
  induction fields generalizing y with
  | nil =>
    refine ⟨y, ?_, fun _ _ => rfl, by simp, fun _ _ => rfl⟩
    have he := ExecWithin.copy (B := .standard) (w := w) (x := y)
      (d := zeroReg L) (s := zeroReg L)
    simpa [initializeFields, Cslib.WordRAM.Data.set] using he
  | cons field rest ih =>
    obtain ⟨offset, value⟩ := field
    obtain ⟨haddr, hvalue, hval⟩ := hfields offset value (by simp)
    have hoff : Cslib.WordRAM.Fits w offset := haddr.of_le (by omega)
    have hba : base ≠ addrReg L := by simp [Fin.ext_iff]; omega
    have hab : addrReg L ≠ valueReg L := by simp [addrReg, valueReg, Fin.ext_iff]
    let y₁ := y.set (addrReg L) offset
    let y₂ := y₁.set (addrReg L) (b + offset)
    let y₃ := y₂.set (valueReg L) value
    let y₄ := y₃.write (b + offset) value
    have hframe (r : Fin (regCount L)) (hr : r.val < L.ptrRegs + L.dataRegs + 2) :
        y₄.regs r = y.regs r := by
      have hra : r ≠ addrReg L := by simp [Fin.ext_iff]; omega
      have hrv : r ≠ valueReg L := by simp [Fin.ext_iff]; omega
      simp [y₄, y₃, y₂, y₁, Cslib.WordRAM.Data.set, Cslib.WordRAM.Data.write,
        Function.update_of_ne hra, Function.update_of_ne hrv]
    obtain ⟨z, hz, hzr, hzm, hzo⟩ := ih y₄ ((hframe base hbase).trans hb)
      (fun o v hv => hfields o v (by simp [hv]))
    refine ⟨z, ?_, fun r hr => (hzr r hr).trans (hframe r hr), ?_, ?_⟩
    · have h₁ : ExecWithin (B := .standard) w (.op (.const (addrReg L) offset)) y y₁ 1 :=
        ExecWithin.const hoff
      have h₂ : ExecWithin w
          (.op (.bin .add (addrReg L) base (addrReg L))) y₁ y₂ 1 := by
        simpa [y₁, y₂, Cslib.WordRAM.Data.set, Function.update_of_ne hba, hb]
          using (ExecWithin.bin (w := w) (x := y₁) (f := .add)
            (d := addrReg L) (i := base) (j := addrReg L)
            (by simpa [y₁, Cslib.WordRAM.Data.set, Function.update_of_ne hba, hb] using haddr))
      have h₃ : ExecWithin (B := .standard) w (.op (.const (valueReg L) value)) y₂ y₃ 1 :=
        ExecWithin.const hvalue
      have h₄ : ExecWithin (B := .standard) w (.op (.store (addrReg L) (valueReg L))) y₃ y₄ 1 := by
        simpa [y₄, y₃, y₂, Cslib.WordRAM.Data.set, Function.update_of_ne hab]
          using (ExecWithin.store (B := .standard) (w := w) (x := y₃)
            (a := addrReg L) (s := valueReg L))
      exact (h₁.seq (h₂.seq (h₃.seq (h₄.seq hz)))).mono (by simp; omega)
    · intro o v hv
      rcases List.mem_cons.mp hv with he | hv
      · cases he
        by_cases hm : ∃ v, (offset, v) ∈ rest
        · obtain ⟨v, hv⟩ := hm
          exact (hzm offset v hv).trans ((hfields offset v (by simp [hv])).2.2.trans hval.symm)
        · rw [hzo (b + offset) (by
            intro o v hv he
            have ho : offset = o := by omega
            subst o
            exact hm ⟨v, hv⟩)]
          simp [y₄, Cslib.WordRAM.Data.write]
      · exact hzm o v hv
    · intro a ha
      rw [hzo a (fun o v hv => ha o v (by simp [hv]))]
      have hne := ha offset value (by simp)
      simp [y₄, y₃, y₂, y₁, Cslib.WordRAM.Data.set, Cslib.WordRAM.Data.write,
        Function.update_of_ne hne]

/-- The concrete allocator initializes a fresh node and preserves all existing records.
Only the resulting state's word bounds are needed, since they also bound the old free address. -/
theorem create_spec (S : Scalars M L) (r : Fin L.ptrRegs)
    {w : ℕ} {x : State M L} {y : Cslib.WordRAM.Data (regCount L)}
    (h : Repr S.encode x y)
    (hfit : Fits S.encode w ((Instr.create r).effect x)) :
    ∃ z, ExecWithin w (S.effect (.create r)) y z (S.effectTime (.create r)) ∧
      Repr S.encode ((Instr.create r).effect x) z := by
  have hnext : Cslib.WordRAM.Fits w (nodeAddr L (x.heap.length + 1)) := by
    simpa [Instr.effect] using hfit.free
  let y₀ := y.set (ptrReg L r) (nodeAddr L x.heap.length)
  have h₀ : Repr S.encode (x.setPtr r (some x.heap.length)) y₀ := h.setPtr r _
  have hr : (ptrReg L r).val < L.ptrRegs + L.dataRegs + 2 := by
    have := r.isLt; simp only [ptrReg]; omega
  have h₀r : y₀.regs (ptrReg L r) = nodeAddr L x.heap.length := by
    simp [y₀, Cslib.WordRAM.Data.set]
  obtain ⟨z, hz, hzr, hzm, hzo⟩ := initialize_spec (ptrReg L r) hr S.initialFields
    (fun f => if f < L.ptrFields then 0 else S.encode M.undefined) y₀ h₀r (by
      intro offset value hv
      simp only [initialFields, List.mem_append, List.mem_map, List.mem_range] at hv
      rcases hv with ⟨f, hf, he⟩ | ⟨f, hf, he⟩
      · have ho := congrArg Prod.fst he
        have hv := congrArg Prod.snd he
        dsimp only at ho hv
        subst offset
        subst value
        have hoff := ptrField_lt_stride (L := L) ⟨f, hf⟩
        refine ⟨hnext.of_le (cellAddr_lt (Nat.lt_succ_self _) hoff).le,
          Cslib.WordRAM.fits_zero _, ?_⟩
        simp [hf]
      · have ho := congrArg Prod.fst he
        have hv := congrArg Prod.snd he
        dsimp only at ho hv
        subst offset
        subst value
        have hoff := dataField_lt_stride (L := L) ⟨f, hf⟩
        refine ⟨hnext.of_le (cellAddr_lt (Nat.lt_succ_self _) hoff).le, ?_, ?_⟩
        · have hb := hfit.heapData Record.blank (by simp [Instr.effect]) ⟨f, hf⟩
          simpa [Record.blank] using hb
        · simp)
  let z₁ := z.set (addrReg L) (stride L)
  let z₂ := z₁.set (freeReg L) (nodeAddr L (x.heap.length + 1))
  have hfree : z.regs (freeReg L) = nodeAddr L x.heap.length :=
    (hzr _ (by simp [freeReg])).trans h₀.free
  have hfa : freeReg L ≠ addrReg L := by simp [freeReg, addrReg, Fin.ext_iff]
  have hstride : Cslib.WordRAM.Fits w (stride L) := hnext.of_le (by
    unfold nodeAddr
    have : stride L ≤ stride L * (x.heap.length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega)
  have hadd : nodeAddr L x.heap.length + stride L = nodeAddr L (x.heap.length + 1) := by
    simp [nodeAddr, Nat.mul_add, Nat.add_assoc]
  refine ⟨z₂, ?_, ?_⟩
  · have hc : ExecWithin (B := .standard) w (.op (.copy (ptrReg L r) (freeReg L))) y y₀ 1 := by
      simpa [y₀, h.free] using (ExecWithin.copy (B := .standard) (w := w) (x := y)
        (d := ptrReg L r) (s := freeReg L))
    have hs : ExecWithin (B := .standard) w (.op (.const (addrReg L) (stride L))) z z₁ 1 :=
      ExecWithin.const hstride
    have ha : ExecWithin w (.op (.bin .add (freeReg L) (freeReg L) (addrReg L)))
        z₁ z₂ 1 := by
      simpa [z₁, z₂, Cslib.WordRAM.Data.set, Function.update_of_ne hfa, hfree, hadd]
        using (ExecWithin.bin (w := w) (x := z₁) (f := .add)
          (d := freeReg L) (i := freeReg L) (j := addrReg L)
          (by simpa [z₁, Cslib.WordRAM.Data.set, Function.update_of_ne hfa, hfree, hadd]
            using hnext))
    exact (hc.seq (hz.seq (hs.seq ha))).mono (by simp [effectTime, initialFields]; omega)
  · refine h₀.append Record.blank ?_ ?_ ?_ ?_ ?_
    · intro s hsl hsf
      have hsa : s ≠ addrReg L := by simp [Fin.ext_iff]; omega
      simpa [z₂, z₁, Cslib.WordRAM.Data.set, Function.update_of_ne hsf,
        Function.update_of_ne hsa] using hzr s hsl
    · simp [z₂, Cslib.WordRAM.Data.set, State.setPtr]
    · intro a ha
      apply hzo a
      intro offset value _ he
      change a < nodeAddr L x.heap.length at ha
      omega
    · intro f
      exact hzm f.val 0 (by
        simp only [initialFields, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl ⟨f.val, f.isLt, rfl⟩)
    · intro f
      exact hzm (L.ptrFields + f.val) (S.encode M.undefined) (by
        simp only [initialFields, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨f.val, f.isLt, rfl⟩)

end Cslib.PointerMachine.WordRAM.Scalars
