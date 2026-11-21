/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Allocation

/-!
# Correctness of compiled pointer-machine instructions

Each instruction's memory and register effect is implemented by its compiled word-RAM code.
Scalar implementations discharge only scalar operations; the pointer-access and allocation
proofs use the explicit memory representation.
-/

public section

namespace Cslib.PointerMachine.WordRAM

open Cslib.WordRAM (Code ExecWithin)

variable {M : Model} {L : Layout}

namespace Scalars

private theorem nop_spec {w : ℕ} (y : Cslib.WordRAM.Data (regCount L)) :
    ExecWithin w (.op (.copy (zeroReg L) (zeroReg L)) : Code .standard _) y y 1 := by
  simpa [Cslib.WordRAM.Data.set] using
    (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := zeroReg L) (s := zeroReg L))

private theorem access_spec {e : M.Value ↪ ℕ} {w : ℕ} {x target : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (h : Repr e x y) (hv : x.Valid)
    (hf : Fits e w x) (b : Fin L.ptrRegs) (offset : ℕ) (ho : offset < stride L)
    (body : Code .standard (regCount L))
    (hnull : x.ptr b = none → Repr e target y)
    (hbody : ∀ a n, x.ptr b = some a → x.heap[a]? = some n →
      ∀ z, Repr e x z → z.regs (ptrReg L b) + z.regs (addrReg L) = cellAddr L a offset →
        Cslib.WordRAM.Fits w (cellAddr L a offset) →
        ∃ z', ExecWithin w body z z' 2 ∧ Repr e target z') :
    ∃ z, ExecWithin w (access (ptrReg L b) offset body) y z 5 ∧ Repr e target z := by
  cases hp : x.ptr b with
  | none =>
    refine ⟨y, (ExecWithin.branch_pos ?_ (nop_spec y)).mono (by omega), hnull hp⟩
    simp [Cslib.WordRAM.Cond.Holds, h.ptr, h.zero, hp, ptrWord]
  | some a =>
    have ha := hv.1 b a hp
    have hn : x.heap[a]? = some (x.heap[a]'ha) := List.getElem?_eq_getElem ha
    have hoff := (hf.cellAddr ha ho).of_le (Nat.le_add_left offset (nodeAddr L a))
    have he := ExecWithin.const (B := .standard) (d := addrReg L) (x := y) hoff
    have hz := h.scratch (addrReg L) (by simp) offset
    have haddr : (y.set (addrReg L) offset).regs (ptrReg L b) +
        (y.set (addrReg L) offset).regs (addrReg L) = cellAddr L a offset := by
      rw [hz.ptr]
      simp [hp, ptrWord, cellAddr]
    obtain ⟨z', he', hz'⟩ := hbody a _ hp hn _ hz haddr (hf.cellAddr ha ho)
    refine ⟨z', ExecWithin.branch_neg ?_ (he.seq he'), hz'⟩
    simp [Cslib.WordRAM.Cond.Holds, h.ptr, h.zero, hp, ptrWord, nodeAddr]

/-- The compiled effect performs the source instruction, within its explicit instruction bound.
For a scalar branch it also leaves the predicate result in the temporary value register. -/
theorem effect_correct (S : Scalars M L) (i : Instr M L) {w : ℕ} {x : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (hv : x.Valid) (h : Repr S.encode x y)
    (hf : Fits S.encode w x) (hf' : Fits S.encode w (i.effect x)) (hs : S.Safe w x i) :
    ∃ z, ExecWithin w (S.effect i) y z (S.effectTime i) ∧
      Repr S.encode (i.effect x) z ∧
      (match i with
      | .ifTest p a b _ => z.regs (valueReg L) = if M.evalTest p (x.data a) (x.data b) then 1 else 0
      | _ => True) := by
  cases i with
  | null r =>
    refine ⟨_, ?_, h.setPtr r none, trivial⟩
    simpa only [effect, effectTime, h.zero, ptrWord] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := ptrReg L r) (s := zeroReg L))
  | movePtr r s =>
    refine ⟨_, ?_, h.setPtr r (x.ptr s), trivial⟩
    simpa only [effect, effectTime, h.ptr] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := ptrReg L r) (s := ptrReg L s))
  | moveData r s =>
    refine ⟨_, ?_, h.setData r (x.data s), trivial⟩
    simpa only [effect, effectTime, h.data] using
      (ExecWithin.copy (B := .standard) (w := w) (x := y) (d := dataReg L r) (s := dataReg L s))
  | loadPtr r f b =>
    have ho : f.val < stride L := ptrField_lt_stride f
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b f.val ho
      (Cslib.WordRAM.readAt (addrReg L) (ptrReg L r) (ptrReg L b) (addrReg L))
      (target := (Instr.loadPtr r f b).effect x) (by
        intro hp; simpa [Instr.effect, State.deref, hp] using h) (by
        intro a n hp hn z hz haddr hfit
        have hz' := hz.scratch (addrReg L) (by simp) (cellAddr L a f.val)
        have he := (Cslib.WordRAM.readAt_exec (w := w) (x := z)
          (tmp := addrReg L) (dst := ptrReg L r) (ptr := ptrReg L b) (idx := addrReg L)
          (by rwa [haddr])).within
        rw [haddr, hz.heapPtr a n hn f] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.deref, hp, hn] using hz'.setPtr r (n.ptr f))
    exact ⟨z, he, hz, trivial⟩
  | loadData r f b =>
    have ho : L.ptrFields + f.val < stride L := dataField_lt_stride f
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b (L.ptrFields + f.val) ho
      (Cslib.WordRAM.readAt (addrReg L) (dataReg L r) (ptrReg L b) (addrReg L))
      (target := (Instr.loadData r f b).effect x) (by
        intro hp; simpa [Instr.effect, State.deref, hp] using h) (by
        intro a n hp hn z hz haddr hfit
        have hz' := hz.scratch (addrReg L) (by simp) (cellAddr L a (L.ptrFields + f.val))
        have he := (Cslib.WordRAM.readAt_exec (w := w) (x := z)
          (tmp := addrReg L) (dst := dataReg L r) (ptr := ptrReg L b) (idx := addrReg L)
          (by rwa [haddr])).within
        rw [haddr, hz.heapData a n hn f] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.deref, hp, hn] using hz'.setData r (n.data f))
    exact ⟨z, he, hz, trivial⟩
  | storePtr f b r =>
    have ho : f.val < stride L := ptrField_lt_stride f
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b f.val ho
      (Cslib.WordRAM.writeAt (addrReg L) (ptrReg L b) (addrReg L) (ptrReg L r))
      (target := (Instr.storePtr f b r).effect x) (by
        intro hp; simpa [Instr.effect, State.modify, hp] using h) (by
        intro a n hp hn z hz haddr hfit
        have hz' := hz.scratch (addrReg L) (by simp) (cellAddr L a f.val)
        have he := (Cslib.WordRAM.writeAt_exec (w := w) (x := z)
          (tmp := addrReg L) (ptr := ptrReg L b) (idx := addrReg L) (src := ptrReg L r)
          (by simp [Fin.ext_iff]; omega) (by rwa [haddr])).within
        rw [haddr, hz.ptr r] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.modify, hp] using hz'.writePtr a f (x.ptr r))
    exact ⟨z, he, hz, trivial⟩
  | storeData f b r =>
    have ho : L.ptrFields + f.val < stride L := dataField_lt_stride f
    obtain ⟨z, he, hz⟩ := access_spec h hv hf b (L.ptrFields + f.val) ho
      (Cslib.WordRAM.writeAt (addrReg L) (ptrReg L b) (addrReg L) (dataReg L r))
      (target := (Instr.storeData f b r).effect x) (by
        intro hp; simpa [Instr.effect, State.modify, hp] using h) (by
        intro a n hp hn z hz haddr hfit
        have hz' := hz.scratch (addrReg L) (by simp) (cellAddr L a (L.ptrFields + f.val))
        have he := (Cslib.WordRAM.writeAt_exec (w := w) (x := z)
          (tmp := addrReg L) (ptr := ptrReg L b) (idx := addrReg L) (src := dataReg L r)
          (by simp [Fin.ext_iff]; omega) (by rwa [haddr])).within
        rw [haddr, hz.data r] at he
        refine ⟨_, he, ?_⟩
        simpa [Instr.effect, State.modify, hp] using hz'.writeData a f (x.data r))
    exact ⟨z, he, hz, trivial⟩
  | op o d a b =>
    have hout : Cslib.WordRAM.Fits w (S.encode (M.evalOp o (x.data a) (x.data b))) := by
      simpa [Instr.effect, State.setData] using hf'.data d
    obtain ⟨z, he, hz⟩ := S.op_spec w o (dataReg L d) (dataReg L a) (dataReg L b)
      y (x.data a) (x.data b) (h.data a) (h.data b) hs hout
    exact ⟨z, he, h.setData_of_frame d _ hz.result hz.frame hz.memory, trivial⟩
  | create r =>
    obtain ⟨z, he, hz⟩ := S.create_spec r h hf'
    exact ⟨z, he, hz, trivial⟩
  | ifTest p a b t =>
    have hone : 1 < 2 ^ w := lt_of_le_of_lt (by simp [nodeAddr]) hf.free
    obtain ⟨z, he, hz⟩ := S.test_spec w p (valueReg L) (dataReg L a) (dataReg L b)
      y (x.data a) (x.data b) (h.data a) (h.data b) hs hone
    refine ⟨z, he, h.of_frame (fun r hr => hz.frame r hr ?_) hz.memory, hz.result⟩
    simp [Fin.ext_iff]
    omega
  | goto t => exact ⟨y, nop_spec y, h, trivial⟩
  | ifPtrEq a b t => exact ⟨y, nop_spec y, h, trivial⟩
  | halt => exact ⟨y, nop_spec y, h, trivial⟩

end Scalars
end Cslib.PointerMachine.WordRAM
