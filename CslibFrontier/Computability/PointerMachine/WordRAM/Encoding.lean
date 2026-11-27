/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Memory

/-!
# Encoding pointer-machine states as word memory

`encodeState` installs the source register banks and fixed-size node blocks in word memory,
sets the next-free address, and fills unused registers and cells with zero. The source control
label is represented separately by the compiled program position. `repr_encodeState`
proves that every source state has this representation. `bounded_encodeState` gives the word
bound for valid source states satisfying `Fits`.

This describes the starting state of the simulator. It does not charge or implement conversion
from the word-RAM's input-list convention.
-/

public section

namespace Cslib.PointerMachine.WordRAM

variable {M : Model} {L : Layout}

/-- Encode the source pointer/data banks and heap blocks. Null, padding and unused memory are
zero; source data uses the explicitly supplied encoding `e`. -/
@[expose] def encodeState (e : M.Value ↪ ℕ) (x : State M L) :
    Cslib.WordRAM.Data (regCount L) where
  regs r :=
    if hp : r.val < L.ptrRegs then ptrWord L (x.ptr ⟨r.val, hp⟩)
    else if hs : r.val < L.ptrRegs + L.dataRegs then
      e (x.data ⟨r.val - L.ptrRegs, by omega⟩)
    else if r.val = L.ptrRegs + L.dataRegs then nodeAddr L x.heap.length else 0
  mem a :=
    if a = 0 then 0 else
    match x.heap[(a - 1) / stride L]? with
    | none => 0
    | some n =>
      if hp : (a - 1) % stride L < L.ptrFields then
        ptrWord L (n.ptr ⟨(a - 1) % stride L, hp⟩)
      else if hd : (a - 1) % stride L < L.ptrFields + L.dataFields then
        e (n.data ⟨(a - 1) % stride L - L.ptrFields, by omega⟩)
      else 0

private theorem encodeState_cell {e : M.Value ↪ ℕ} {x : State M L}
    {a f : ℕ} {n : Record M L} (hn : x.heap[a]? = some n) (hf : f < stride L) :
    (encodeState e x).mem (cellAddr L a f) =
      if hp : f < L.ptrFields then ptrWord L (n.ptr ⟨f, hp⟩)
      else if hd : f < L.ptrFields + L.dataFields then
        e (n.data ⟨f - L.ptrFields, by omega⟩)
      else 0 := by
  have hs : 0 < stride L := by simp [stride]
  have hne : cellAddr L a f ≠ 0 := by unfold cellAddr nodeAddr; omega
  have hsub : cellAddr L a f - 1 = stride L * a + f := by
    unfold cellAddr nodeAddr; omega
  have hdiv : (cellAddr L a f - 1) / stride L = a := by
    rw [hsub, Nat.mul_add_div hs, Nat.div_eq_of_lt hf, Nat.add_zero]
  have hmod : (cellAddr L a f - 1) % stride L = f := by
    rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  simp [encodeState, hne, hdiv, hmod, hn]

/-- Every source state is represented by its canonical word-memory encoding. -/
theorem repr_encodeState (e : M.Value ↪ ℕ) (x : State M L) :
    Repr e x (encodeState e x) where
  ptr r := by simp [encodeState, ptrReg, r.isLt]
  data s := by
    have hs : L.ptrRegs + s.val < L.ptrRegs + L.dataRegs := by have := s.isLt; omega
    simp [encodeState, dataReg, hs]
  free := by simp [encodeState, freeReg]
  zero := by
    have hp : ¬L.ptrRegs + L.dataRegs + 1 < L.ptrRegs := by omega
    have hd : ¬L.ptrRegs + L.dataRegs + 1 < L.ptrRegs + L.dataRegs := by omega
    simp [encodeState, zeroReg, hp, hd]
  heapPtr a n hn f := by
    have hf : f.val < stride L := ptrField_lt_stride f
    rw [encodeState_cell hn hf]
    simp [f.isLt]
  heapData a n hn f := by
    have hf : L.ptrFields + f.val < stride L := dataField_lt_stride f
    have hsum : L.ptrFields + f.val < L.ptrFields + L.dataFields := by have := f.isLt; omega
    rw [encodeState_cell hn hf]
    simp [hsum]

/-- Valid pointers and fitting source data make every encoded register and cell word-bounded. -/
theorem bounded_encodeState {e : M.Value ↪ ℕ} {w : ℕ} {x : State M L}
    (hv : x.Valid) (hf : Fits e w x) : (encodeState e x).Bounded w := by
  constructor
  · intro r
    simp only [encodeState]
    split_ifs with hp hs he
    · exact hf.ptrWord (hv.1 ⟨r.val, hp⟩)
    · exact hf.data _
    · exact hf.free
    · exact Cslib.WordRAM.fits_zero w
  · intro a
    by_cases ha : a = 0
    · simp [encodeState, ha, Cslib.WordRAM.fits_zero]
    · simp only [encodeState, ha, ite_false]
      cases hn : x.heap[(a - 1) / stride L]? with
      | none => exact Cslib.WordRAM.fits_zero w
      | some n =>
        split_ifs with hp hd
        · exact hf.ptrWord (hv.2 n (List.mem_of_getElem? hn) ⟨_, hp⟩)
        · exact hf.heapData n (List.mem_of_getElem? hn) _
        · exact Cslib.WordRAM.fits_zero w

end Cslib.PointerMachine.WordRAM
