/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic
public import CslibFrontier.Computability.WordRAM.Defs

/-!
# Pointer-machine heaps in word memory

A node occupies a fixed block of words. Null is zero; node `a` starts at
`1 + stride L * a`. Pointer fields precede data fields. The register layout keeps the source
banks, the next free address, a zero register, and four temporary registers.

`Repr` describes the represented state without constraining temporary registers or unused
memory. The update lemmas connect source register and field updates to word-memory updates.
-/

public section

namespace Cslib.PointerMachine.WordRAM

/-- Source register banks, next-free and zero registers, and four temporary registers. -/
abbrev regCount (L : Layout) : ℕ := L.ptrRegs + L.dataRegs + 6

/-- The target register containing a source pointer register. -/
@[expose] def ptrReg (L : Layout) (r : Fin L.ptrRegs) : Fin (regCount L) :=
  ⟨r.val, by have := r.isLt; unfold regCount; omega⟩

/-- The target register containing a source data register. -/
@[expose] def dataReg (L : Layout) (s : Fin L.dataRegs) : Fin (regCount L) :=
  ⟨L.ptrRegs + s.val, by have := s.isLt; unfold regCount; omega⟩

/-- The first address after all allocated records. -/
@[expose] def freeReg (L : Layout) : Fin (regCount L) :=
  ⟨L.ptrRegs + L.dataRegs, by unfold regCount; omega⟩

/-- A register that remains zero. -/
@[expose] def zeroReg (L : Layout) : Fin (regCount L) :=
  ⟨L.ptrRegs + L.dataRegs + 1, by unfold regCount; omega⟩

/-- Temporary address register. -/
@[expose] def addrReg (L : Layout) : Fin (regCount L) :=
  ⟨L.ptrRegs + L.dataRegs + 2, by unfold regCount; omega⟩

/-- Temporary value register. -/
@[expose] def valueReg (L : Layout) : Fin (regCount L) :=
  ⟨L.ptrRegs + L.dataRegs + 3, by unfold regCount; omega⟩

@[simp] theorem ptrReg_val (L : Layout) (r : Fin L.ptrRegs) :
    (ptrReg L r).val = r.val := rfl

@[simp] theorem dataReg_val (L : Layout) (s : Fin L.dataRegs) :
    (dataReg L s).val = L.ptrRegs + s.val := rfl

@[simp] theorem freeReg_val (L : Layout) :
    (freeReg L).val = L.ptrRegs + L.dataRegs := rfl

@[simp] theorem zeroReg_val (L : Layout) :
    (zeroReg L).val = L.ptrRegs + L.dataRegs + 1 := rfl

@[simp] theorem addrReg_val (L : Layout) :
    (addrReg L).val = L.ptrRegs + L.dataRegs + 2 := rfl

@[simp] theorem valueReg_val (L : Layout) :
    (valueReg L).val = L.ptrRegs + L.dataRegs + 3 := rfl

/-- Each node occupies at least one cell, even when it has no fields. -/
@[expose] def stride (L : Layout) : ℕ := max 1 (L.ptrFields + L.dataFields)

/-- The base address of node `a`, reserving zero for null. -/
@[expose] def nodeAddr (L : Layout) (a : ℕ) : ℕ := 1 + stride L * a

/-- Null becomes zero and nonnull pointers become node base addresses. -/
@[expose] def ptrWord (L : Layout) : Pointer → ℕ
  | none => 0
  | some a => nodeAddr L a

/-- Address of offset `f` within node `a`. Pointer offsets precede data offsets. -/
@[expose] def cellAddr (L : Layout) (a f : ℕ) : ℕ := nodeAddr L a + f

variable {M : Model} {L : Layout}

/-- A source state represented in target registers and allocated memory. -/
structure Repr (e : M.Value ↪ ℕ) (x : State M L) (y : Cslib.WordRAM.Data (regCount L)) : Prop where
  /-- Pointer register contents. -/
  ptr : ∀ r, y.regs (ptrReg L r) = ptrWord L (x.ptr r)
  /-- Data register contents. -/
  data : ∀ s, y.regs (dataReg L s) = e (x.data s)
  /-- The next free address. -/
  free : y.regs (freeReg L) = nodeAddr L x.heap.length
  /-- Null comparison register. -/
  zero : y.regs (zeroReg L) = 0
  /-- Pointer fields of allocated records. -/
  heapPtr : ∀ a n, x.heap[a]? = some n → ∀ f,
    y.mem (cellAddr L a f.val) = ptrWord L (n.ptr f)
  /-- Data fields of allocated records. -/
  heapData : ∀ a n, x.heap[a]? = some n → ∀ f,
    y.mem (cellAddr L a (L.ptrFields + f.val)) = e (n.data f)

/-- The next-free address and every represented datum fit in a word. Validity separately
ensures pointer words and occupied cell addresses are below the next-free address. -/
structure Fits (e : M.Value ↪ ℕ) (w : ℕ) (x : State M L) : Prop where
  /-- The first free address fits in a word. -/
  free : Cslib.WordRAM.Fits w (nodeAddr L x.heap.length)
  /-- Every scalar register fits in a word. -/
  data : ∀ s, Cslib.WordRAM.Fits w (e (x.data s))
  /-- Every allocated scalar field fits in a word. -/
  heapData : ∀ n ∈ x.heap, ∀ f, Cslib.WordRAM.Fits w (e (n.data f))

/-- Pointer fields lie within their node's block. -/
theorem ptrField_lt_stride (f : Fin L.ptrFields) : f.val < stride L :=
  lt_of_lt_of_le (Nat.lt_add_right L.dataFields f.isLt) (le_max_right _ _)

/-- Data fields follow the pointer fields within their node's block. -/
theorem dataField_lt_stride (f : Fin L.dataFields) : L.ptrFields + f.val < stride L :=
  lt_of_lt_of_le (Nat.add_lt_add_left f.isLt _) (le_max_right _ _)

/-- A cell of an allocated node precedes the first free address. -/
theorem cellAddr_lt {a n i : ℕ} (ha : a < n) (hi : i < stride L) :
    cellAddr L a i < nodeAddr L n := by
  have h := Nat.mul_le_mul_left (stride L) (Nat.add_one_le_iff.mpr ha)
  simp only [Nat.mul_add, Nat.mul_one] at h
  unfold cellAddr nodeAddr
  omega

/-- Different nodes and offsets designate different cells. -/
theorem cellAddr_injective {a b i j : ℕ} (hi : i < stride L) (hj : j < stride L)
    (h : cellAddr L a i = cellAddr L b j) : a = b ∧ i = j := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact absurd h (ne_of_lt ((cellAddr_lt hab hi).trans_le (Nat.le_add_right _ _)))
  · exact ⟨rfl, Nat.add_left_cancel h⟩
  · exact absurd h.symm (ne_of_lt ((cellAddr_lt hba hj).trans_le (Nat.le_add_right _ _)))

private theorem cellAddr_eq_iff {a b i j : ℕ} (hi : i < stride L) (hj : j < stride L) :
    cellAddr L a i = cellAddr L b j ↔ a = b ∧ i = j :=
  ⟨cellAddr_injective hi hj, by rintro ⟨rfl, rfl⟩; rfl⟩

private theorem cellAddr_ptr_ne_data (a b : ℕ) (f : Fin L.ptrFields) (g : Fin L.dataFields) :
    cellAddr L a f.val ≠ cellAddr L b (L.ptrFields + g.val) := fun h => by
  have := (cellAddr_injective (ptrField_lt_stride f) (dataField_lt_stride g) h).2
  omega

/-- Pointer words retain pointer equality, including null. -/
theorem ptrWord_injective : Function.Injective (ptrWord L) := by
  rintro (_ | a) (_ | b) h
  · rfl
  · simp only [ptrWord, nodeAddr] at h; omega
  · simp only [ptrWord, nodeAddr] at h; omega
  · simp only [ptrWord, nodeAddr, Nat.add_left_cancel_iff] at h
    exact congrArg some (Nat.eq_of_mul_eq_mul_left (by simp [stride]) h)

namespace Fits

variable {e : M.Value ↪ ℕ} {w : ℕ} {x : State M L}

/-- Occupied field addresses fit whenever the next-free address does. -/
theorem cellAddr (h : Fits e w x) {a i : ℕ} (ha : a < x.heap.length)
    (hi : i < stride L) : Cslib.WordRAM.Fits w (cellAddr L a i) :=
  lt_trans (cellAddr_lt ha hi) h.free

/-- Null or a pointer to an allocated record fits in the target word size. -/
theorem ptrWord (h : Fits e w x) {p : Pointer}
    (hp : ∀ a, p = some a → a < x.heap.length) : Cslib.WordRAM.Fits w (ptrWord L p) := by
  cases p with
  | none => exact Nat.two_pow_pos w
  | some a =>
    have hs : 0 < stride L := by simp [stride]
    simpa [WordRAM.ptrWord, WordRAM.cellAddr] using h.cellAddr (hp a rfl) hs

end Fits

namespace Repr

variable {e : M.Value ↪ ℕ} {x : State M L} {y z : Cslib.WordRAM.Data (regCount L)} (h : Repr e x y)

include h

/-- The representation ignores the source control label. -/
theorem with_pc (pc : ℕ) : Repr e {x with pc := pc} y :=
  ⟨h.ptr, h.data, h.free, h.zero, h.heapPtr, h.heapData⟩

/-- Changing temporary registers preserves the represented state. -/
theorem of_frame (hr : ∀ r : Fin (regCount L), r.val < L.ptrRegs + L.dataRegs + 2 →
    z.regs r = y.regs r) (hm : z.mem = y.mem) : Repr e x z where
  ptr r := (hr _ (by have := r.isLt; simp only [ptrReg]; omega)).trans (h.ptr r)
  data s := (hr _ (by have := s.isLt; simp only [dataReg]; omega)).trans (h.data s)
  free := (hr _ (by simp [freeReg])).trans h.free
  zero := (hr _ (by simp [zeroReg])).trans h.zero
  heapPtr a n hn f := by rw [hm]; exact h.heapPtr a n hn f
  heapData a n hn f := by rw [hm]; exact h.heapData a n hn f

/-- Writing a temporary register leaves the represented state unchanged. -/
theorem scratch (r : Fin (regCount L)) (hr : L.ptrRegs + L.dataRegs + 2 ≤ r.val) (v : ℕ) :
    Repr e x (y.set r v) := h.of_frame (fun s hs => by
      have hsr : s ≠ r := by intro hsr; subst r; omega
      simp [Cslib.WordRAM.Data.set, Function.update_of_ne hsr]) rfl

/-- A pointer-register update is one corresponding word-register update. -/
theorem setPtr (r : Fin L.ptrRegs) (p : Pointer) :
    Repr e (x.setPtr r p) (y.set (ptrReg L r) (ptrWord L p)) where
  ptr s := by
    by_cases hs : s = r
    · subst s; simp [State.setPtr, Cslib.WordRAM.Data.set]
    · have hsr : ptrReg L s ≠ ptrReg L r := by simpa [ptrReg, Fin.ext_iff] using hs
      simp [State.setPtr, Cslib.WordRAM.Data.set, Function.update_of_ne hs,
        Function.update_of_ne hsr, h.ptr]
  data s := by
    have hsr : dataReg L s ≠ ptrReg L r := by simp [Fin.ext_iff]; omega
    simpa [State.setPtr, Cslib.WordRAM.Data.set, Function.update_of_ne hsr] using h.data s
  free := by
    have hr : freeReg L ≠ ptrReg L r := by simp [Fin.ext_iff]; omega
    simpa [State.setPtr, Cslib.WordRAM.Data.set, Function.update_of_ne hr] using h.free
  zero := by
    have hr : zeroReg L ≠ ptrReg L r := by simp [Fin.ext_iff]; omega
    simpa [State.setPtr, Cslib.WordRAM.Data.set, Function.update_of_ne hr] using h.zero
  heapPtr := h.heapPtr
  heapData := h.heapData

/-- A data-register update is one corresponding word-register update. -/
theorem setData (s : Fin L.dataRegs) (v : M.Value) :
    Repr e (x.setData s v) (y.set (dataReg L s) (e v)) where
  ptr r := by
    have hrs : ptrReg L r ≠ dataReg L s := by simp [Fin.ext_iff]; omega
    simpa [State.setData, Cslib.WordRAM.Data.set, Function.update_of_ne hrs] using h.ptr r
  data t := by
    by_cases ht : t = s
    · subst t; simp [State.setData, Cslib.WordRAM.Data.set]
    · have hts : dataReg L t ≠ dataReg L s := by simpa [dataReg, Fin.ext_iff] using ht
      simp [State.setData, Cslib.WordRAM.Data.set, Function.update_of_ne ht,
        Function.update_of_ne hts, h.data]
  free := by
    have hs : freeReg L ≠ dataReg L s := by simp [Fin.ext_iff]; omega
    simpa [State.setData, Cslib.WordRAM.Data.set, Function.update_of_ne hs] using h.free
  zero := by
    have hs : zeroReg L ≠ dataReg L s := by simp [Fin.ext_iff]; omega
    simpa [State.setData, Cslib.WordRAM.Data.set, Function.update_of_ne hs] using h.zero
  heapPtr := h.heapPtr
  heapData := h.heapData


/-- Transfer a scalar result while allowing temporary registers to change. -/
theorem setData_of_frame (s : Fin L.dataRegs) (v : M.Value)
    (hv : z.regs (dataReg L s) = e v)
    (hr : ∀ r : Fin (regCount L), r.val < L.ptrRegs + L.dataRegs + 2 →
      r ≠ dataReg L s → z.regs r = y.regs r) (hm : z.mem = y.mem) :
    Repr e (x.setData s v) z := (h.setData s v).of_frame (fun r hl => by
      by_cases he : r = dataReg L s
      · subst r; simpa [Cslib.WordRAM.Data.set] using hv
      · simpa [Cslib.WordRAM.Data.set, Function.update_of_ne he] using hr r hl he) hm

private theorem modify (a : ℕ) (g : Record M L → Record M L)
    (hr : z.regs = y.regs)
    (hp : ∀ b n, x.heap[b]? = some n → ∀ f,
      z.mem (cellAddr L b f.val) = ptrWord L ((if b = a then g n else n).ptr f))
    (hd : ∀ b n, x.heap[b]? = some n → ∀ f,
      z.mem (cellAddr L b (L.ptrFields + f.val)) = e ((if b = a then g n else n).data f)) :
    Repr e {x with heap := x.heap.modify a g} z where
  ptr r := by rw [hr]; exact h.ptr r
  data s := by rw [hr]; exact h.data s
  free := by simpa [hr] using h.free
  zero := by rw [hr]; exact h.zero
  heapPtr b n hn f := by
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_modify .. ▸ hn)
    simpa only [eq_comm] using hp b m hm f
  heapData b n hn f := by
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_modify .. ▸ hn)
    simpa only [eq_comm] using hd b m hm f

/-- Storing a pointer field is a single word-memory update. -/
theorem writePtr (a : ℕ) (f : Fin L.ptrFields) (p : Pointer) :
    Repr e {x with heap := x.heap.modify a fun n =>
      {n with ptr := Function.update n.ptr f p}}
      (y.write (cellAddr L a f.val) (ptrWord L p)) := by
  refine h.modify (z := y.write (cellAddr L a f.val) (ptrWord L p)) a _ rfl ?_ ?_
  · intro b n hn t
    have he : cellAddr L b t.val = cellAddr L a f.val ↔ b = a ∧ t = f := by
      rw [cellAddr_eq_iff (ptrField_lt_stride t) (ptrField_lt_stride f), Fin.ext_iff]
    have hmem := h.heapPtr b n hn t
    simp only [Cslib.WordRAM.Data.write, Function.update_apply, he]
    by_cases hb : b = a <;> by_cases ht : t = f <;> simp_all
  · intro b n hn t
    simp only [Cslib.WordRAM.Data.write,
      Function.update_of_ne (cellAddr_ptr_ne_data a b f t).symm]
    split_ifs <;> exact h.heapData b n hn t

/-- Storing a data field is a single word-memory update. -/
theorem writeData (a : ℕ) (f : Fin L.dataFields) (v : M.Value) :
    Repr e {x with heap := x.heap.modify a fun n =>
      {n with data := Function.update n.data f v}}
      (y.write (cellAddr L a (L.ptrFields + f.val)) (e v)) := by
  refine h.modify (z := y.write (cellAddr L a (L.ptrFields + f.val)) (e v)) a _ rfl ?_ ?_
  · intro b n hn t
    simp only [Cslib.WordRAM.Data.write, Function.update_of_ne (cellAddr_ptr_ne_data b a t f)]
    split_ifs <;> exact h.heapPtr b n hn t
  · intro b n hn t
    have he : cellAddr L b (L.ptrFields + t.val) = cellAddr L a (L.ptrFields + f.val) ↔
        b = a ∧ t = f := by
      rw [cellAddr_eq_iff (dataField_lt_stride t) (dataField_lt_stride f),
        Nat.add_left_cancel_iff, Fin.ext_iff]
    have hmem := h.heapData b n hn t
    simp only [Cslib.WordRAM.Data.write, Function.update_apply, he]
    by_cases hb : b = a <;> by_cases ht : t = f <;> simp_all

/-- Appending an initialized record preserves representation. The implementation must preserve
old occupied cells, initialize the new fields, and advance the next-free register. -/
theorem append (n : Record M L)
    (hr : ∀ r : Fin (regCount L), r.val < L.ptrRegs + L.dataRegs + 2 →
      r ≠ freeReg L → z.regs r = y.regs r)
    (hf : z.regs (freeReg L) = nodeAddr L (x.heap.length + 1))
    (hm : ∀ a < nodeAddr L x.heap.length, z.mem a = y.mem a)
    (hp : ∀ f, z.mem (cellAddr L x.heap.length f.val) = ptrWord L (n.ptr f))
    (hd : ∀ f, z.mem (cellAddr L x.heap.length (L.ptrFields + f.val)) = e (n.data f)) :
    Repr e {x with heap := x.heap ++ [n]} z := by
  have lookup {a : ℕ} {m : Record M L} (ha : (x.heap ++ [n])[a]? = some m) :
      (a < x.heap.length ∧ x.heap[a]? = some m) ∨ (a = x.heap.length ∧ m = n) := by
    by_cases hl : a < x.heap.length
    · exact Or.inl ⟨hl, by simpa only [List.getElem?_append_left hl] using ha⟩
    · obtain ⟨hb, ha⟩ := List.getElem?_eq_some_iff.mp ha
      obtain rfl : a = x.heap.length := by
        simp only [List.length_append, List.length_singleton] at hb
        omega
      exact Or.inr ⟨rfl, by simpa using ha.symm⟩
  exact {
    ptr r := (hr _ (by simp; omega)
      (by simp [Fin.ext_iff]; omega)).trans (h.ptr r)
    data s := (hr _ (by simp; omega)
      (by simp [Fin.ext_iff]; omega)).trans (h.data s)
    free := by simpa using hf
    zero := (hr _ (by simp [zeroReg]) (by simp [zeroReg, freeReg, Fin.ext_iff])).trans h.zero
    heapPtr a m ha f := by
      rcases lookup ha with ⟨hl, hm'⟩ | ⟨rfl, rfl⟩
      · rw [hm _ (cellAddr_lt hl (ptrField_lt_stride f))]
        exact h.heapPtr a m hm' f
      · exact hp f
    heapData a m ha f := by
      rcases lookup ha with ⟨hl, hm'⟩ | ⟨rfl, rfl⟩
      · rw [hm _ (cellAddr_lt hl (dataField_lt_stride f))]
        exact h.heapData a m hm' f
      · exact hd f }

end Repr
end Cslib.PointerMachine.WordRAM
