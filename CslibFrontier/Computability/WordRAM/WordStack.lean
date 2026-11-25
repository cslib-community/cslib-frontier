/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Record

/-!
# Register-top `k`-word stacks on the word RAM

`Stack.Memory` and `MemoryStack` store one-word items alongside a count cell in memory.
Iterative depth-first and worklist controllers on the word RAM instead keep the live record
count in a register `top` and store `k`-word records directly at `[base, base + cap * k)` with
no header cell, starting from possibly dirty memory.

This module provides:

* `WordStack.Holds R base items mem`, the top-first LIFO representation of `items : List α` in
  `[base, base + items.length * k)`, requiring no initialization of unused capacity above the
  live prefix;
* `WordStack.push` and `WordStack.pop`, inline `Code .standard r` routines executing in exact
  `2 * k + 2` instructions;
* `WordStack.pushWords_exec`, `WordStack.popWords_exec`, `WordStack.push_exec`, and
  `WordStack.pop_exec`, proving exact instruction counts, typed LIFO stack transitions, and
  both single-slot and capacity-bounded `Modifies` frames.

## Main definitions

* `Cslib.WordRAM.WordStack.Holds`: top-first `k`-word stack representation at `base`.
* `Cslib.WordRAM.WordStack.push`, `Cslib.WordRAM.WordStack.pop`: inline `2 * k + 2`-instruction
  push and pop programs.
* `Cslib.WordRAM.WordStack.PushLocal`, `Cslib.WordRAM.WordStack.PopLocal`: modified-register
  predicates for `push` and `pop`.

## Main results

* `Cslib.WordRAM.WordStack.Holds.unique`, `Cslib.WordRAM.WordStack.Holds.keep`,
  `Cslib.WordRAM.WordStack.holds_iff_getElem_reverse`: uniqueness at a known register top,
  equality-frame preservation, and reverse-indexed characterization of `WordStack.Holds`.
* `Cslib.WordRAM.WordStack.pushWords_exec`, `Cslib.WordRAM.WordStack.push_exec`: exact
  `2 * k + 2`-instruction push at the single-slot and typed-stack levels.
* `Cslib.WordRAM.WordStack.popWords_exec`, `Cslib.WordRAM.WordStack.pop_exec`: exact
  `2 * k + 2`-instruction pop at the single-slot and typed-stack levels.
-/

public section

namespace Cslib.WordRAM.WordStack

/-! ## Top-first `k`-word stack invariant -/

section Holds

variable {α : Type*} {k : ℕ}

/-- Top-first LIFO stack of `k`-word records at `base`: `items = v :: rest` places `v` at
`base + rest.length * k` above `rest` in `[base, base + rest.length * k)`. Cells at or above
`base + items.length * k` are unconstrained. -/
@[expose] def Holds (R : RecordSpec α k) (base : ℕ) : List α → (ℕ → ℕ) → Prop
  | [], _ => True
  | v :: rest, mem => R.HoldsAt (base + rest.length * k) v mem ∧ Holds R base rest mem

@[simp]
theorem holds_nil (R : RecordSpec α k) (base : ℕ) (mem : ℕ → ℕ) : Holds R base [] mem :=
  trivial

@[simp]
theorem holds_cons (R : RecordSpec α k) (base : ℕ) (v : α) (rest : List α) (mem : ℕ → ℕ) :
    Holds R base (v :: rest) mem ↔
      R.HoldsAt (base + rest.length * k) v mem ∧ Holds R base rest mem :=
  Iff.rfl

/-- An equality frame covering `[base, base + items.length * k)` preserves `Holds`. -/
theorem Holds.keep {R : RecordSpec α k} {base : ℕ} {items : List α}
    {before after : ℕ → ℕ} {reads : Set ℕ}
    (h : Holds R base items before) (hf : Set.EqOn after before reads)
    (hspan : Set.Ico base (base + items.length * k) ⊆ reads) :
    Holds R base items after := by
  induction items with
  | nil => trivial
  | cons v rest ih =>
    have hlen : (v :: rest).length * k = rest.length * k + k := by
      simp only [List.length_cons, Nat.succ_mul]
    refine ⟨Block.Realizes.keep h.1 hf fun a ha => hspan ?_, ih h.2 fun a ha => hspan ?_⟩ <;>
      simp only [Set.mem_Ico] at ha ⊢ <;> omega

/-- Agreement on `[base, base + items.length * k)` transports `Holds`. -/
theorem Holds.frame {R : RecordSpec α k} {base : ℕ} {items : List α} {mem mem' : ℕ → ℕ}
    (h : Holds R base items mem)
    (heq : ∀ a, base ≤ a → a < base + items.length * k → mem' a = mem a) :
    Holds R base items mem' :=
  h.keep (reads := Set.Ico base (base + items.length * k))
    (fun a ha => heq a ha.1 ha.2) Set.Subset.rfl

/-- Writing `v` immediately above a represented stack `items` represents `v :: items`. -/
theorem Holds.push_write {R : RecordSpec α k} {base : ℕ} {items : List α} {mem : ℕ → ℕ}
    (h : Holds R base items mem) (v : α) :
    Holds R base (v :: items) (R.write (base + items.length * k) v mem) :=
  ⟨R.holdsAt_write _ v mem,
    h.frame fun _ _ ha => writeWords_of_not_owns (by simp only [Block.Owns]; omega)⟩

/-- At a fixed stack height, injective record encoding uniquely determines the logical stack list
from memory. -/
theorem Holds.unique {R : RecordSpec α k} (hinj : Function.Injective R.toWords)
    {base : ℕ} {items₁ items₂ : List α} {mem : ℕ → ℕ}
    (h₁ : Holds R base items₁ mem) (h₂ : Holds R base items₂ mem)
    (hlen : items₁.length = items₂.length) : items₁ = items₂ := by
  induction items₁ generalizing items₂ with
  | nil =>
    cases items₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons v₁ rest₁ ih =>
    cases items₂ with
    | nil => simp at hlen
    | cons v₂ rest₂ =>
      have hrest_len : rest₁.length = rest₂.length := by simpa using hlen
      have hv : v₁ = v₂ := h₁.1.unique hinj (hrest_len ▸ h₂.1)
      rw [hv, ih h₁.2 h₂.2 hrest_len]

/-- `Holds R base items mem` is equivalent to each slot `idx < items.length` holding the
`idx`-th element from the bottom (`items.reverse[idx]`). -/
theorem holds_iff_getElem_reverse (R : RecordSpec α k) (base : ℕ) (items : List α)
    (mem : ℕ → ℕ) :
    Holds R base items mem ↔
      ∀ idx : Fin items.length,
        R.HoldsAt (base + idx.val * k) (items.reverse[idx.val]'(by simp)) mem := by
  induction items with
  | nil => simp
  | cons v rest ih =>
    rw [holds_cons, ih, and_comm]
    refine Iff.trans ?_ Fin.forall_fin_succ'.symm
    simp [List.getElem_append_left, List.getElem_append_right]

end Holds

/-! ## Inline register-top `push` and `pop` routines -/

section Routines

variable {r : ℕ}

/-- Push one `k`-word record from `fields` onto the stack at `base + top * width` and increment
`top` (`2 * k + 2` instructions). -/
@[expose] def push {k : ℕ} [NeZero k] (base top cursor width one : Fin r) (fields : Fin k → Fin r) :
    Code .standard r :=
  ram[ cursor ← top * width; cursor ← base + cursor;
       ⟪appendCode (storeCursor cursor one fields) (ram[ top ← top + one ])⟫ ]

/-- Decrement `top` and load the `k`-word record at `base + top * width` into `fields`
(`2 * k + 2` instructions). -/
@[expose] def pop {k : ℕ} [NeZero k] (base top cursor width one : Fin r) (fields : Fin k → Fin r) :
    Code .standard r :=
  ram[ top ← top - one; cursor ← top * width; cursor ← base + cursor;
       ⟪loadCursor cursor one fields⟫ ]

/-- Registers written by `WordStack.push`: `cursor` and `top`. -/
@[expose] def PushLocal (top cursor i : Fin r) : Prop := i = cursor ∨ i = top

instance (top cursor i : Fin r) : Decidable (PushLocal top cursor i) :=
  inferInstanceAs (Decidable (i = cursor ∨ i = top))

/-- Registers written by `WordStack.pop`: `top`, `cursor`, and the loaded `fields`. -/
@[expose] def PopLocal {k : ℕ} (top cursor : Fin r) (fields : Fin k → Fin r) (i : Fin r) : Prop :=
  i = top ∨ LoadRecordLocal cursor fields i

instance {k : ℕ} (top cursor : Fin r) (fields : Fin k → Fin r) (i : Fin r) :
    Decidable (PopLocal top cursor fields i) :=
  inferInstanceAs (Decidable (i = top ∨ LoadRecordLocal cursor fields i))

/-- `WordStack.push` preserves every register outside `PushLocal top cursor`. -/
theorem push_preserves {k : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) {i : Fin r} (hi : ¬PushLocal top cursor i) :
    (push base top cursor width one fields).Preserves i := by
  have hcur : i ≠ cursor := fun h => hi (Or.inl h)
  have htop : i ≠ top := fun h => hi (Or.inr h)
  simp only [push, Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
  refine ⟨hcur.symm, hcur.symm, Code.preserves_appendCode
    (storeCursor_preserves cursor one fields hcur) ?_⟩
  simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  exact htop.symm

/-- `WordStack.pop` preserves every register outside `PopLocal top cursor fields`. -/
theorem pop_preserves {k : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) {i : Fin r} (hi : ¬PopLocal top cursor fields i) :
    (pop base top cursor width one fields).Preserves i := by
  have htop : i ≠ top := fun h => hi (Or.inl h)
  have hload : ¬LoadRecordLocal cursor fields i := fun h => hi (Or.inr h)
  have hcur : i ≠ cursor := fun h => hload (Or.inl h)
  simp only [pop, Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
  exact ⟨htop.symm, hcur.symm, hcur.symm, loadCursor_preserves cursor one fields hload⟩

/-- `WordStack.push` never inspects the physical word width. -/
theorem push_not_readsWidth {k : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) : ¬(push base top cursor width one fields).ReadsWidth := by
  simp only [push, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
  refine ⟨by simp, by simp,
    Code.not_readsWidth_appendCode (storeCursor_not_readsWidth cursor one fields) ?_⟩
  simp [Code.ReadsWidth, Op.ReadsWidth]

/-- `WordStack.pop` never inspects the physical word width. -/
theorem pop_not_readsWidth {k : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) : ¬(pop base top cursor width one fields).ReadsWidth := by
  simp only [pop, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
  exact ⟨by simp, by simp, by simp,
    loadCursor_not_readsWidth cursor one fields⟩

/-- Single-slot execution of `WordStack.push` in exact `2 * k + 2` instructions. -/
theorem pushWords_exec {k w F n : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) (x : Data r)
    (hbase_cur : base ≠ cursor) (htop_cur : top ≠ cursor) (hone_cur : one ≠ cursor)
    (hfields_cur : ∀ i, fields i ≠ cursor)
    (hbase : x.regs base = F) (htop : x.regs top = n)
    (hwidth : x.regs width = k) (hone : x.regs one = 1)
    (hfit : Fits w (F + (n + 1) * k)) :
    ∃ y, Exec w (push base top cursor width one fields) x y (2 * k + 2) ∧
      y.regs top = n + 1 ∧
      y.mem = writeWords x.mem (F + n * k) (fun i => x.regs (fields i)) ∧
      Modifies (Block.mk (F + n * k) k).footprint x.mem y.mem ∧
      ∀ i, ¬PushLocal top cursor i → y.regs i = x.regs i := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hnk : n * k + k = (n + 1) * k := (Nat.succ_mul n k).symm
  have hn_le : n ≤ n * k := Nat.le_mul_of_pos_right n hk
  unfold push
  wram_exec [hbase, htop, hwidth]
  refine WP.Exact.name fun x₁ hx₁ => ?_
  obtain ⟨z, hz, hzmem, _, hzregs⟩ := storeCursor_exec (w := w) cursor one fields x₁ hone_cur
    hfields_cur (by wram_simp [hx₁, hone]) (by wram_simp [hx₁]; fits)
  have hz_top : z.regs top = n := by rw [hzregs top htop_cur]; wram_simp [hx₁, htop]
  have hz_one : z.regs one = 1 := by rw [hzregs one hone_cur]; wram_simp [hx₁, hone]
  have hinc : Exec w (ram[ top ← top + one ]) z (z.set top (n + 1)) 1 := by
    wram_exec [hz_top, hz_one]
  have hymem : (z.set top (n + 1)).mem = writeWords x.mem (F + n * k) fun i => x.regs (fields i) :=
    by wram_simp [hzmem, hx₁]
  refine WP.Exact.of_exec (exec_append hz hinc) ⟨by omega, by wram_simp, hymem,
    hymem ▸ modifies_writeWords x.mem (F + n * k) _, fun i hi => ?_⟩
  simp only [PushLocal, not_or] at hi
  rw [Data.set_regs_of_ne hi.2, hzregs i hi.1]
  wram_simp [hx₁]

/-- Push a typed `k`-word record `v` onto a stack of capacity `cap` in exact `2 * k + 2`
instructions. -/
theorem push_exec {α : Type*} {k w baseAddr cap : ℕ} [NeZero k] (R : RecordSpec α k)
    (base top cursor width one : Fin r) (fields : Fin k → Fin r)
    (items : List α) (v : α) (x : Data r)
    (hbase_cur : base ≠ cursor) (htop_cur : top ≠ cursor) (hone_cur : one ≠ cursor)
    (hfields_cur : ∀ i, fields i ≠ cursor)
    (hbase : x.regs base = baseAddr) (htop : x.regs top = items.length)
    (hwidth : x.regs width = k) (hone : x.regs one = 1)
    (hfields : ∀ i, x.regs (fields i) = R.toWords v i)
    (hstack : Holds R baseAddr items x.mem) (hcap : items.length < cap)
    (hfit : Fits w (baseAddr + cap * k)) :
    ∃ y, Exec w (push base top cursor width one fields) x y (2 * k + 2) ∧
      y.regs top = items.length + 1 ∧
      Holds R baseAddr (v :: items) y.mem ∧
      y.mem = R.write (baseAddr + items.length * k) v x.mem ∧
      Modifies (Block.mk baseAddr (cap * k)).footprint x.mem y.mem ∧
      ∀ i, ¬PushLocal top cursor i → y.regs i = x.regs i := by
  have hslot_le : (items.length + 1) * k ≤ cap * k := Nat.mul_le_mul_right k hcap
  obtain ⟨y, hy, hytop, hymem, hmod_slot, hyregs⟩ :=
    pushWords_exec base top cursor width one fields x
      hbase_cur htop_cur hone_cur hfields_cur hbase htop hwidth hone
      (hfit.of_le (by omega))
  have hwords : (fun i => x.regs (fields i)) = R.toWords v := funext hfields
  rw [hwords] at hymem
  have hnk : items.length * k + k = (items.length + 1) * k := (Nat.succ_mul _ _).symm
  refine ⟨y, hy, hytop, hymem ▸ hstack.push_write v, hymem,
    fun a ha => hmod_slot a (mt (fun ha => ?_) ha), hyregs⟩
  simp only [Block.mem_footprint, Block.Owns] at ha ⊢
  omega

/-- Single-slot execution of `WordStack.pop` in exact `2 * k + 2` instructions. -/
theorem popWords_exec {k w F n : ℕ} [NeZero k] (base top cursor width one : Fin r)
    (fields : Fin k → Fin r) (x : Data r)
    (hbase_top : base ≠ top) (hwidth_top : width ≠ top) (hone_top : one ≠ top)
    (hbase_cur : base ≠ cursor) (htop_cur : top ≠ cursor) (hone_cur : one ≠ cursor)
    (hfields_top : ∀ i, fields i ≠ top) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hbase : x.regs base = F) (htop : x.regs top = n + 1)
    (hwidth : x.regs width = k) (hone : x.regs one = 1)
    (hfit : Fits w (F + n * k + (k - 1))) :
    ∃ y, Exec w (pop base top cursor width one fields) x y (2 * k + 2) ∧
      y.regs top = n ∧
      y.mem = x.mem ∧
      (∀ i, y.regs (fields i) = x.mem (F + n * k + i.val)) ∧
      ∀ i, ¬PopLocal top cursor fields i → y.regs i = x.regs i := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hn_le : n ≤ n * k := Nat.le_mul_of_pos_right n hk
  unfold pop
  wram_exec [hbase, htop, hwidth, hone]
  refine WP.Exact.name fun x₂ hx₂ => ?_
  obtain ⟨y, hy, hymem, hyfields, _, hyregs⟩ := loadCursor_exec cursor one fields x₂ hone_cur
    hfields_cur hfields_one hinj (by wram_simp [hx₂, hone]) (by wram_simp [hx₂]; fits)
  have htop_not_load : ¬LoadRecordLocal cursor fields top := by
    rintro (h | ⟨i, h⟩)
    · exact htop_cur h
    · exact hfields_top i h.symm
  refine WP.Exact.of_exec hy ⟨by omega, by rw [hyregs top htop_not_load]; wram_simp [hx₂],
    by wram_simp [hymem, hx₂], fun i => by rw [hyfields i]; wram_simp [hx₂], fun i hi => ?_⟩
  have hcur : i ≠ cursor := fun h => hi (Or.inr (Or.inl h))
  have htop' : i ≠ top := fun h => hi (Or.inl h)
  rw [hyregs i fun h => hi (Or.inr h)]
  wram_simp [hx₂]

/-- Pop the top typed `k`-word record `v` from `v :: items` into `fields` in exact `2 * k + 2`
instructions. -/
theorem pop_exec {α : Type*} {k w baseAddr : ℕ} [NeZero k] (R : RecordSpec α k)
    (base top cursor width one : Fin r) (fields : Fin k → Fin r)
    (items : List α) (v : α) (x : Data r)
    (hbase_top : base ≠ top) (hwidth_top : width ≠ top) (hone_top : one ≠ top)
    (hbase_cur : base ≠ cursor) (htop_cur : top ≠ cursor) (hone_cur : one ≠ cursor)
    (hfields_top : ∀ i, fields i ≠ top) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hbase : x.regs base = baseAddr) (htop : x.regs top = items.length + 1)
    (hwidth : x.regs width = k) (hone : x.regs one = 1)
    (hstack : Holds R baseAddr (v :: items) x.mem)
    (hfit : Fits w (baseAddr + items.length * k + (k - 1))) :
    ∃ y, Exec w (pop base top cursor width one fields) x y (2 * k + 2) ∧
      y.regs top = items.length ∧
      Holds R baseAddr items y.mem ∧
      (∀ i, y.regs (fields i) = R.toWords v i) ∧
      y.mem = x.mem ∧
      ∀ i, ¬PopLocal top cursor fields i → y.regs i = x.regs i := by
  obtain ⟨y, hy, hytop, hymem, hyfields, hyregs⟩ :=
    popWords_exec base top cursor width one fields x
      hbase_top hwidth_top hone_top hbase_cur htop_cur hone_cur
      hfields_top hfields_cur hfields_one hinj hbase htop hwidth hone hfit
  exact ⟨y, hy, hytop, hymem ▸ hstack.2, fun i => (hyfields i).trans (hstack.1 i), hymem, hyregs⟩

end Routines

end Cslib.WordRAM.WordStack

end
