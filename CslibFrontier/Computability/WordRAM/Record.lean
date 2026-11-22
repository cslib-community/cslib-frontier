/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.MemoryView
public import CslibFrontier.Computability.WordRAM.Subroutine
public import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Fixed-width flat memory records on the word RAM

Algorithms on the word RAM serialize fixed-width headers, task descriptors, and explicit stack
frames as `k` consecutive words at an address `addr`. This module provides:

* `writeWords`, the multi-word memory update writing `k` consecutive words from `addr`, proved
  to realize those words on `Block.mk addr k` and to satisfy `Modifies (Block.mk addr k).footprint`
  for frame preservation via `ram_keep`;
* `RecordSpec α k`, a typed `k`-word layout specification whose `HoldsAt` assertion specializes
  `Block.Realizes` directly, taking injectivity of `toWords` only on uniqueness lemmas;
* `storeCursor`, `storeRecord`, `loadCursor`, and `loadRecord`, structured `Code .standard r`
  routines that step an address cursor by one across `k` field registers in exact instruction
  counts (`2 * k - 1` from an initialized cursor, `2 * k` from a base-address register), together
  with `appendCode` composition rules matching right-associated `ram[ … ]` blocks.

## Main definitions

* `Cslib.WordRAM.writeWords`: write `k` consecutive words starting at `addr`.
* `Cslib.WordRAM.RecordSpec`, `Cslib.WordRAM.RecordSpec.HoldsAt`,
  `Cslib.WordRAM.RecordSpec.write`: typed `k`-word flat record layout, memory assertion, and
  multi-word update.
* `Cslib.WordRAM.storeCursor`, `Cslib.WordRAM.storeRecord`: sequential cursor stores of `k`
  field registers.
* `Cslib.WordRAM.loadCursor`, `Cslib.WordRAM.loadRecord`, `Cslib.WordRAM.LoadRecordLocal`:
  sequential cursor loads into `k` field registers and their modified-register predicate.

## Main results

* `Cslib.WordRAM.Block.realizes_writeWords`, `Cslib.WordRAM.modifies_writeWords`,
  `Cslib.WordRAM.writeWords_of_not_owns`: exact block readback and disjoint write frame for
  `writeWords`.
* `Cslib.WordRAM.RecordSpec.HoldsAt.unique`, `Cslib.WordRAM.RecordSpec.holdsAt_write_iff`:
  uniqueness of decoded records and read-after-write characterization.
* `Cslib.WordRAM.exec_append`, `Cslib.WordRAM.WP.of_exec_spec`, `Cslib.WordRAM.WP.of_append_exec`:
  exact and weakest-precondition composition along `appendCode`.
* `Cslib.WordRAM.storeCursor_exec`, `Cslib.WordRAM.storeRecord_exec`,
  `Cslib.WordRAM.RecordSpec.store_exec`: exact-step execution of sequential record stores.
* `Cslib.WordRAM.loadCursor_exec`, `Cslib.WordRAM.loadRecord_exec`,
  `Cslib.WordRAM.RecordSpec.load_exec`, `Cslib.WordRAM.loadRecord_exec_self`: exact-step
  execution of sequential record loads, including idempotent reload of already-resident registers.
-/

public section

namespace Cslib.WordRAM

/-! ## Multi-word consecutive memory updates -/

/-- Write `k` consecutive words starting at `addr`, in increasing offset order. -/
@[expose] def writeWords (mem : ℕ → ℕ) (addr : ℕ) : {k : ℕ} → (Fin k → ℕ) → ℕ → ℕ
  | 0, _ => mem
  | k + 1, words =>
    Function.update (writeWords mem addr (fun i => words i.castSucc))
      (addr + k) (words (.last k))

@[simp]
theorem writeWords_zero (mem : ℕ → ℕ) (addr : ℕ) (words : Fin 0 → ℕ) :
    writeWords mem addr words = mem := rfl

@[simp]
theorem writeWords_succ (mem : ℕ → ℕ) (addr : ℕ) {k : ℕ} (words : Fin (k + 1) → ℕ) :
    writeWords mem addr words =
      Function.update (writeWords mem addr (fun i => words i.castSucc))
        (addr + k) (words (.last k)) := rfl

/-- Writing `words 0` at `addr` and the remaining `k` words at `addr + 1` equals writing all
`k + 1` words from `addr`. -/
theorem writeWords_cons (mem : ℕ → ℕ) (addr : ℕ) {k : ℕ} (words : Fin (k + 1) → ℕ) :
    writeWords (Function.update mem addr (words 0)) (addr + 1) (fun i : Fin k => words i.succ) =
      writeWords mem addr words := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev : writeWords (Function.update mem addr (words 0)) (addr + 1)
        (fun i : Fin k => words i.castSucc.succ) =
        writeWords mem addr (fun i => words i.castSucc) :=
      ih (fun i => words i.castSucc)
    have hcast : (fun i : Fin k => words i.succ.castSucc) =
        fun i : Fin k => words i.castSucc.succ := by
      funext i
      exact congrArg words (Fin.succ_castSucc i)
    calc
      writeWords (Function.update mem addr (words 0)) (addr + 1) (fun i => words i.succ)
        = Function.update
            (writeWords (Function.update mem addr (words 0)) (addr + 1)
              (fun i : Fin k => words i.succ.castSucc))
            (addr + 1 + k) (words (Fin.last k).succ) := rfl
      _ = Function.update (writeWords mem addr (fun i => words i.castSucc))
            (addr + (k + 1)) (words (.last (k + 1))) := by
          rw [hcast, hprev, show addr + 1 + k = addr + (k + 1) by omega, Fin.succ_last]
      _ = writeWords mem addr words := rfl

/-- Writing `k` words at `addr` realizes `words` on `Block.mk addr k`. -/
theorem Block.realizes_writeWords (mem : ℕ → ℕ) (addr : ℕ) {k : ℕ} (words : Fin k → ℕ) :
    (Block.mk addr k).Realizes (writeWords mem addr words) words := by
  induction k with
  | zero => exact fun i => Fin.elim0 i
  | succ k ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Block.read]
    · have hne : addr + j.val ≠ addr + k := by omega
      simpa only [Block.read, Fin.val_castSucc, writeWords_succ, Function.update_of_ne hne] using
        ih (fun i => words i.castSucc) j

@[simp]
theorem writeWords_add_fin (mem : ℕ → ℕ) (addr : ℕ) {k : ℕ} (words : Fin k → ℕ) (i : Fin k) :
    writeWords mem addr words (addr + i.val) = words i :=
  Block.realizes_writeWords mem addr words i

/-- Addresses outside `Block.mk addr k` are unchanged by `writeWords`. -/
theorem writeWords_of_not_owns {mem : ℕ → ℕ} {addr k a : ℕ} {words : Fin k → ℕ}
    (ha : ¬(Block.mk addr k).Owns a) : writeWords mem addr words a = mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Block.Owns] at ha
    rw [writeWords_succ, Function.update_of_ne (by omega)]
    exact ih (by simp only [Block.Owns]; omega)

/-- `writeWords mem addr words` modifies at most `(Block.mk addr k).footprint`. -/
theorem modifies_writeWords (mem : ℕ → ℕ) (addr : ℕ) {k : ℕ} (words : Fin k → ℕ) :
    Modifies (Block.mk addr k).footprint mem (writeWords mem addr words) :=
  fun _ ha => writeWords_of_not_owns (mt Block.mem_footprint.mpr ha)

/-! ## Typed fixed-width record specifications -/

/-- Specification of a fixed-width flat `k`-word memory layout for values of type `α`. -/
structure RecordSpec (α : Type*) (k : ℕ) where
  /-- The `k` consecutive words representing a record value. -/
  toWords : α → Fin k → ℕ

namespace RecordSpec

variable {α : Type*} {k : ℕ}

/-- Memory `mem` holds the `k`-word representation of `v` starting at `addr`.
Defined as an abbreviation of `Block.Realizes` so `ram_keep` applies directly. -/
abbrev HoldsAt (R : RecordSpec α k) (addr : ℕ) (v : α) (mem : ℕ → ℕ) : Prop :=
  (Block.mk addr k).Realizes mem (R.toWords v)

/-- Write the `k`-word representation of `v` into `mem` starting at `addr`. -/
abbrev write (R : RecordSpec α k) (addr : ℕ) (v : α) (mem : ℕ → ℕ) : ℕ → ℕ :=
  writeWords mem addr (R.toWords v)

theorem holdsAt_iff (R : RecordSpec α k) (addr : ℕ) (v : α) (mem : ℕ → ℕ) :
    R.HoldsAt addr v mem ↔ ∀ i : Fin k, mem (addr + i.val) = R.toWords v i :=
  Iff.rfl

/-- At most one value of `α` can hold at `addr` in a given memory when `R.toWords` is injective. -/
theorem HoldsAt.unique {R : RecordSpec α k} (hinj : Function.Injective R.toWords)
    {addr : ℕ} {u v : α} {mem : ℕ → ℕ}
    (hu : R.HoldsAt addr u mem) (hv : R.HoldsAt addr v mem) : u = v :=
  hinj (funext fun i => (hu i).symm.trans (hv i))

/-- Writing `v` at `addr` establishes `R.HoldsAt addr v`. -/
theorem holdsAt_write (R : RecordSpec α k) (addr : ℕ) (v : α) (mem : ℕ → ℕ) :
    R.HoldsAt addr v (R.write addr v mem) :=
  Block.realizes_writeWords mem addr (R.toWords v)

/-- After writing `v` at `addr`, `R.HoldsAt addr u` holds if and only if `u = v` when `R.toWords`
is injective. -/
theorem holdsAt_write_iff (R : RecordSpec α k) (hinj : Function.Injective R.toWords)
    (addr : ℕ) (u v : α) (mem : ℕ → ℕ) :
    R.HoldsAt addr u (R.write addr v mem) ↔ u = v :=
  ⟨fun hu => hu.unique hinj (R.holdsAt_write addr v mem),
    fun h => h ▸ R.holdsAt_write addr v mem⟩

end RecordSpec

/-! ## Right-associated composition rules for `appendCode` -/

/-- Exact instruction-count execution rule for `appendCode`. -/
theorem exec_append {B : Basis} {r w T₁ T₂ : ℕ} {c d : Code B r} {x y z : Data r}
    (h₁ : Exec w c x y T₁) (h₂ : Exec w d y z T₂) :
    Exec w (appendCode c d) x z (T₁ + T₂) := by
  induction c generalizing x T₁ with
  | seq c₁ c₂ _ ih =>
    cases h₁ with
    | seq he₁ he₂ =>
      simpa only [appendCode, Nat.add_assoc] using he₁.seq (ih he₂)
  | op _ | branch _ _ _ _ _ | loop _ _ _ | rand _ _ => exact h₁.seq h₂

/-- `appendCode` preserves register `i` when both parts preserve `i`. -/
theorem Code.preserves_appendCode {B : Basis} {r : ℕ} {c d : Code B r} {i : Fin r}
    (hc : c.Preserves i) (hd : d.Preserves i) : (appendCode c d).Preserves i := by
  induction c with
  | seq c₁ c₂ _ ih => exact ⟨hc.1, ih hc.2⟩
  | op _ | branch _ _ _ _ _ | loop _ _ _ | rand _ _ => exact ⟨hc, hd⟩

/-- `appendCode` avoids `width%` when both parts do. -/
theorem Code.not_readsWidth_appendCode {B : Basis} {r : ℕ} {c d : Code B r}
    (hc : ¬c.ReadsWidth) (hd : ¬d.ReadsWidth) : ¬(appendCode c d).ReadsWidth := by
  induction c with
  | seq c₁ c₂ _ ih =>
    have hc' : ¬c₁.ReadsWidth ∧ ¬c₂.ReadsWidth := not_or.mp hc
    exact not_or.mpr ⟨hc'.1, ih hc'.2⟩
  | op _ | branch _ _ _ _ _ | loop _ _ _ | rand _ _ =>
    exact not_or.mpr ⟨hc, hd⟩

/-- Continue symbolic `WP` execution from an exact-count routine contract. -/
theorem WP.of_exec_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin hy.within (hQ y hP)

/-- Continue symbolic `WP` execution across an exact-count prefix `c` of a right-nested
`ram[ … ]` block. -/
theorem WP.of_append_exec {B : Basis} {r w T₁ : ℕ} {c d : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T₁ ∧ P y)
    (hcont : ∀ y, P y → WP w d y fun z T₂ => Q z (T₂ + T₁)) :
    WP w (appendCode c d) x Q := by
  obtain ⟨y, hy, hP⟩ := h
  obtain ⟨z, T₂, hz, hQ⟩ := hcont y hP
  exact ⟨z, T₁ + T₂, execWithin_append hy.within hz, Nat.add_comm T₁ T₂ ▸ hQ⟩

/-- Discharge an `∃ y, ExecWithin w c x y T ∧ Q y` goal from a register-preservation lemma
`∀ i, P i → c.Preserves i` and a `WP` proof that receives `∀ i, P i → y.regs i = x.regs i`. -/
theorem WP.exists_execWithin_preserves {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Fin r → Prop} {Q : Data r → Prop}
    (hpres : ∀ i, P i → c.Preserves i)
    (hwp : WP w c x fun y t => t ≤ T ∧ ((∀ i, P i → y.regs i = x.regs i) → Q y)) :
    ∃ y, ExecWithin w c x y T ∧ Q y := by
  obtain ⟨y, he, hQ⟩ := WP.exists_execWithin hwp
  exact ⟨y, he, hQ fun i hi => he.regs_eq (hpres i hi)⟩

/-! ## Certified sequential cursor store and load routines -/

section Routines

variable {r : ℕ}

/-- Store `k ≥ 1` field registers at consecutive addresses starting from the address already in
`cursor`, stepping `cursor` by `one` between stores (`2 * k - 1` instructions). -/
@[expose] def storeCursor (cursor one : Fin r) : {k : ℕ} → [NeZero k] → (Fin k → Fin r) →
    Code .standard r
  | 0, h, _ => absurd rfl h.out
  | 1, _, fields => .op (.store cursor (fields 0))
  | k + 2, _, fields =>
    .seq (.op (.store cursor (fields 0)))
      (.seq (.op (.bin .add cursor cursor one))
        (storeCursor cursor one (k := k + 1) (fun i => fields i.succ)))

/-- Copy `addr` into `cursor` and store `k ≥ 1` field registers at `addr, …, addr + (k - 1)`
(`2 * k` instructions). Matches `ram[ cursor ← addr; *cursor ← f₀; cursor ← cursor + one; … ]`
definitionally. -/
@[expose] def storeRecord {k : ℕ} [NeZero k] (addr cursor one : Fin r) (fields : Fin k → Fin r) :
    Code .standard r :=
  .seq (.op (.copy cursor addr)) (storeCursor cursor one fields)

/-- Load `k ≥ 1` consecutive memory words starting from the address already in `cursor` into
`fields`, stepping `cursor` by `one` between loads (`2 * k - 1` instructions). -/
@[expose] def loadCursor (cursor one : Fin r) : {k : ℕ} → [NeZero k] → (Fin k → Fin r) →
    Code .standard r
  | 0, h, _ => absurd rfl h.out
  | 1, _, fields => .op (.load (fields 0) cursor)
  | k + 2, _, fields =>
    .seq (.op (.load (fields 0) cursor))
      (.seq (.op (.bin .add cursor cursor one))
        (loadCursor cursor one (k := k + 1) (fun i => fields i.succ)))

/-- Copy `addr` into `cursor` and load `k ≥ 1` consecutive words from `addr, …, addr + (k - 1)`
into `fields` (`2 * k` instructions). -/
@[expose] def loadRecord {k : ℕ} [NeZero k] (addr cursor one : Fin r) (fields : Fin k → Fin r) :
    Code .standard r :=
  .seq (.op (.copy cursor addr)) (loadCursor cursor one fields)

/-- Registers written by `loadCursor` and `loadRecord`: the address cursor and the target field
registers. -/
@[expose] def LoadRecordLocal {k : ℕ} (cursor : Fin r) (fields : Fin k → Fin r) (j : Fin r) :
    Prop :=
  j = cursor ∨ ∃ i, j = fields i

instance {k : ℕ} (cursor : Fin r) (fields : Fin k → Fin r) (j : Fin r) :
    Decidable (LoadRecordLocal cursor fields j) :=
  inferInstanceAs (Decidable (j = cursor ∨ ∃ i, j = fields i))

/-- `storeCursor` preserves every register except `cursor`. -/
theorem storeCursor_preserves {k : ℕ} [inst : NeZero k] (cursor one : Fin r)
    (fields : Fin k → Fin r) {j : Fin r} (hj : j ≠ cursor) :
    (storeCursor cursor one fields).Preserves j := by
  match k, inst, fields with
  | 0, h, _ => exact absurd rfl h.out
  | 1, _, _ => simp [storeCursor, Code.Preserves, Op.dest]
  | k + 2, _, fields =>
    simp only [storeCursor, Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq,
      reduceCtorEq, not_false_eq_true, true_and]
    exact ⟨hj.symm,
      storeCursor_preserves cursor one (k := k + 1) (fun i => fields i.succ) hj⟩

/-- `storeRecord` preserves every register except `cursor`. -/
theorem storeRecord_preserves {k : ℕ} [NeZero k] (addr cursor one : Fin r)
    (fields : Fin k → Fin r) {j : Fin r} (hj : j ≠ cursor) :
    (storeRecord addr cursor one fields).Preserves j := by
  simp only [storeRecord, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  exact ⟨hj.symm, storeCursor_preserves cursor one fields hj⟩

/-- `loadCursor` preserves every register outside `LoadRecordLocal cursor fields`. -/
theorem loadCursor_preserves {k : ℕ} [inst : NeZero k] (cursor one : Fin r)
    (fields : Fin k → Fin r) {j : Fin r} (hj : ¬LoadRecordLocal cursor fields j) :
    (loadCursor cursor one fields).Preserves j := by
  have hcur : j ≠ cursor := fun h => hj (Or.inl h)
  have hf : ∀ i, j ≠ fields i := fun i h => hj (Or.inr ⟨i, h⟩)
  match k, inst, fields, hf with
  | 0, h, _, _ => exact absurd rfl h.out
  | 1, _, fields, hf =>
    simp only [loadCursor, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    exact (hf 0).symm
  | k + 2, _, fields, hf =>
    simp only [loadCursor, Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
    refine ⟨(hf 0).symm, hcur.symm,
      loadCursor_preserves cursor one (k := k + 1) (fun i => fields i.succ) ?_⟩
    rintro (rfl | ⟨i, rfl⟩)
    · exact hcur rfl
    · exact hf i.succ rfl

/-- `loadRecord` preserves every register outside `LoadRecordLocal cursor fields`. -/
theorem loadRecord_preserves {k : ℕ} [NeZero k] (addr cursor one : Fin r)
    (fields : Fin k → Fin r) {j : Fin r} (hj : ¬LoadRecordLocal cursor fields j) :
    (loadRecord addr cursor one fields).Preserves j := by
  simp only [loadRecord, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  exact ⟨fun h => hj (Or.inl h.symm), loadCursor_preserves cursor one fields hj⟩

private theorem add_not_readsWidth (cursor one : Fin r) :
    ¬(Code.op (B := .standard) (Op.bin .add cursor cursor one)).ReadsWidth := by
  simp [Code.ReadsWidth, Op.ReadsWidth, Op.bin]

/-- `storeCursor` never inspects the physical word width. -/
theorem storeCursor_not_readsWidth {k : ℕ} [inst : NeZero k] (cursor one : Fin r)
    (fields : Fin k → Fin r) : ¬(storeCursor cursor one fields).ReadsWidth :=
  match k, inst, fields with
  | 0, h, _ => absurd rfl h.out
  | 1, _, _ => not_false
  | k + 2, _, fields =>
    not_or.mpr ⟨not_false, not_or.mpr ⟨add_not_readsWidth cursor one,
      storeCursor_not_readsWidth cursor one (k := k + 1) (fun i => fields i.succ)⟩⟩

/-- `storeRecord` never inspects the physical word width. -/
theorem storeRecord_not_readsWidth {k : ℕ} [NeZero k] (addr cursor one : Fin r)
    (fields : Fin k → Fin r) : ¬(storeRecord addr cursor one fields).ReadsWidth :=
  not_or.mpr ⟨not_false, storeCursor_not_readsWidth cursor one fields⟩

/-- `loadCursor` never inspects the physical word width. -/
theorem loadCursor_not_readsWidth {k : ℕ} [inst : NeZero k] (cursor one : Fin r)
    (fields : Fin k → Fin r) : ¬(loadCursor cursor one fields).ReadsWidth :=
  match k, inst, fields with
  | 0, h, _ => absurd rfl h.out
  | 1, _, _ => not_false
  | k + 2, _, fields =>
    not_or.mpr ⟨not_false, not_or.mpr ⟨add_not_readsWidth cursor one,
      loadCursor_not_readsWidth cursor one (k := k + 1) (fun i => fields i.succ)⟩⟩

/-- `loadRecord` never inspects the physical word width. -/
theorem loadRecord_not_readsWidth {k : ℕ} [NeZero k] (addr cursor one : Fin r)
    (fields : Fin k → Fin r) : ¬(loadRecord addr cursor one fields).ReadsWidth :=
  not_or.mpr ⟨not_false, loadCursor_not_readsWidth cursor one fields⟩

/-- Execute `storeCursor` in `2 * k - 1` instructions from an initialized cursor register. -/
theorem storeCursor_exec {k w : ℕ} [inst : NeZero k] (cursor one : Fin r) (fields : Fin k → Fin r)
    (x : Data r) (hone_ne : one ≠ cursor) (hfields_ne : ∀ i, fields i ≠ cursor)
    (hone : x.regs one = 1) (hfit : Fits w (x.regs cursor + (k - 1))) :
    ∃ y, Exec w (storeCursor cursor one fields) x y (2 * k - 1) ∧
      y.mem = writeWords x.mem (x.regs cursor) (fun i => x.regs (fields i)) ∧
      y.regs cursor = x.regs cursor + (k - 1) ∧
      ∀ j, j ≠ cursor → y.regs j = x.regs j := by
  match k, inst, fields, hfields_ne, hfit with
  | 0, h, _, _, _ => exact absurd rfl h.out
  | 1, _, fields, _, _ =>
    refine ⟨x.write (x.regs cursor) (x.regs (fields 0)), Exec.store, ?_, ?_, fun _ _ => rfl⟩
    · simp [writeWords, Data.write_mem]
    · simp
  | k + 2, _, fields, hfields_ne, hfit =>
    let x₁ := x.write (x.regs cursor) (x.regs (fields 0))
    let x₂ := x₁.set cursor (x.regs cursor + 1)
    have hstep₁ : Exec (B := .standard) w (.op (.store cursor (fields 0))) x x₁ 1 := Exec.store
    have hadd_fit : Fits w (BinOp.add.eval (x₁.regs cursor) (x₁.regs one)) := by
      simpa only [x₁, Data.write_regs, hone, BinOp.eval] using hfit.of_le (by omega)
    have hstep₂ : Exec w (.op (.bin .add cursor cursor one)) x₁ x₂ 1 := by
      simpa only [x₂, x₁, Data.write_regs, hone, BinOp.eval] using
        Exec.bin (f := .add) (d := cursor) (i := cursor) (j := one) (x := x₁) hadd_fit
    have hx₂_one : x₂.regs one = 1 := by
      simp [x₂, x₁, Data.set_regs, Function.update_of_ne hone_ne, hone]
    have hx₂_cur : x₂.regs cursor = x.regs cursor + 1 := by simp [x₂]
    obtain ⟨y, hy, hymem, hycur, hyregs⟩ :=
      storeCursor_exec (k := k + 1) cursor one (fun i => fields i.succ) x₂
        hone_ne (fun i => hfields_ne i.succ) hx₂_one
        (by rw [hx₂_cur]; exact hfit.of_le (by omega))
    have hfields_x₂ : (fun i : Fin (k + 1) => x₂.regs (fields i.succ)) =
        fun i : Fin (k + 1) => x.regs (fields i.succ) := by
      funext i
      simp [x₂, x₁, Data.set_regs, Function.update_of_ne (hfields_ne i.succ)]
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · have hseq := hstep₁.seq (hstep₂.seq hy)
      simpa only [storeCursor, show 1 + (1 + (2 * (k + 1) - 1)) = 2 * (k + 2) - 1 by omega]
        using hseq
    · rw [hymem, hx₂_cur, hfields_x₂]
      simpa only [x₂, x₁, Data.set_mem, Data.write_mem] using
        writeWords_cons x.mem (x.regs cursor) (fun i => x.regs (fields i))
    · rw [hycur, hx₂_cur]
      omega
    · intro j hj
      rw [hyregs j hj]
      simp [x₂, x₁, Data.set_regs, Function.update_of_ne hj]

private theorem initCursor_exec {k w : ℕ} [NeZero k] (addr cursor one : Fin r)
    (d : Code .standard r) (x : Data r) {P : Data r → Prop}
    (hone_ne : one ≠ cursor) (hone : x.regs one = 1)
    (hd : ∀ x₀ : Data r, x₀ = x.set cursor (x.regs addr) → x₀.regs one = 1 →
      x₀.regs cursor = x.regs addr → ∃ y, Exec w d x₀ y (2 * k - 1) ∧ P y) :
    ∃ y, Exec w (.seq (.op (.copy cursor addr)) d) x y (2 * k) ∧ P y := by
  let x₀ := x.set cursor (x.regs addr)
  have hcopy : Exec (B := .standard) w (.op (.copy cursor addr)) x x₀ 1 := Exec.copy
  have hx₀_one : x₀.regs one = 1 := by
    simp [x₀, Data.set_regs, Function.update_of_ne hone_ne, hone]
  obtain ⟨y, hy, hP⟩ := hd x₀ rfl hx₀_one (Data.set_regs_self x cursor (x.regs addr))
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact ⟨y, by simpa only [show 1 + (2 * k - 1) = 2 * k by omega] using hcopy.seq hy, hP⟩

/-- Execute `storeRecord` in `2 * k` exact instructions, writing `x.regs ∘ fields` at
`x.regs addr` and preserving all registers other than `cursor`. -/
theorem storeRecord_exec {k w : ℕ} [NeZero k] (addr cursor one : Fin r) (fields : Fin k → Fin r)
    (x : Data r) (hone_ne : one ≠ cursor) (hfields_ne : ∀ i, fields i ≠ cursor)
    (hone : x.regs one = 1) (hfit : Fits w (x.regs addr + (k - 1))) :
    ∃ y, Exec w (storeRecord addr cursor one fields) x y (2 * k) ∧
      y.mem = writeWords x.mem (x.regs addr) (fun i => x.regs (fields i)) ∧
      Modifies (Block.mk (x.regs addr) k).footprint x.mem y.mem ∧
      y.regs cursor = x.regs addr + (k - 1) ∧
      ∀ j, j ≠ cursor → y.regs j = x.regs j := by
  refine initCursor_exec (k := k) addr cursor one (storeCursor cursor one fields) x hone_ne hone
    fun x₀ hx₀ hx₀_one hx₀_cur => ?_
  obtain ⟨y, hy, hymem, hycur, hyregs⟩ :=
    storeCursor_exec cursor one fields x₀ hone_ne hfields_ne hx₀_one (by rwa [hx₀_cur])
  have hfields_x₀ : (fun i : Fin k => x₀.regs (fields i)) = fun i => x.regs (fields i) := by
    funext i
    simp [hx₀, Data.set_regs, Function.update_of_ne (hfields_ne i)]
  have hmem : y.mem = writeWords x.mem (x.regs addr) (fun i => x.regs (fields i)) := by
    rw [hx₀_cur, hfields_x₀] at hymem
    simpa only [hx₀, Data.set_mem] using hymem
  refine ⟨y, hy, hmem, hmem ▸ modifies_writeWords x.mem (x.regs addr) _, ?_, ?_⟩
  · rwa [hx₀_cur] at hycur
  · intro j hj
    rw [hyregs j hj, hx₀]
    simp [Data.set_regs, Function.update_of_ne hj]

/-- Execute `storeRecord` for a typed `RecordSpec α k` value held across `fields`. -/
theorem RecordSpec.store_exec {α : Type*} {k w : ℕ} [NeZero k] (R : RecordSpec α k)
    (addr cursor one : Fin r) (fields : Fin k → Fin r) (v : α) (x : Data r)
    (hone_ne : one ≠ cursor) (hfields_ne : ∀ i, fields i ≠ cursor)
    (hone : x.regs one = 1) (hfields : ∀ i, x.regs (fields i) = R.toWords v i)
    (hfit : Fits w (x.regs addr + (k - 1))) :
    ∃ y, Exec w (storeRecord addr cursor one fields) x y (2 * k) ∧
      R.HoldsAt (x.regs addr) v y.mem ∧
      y.mem = R.write (x.regs addr) v x.mem ∧
      Modifies (Block.mk (x.regs addr) k).footprint x.mem y.mem ∧
      ∀ j, j ≠ cursor → y.regs j = x.regs j := by
  obtain ⟨y, hy, hymem, hmod, _, hyregs⟩ :=
    storeRecord_exec addr cursor one fields x hone_ne hfields_ne hone hfit
  have hwords : (fun i => x.regs (fields i)) = R.toWords v := funext hfields
  rw [hwords] at hymem
  exact ⟨y, hy, hymem ▸ R.holdsAt_write (x.regs addr) v x.mem, hymem, hmod, hyregs⟩

/-- Execute `loadCursor` in `2 * k - 1` instructions from an initialized cursor register. -/
theorem loadCursor_exec {k w : ℕ} [inst : NeZero k] (cursor one : Fin r) (fields : Fin k → Fin r)
    (x : Data r) (hone_ne : one ≠ cursor) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hone : x.regs one = 1) (hfit : Fits w (x.regs cursor + (k - 1))) :
    ∃ y, Exec w (loadCursor cursor one fields) x y (2 * k - 1) ∧
      y.mem = x.mem ∧
      (∀ i, y.regs (fields i) = x.mem (x.regs cursor + i.val)) ∧
      y.regs cursor = x.regs cursor + (k - 1) ∧
      ∀ j, ¬LoadRecordLocal cursor fields j → y.regs j = x.regs j := by
  match k, inst, fields, hfields_cur, hfields_one, hinj, hfit with
  | 0, h, _, _, _, _, _ => exact absurd rfl h.out
  | 1, _, fields, hfields_cur, _, _, _ =>
    let y := x.set (fields 0) (x.mem (x.regs cursor))
    refine ⟨y, Exec.load, rfl, ?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simp [y]
    · simp [y, Data.set_regs, Function.update_of_ne (hfields_cur 0).symm]
    · intro j hj
      have hne : j ≠ fields 0 := fun h => hj (Or.inr ⟨0, h⟩)
      simp [y, Data.set_regs, Function.update_of_ne hne]
  | k + 2, _, fields, hfields_cur, hfields_one, hinj, hfit =>
    let x₁ := x.set (fields 0) (x.mem (x.regs cursor))
    let x₂ := x₁.set cursor (x.regs cursor + 1)
    have hstep₁ : Exec (B := .standard) w (.op (.load (fields 0) cursor)) x x₁ 1 := Exec.load
    have hx₁_cur : x₁.regs cursor = x.regs cursor := by
      simp [x₁, Data.set_regs, Function.update_of_ne (hfields_cur 0).symm]
    have hx₁_one : x₁.regs one = 1 := by
      simp [x₁, Data.set_regs, Function.update_of_ne (hfields_one 0).symm, hone]
    have hadd_fit : Fits w (BinOp.add.eval (x₁.regs cursor) (x₁.regs one)) := by
      simpa only [hx₁_cur, hx₁_one, BinOp.eval] using hfit.of_le (by omega)
    have hstep₂ : Exec w (.op (.bin .add cursor cursor one)) x₁ x₂ 1 := by
      simpa only [x₂, hx₁_cur, hx₁_one, BinOp.eval] using
        Exec.bin (f := .add) (d := cursor) (i := cursor) (j := one) (x := x₁) hadd_fit
    have hx₂_one : x₂.regs one = 1 := by
      simp [x₂, Data.set_regs, Function.update_of_ne hone_ne, hx₁_one]
    have hx₂_cur : x₂.regs cursor = x.regs cursor + 1 := by simp [x₂]
    obtain ⟨y, hy, hymem, hyfields, hycur, hyregs⟩ :=
      loadCursor_exec (k := k + 1) cursor one (fun i => fields i.succ) x₂
        hone_ne (fun i => hfields_cur i.succ) (fun i => hfields_one i.succ)
        (fun i j h => Fin.succ_injective _ (hinj h)) hx₂_one
        (by rw [hx₂_cur]; exact hfit.of_le (by omega))
    refine ⟨y, ?_, hymem, ?_, ?_, ?_⟩
    · have hseq := hstep₁.seq (hstep₂.seq hy)
      simpa only [loadCursor, show 1 + (1 + (2 * (k + 1) - 1)) = 2 * (k + 2) - 1 by omega]
        using hseq
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · have hnot : ¬LoadRecordLocal cursor (fun i : Fin (k + 1) => fields i.succ) (fields 0) := by
          rintro (h | ⟨j, h⟩)
          · exact hfields_cur 0 h
          · exact Fin.succ_ne_zero j (hinj h.symm)
        rw [hyregs (fields 0) hnot]
        simp [x₂, x₁, Data.set_regs, Function.update_of_ne (hfields_cur 0)]
      · rw [hyfields i', hx₂_cur]
        change x.mem (x.regs cursor + 1 + i'.val) = x.mem (x.regs cursor + (i'.val + 1))
        congr 1
        omega
    · rw [hycur, hx₂_cur]
      omega
    · intro j hj
      have hcur : j ≠ cursor := fun h => hj (Or.inl h)
      have hf0 : j ≠ fields 0 := fun h => hj (Or.inr ⟨0, h⟩)
      have hnot : ¬LoadRecordLocal cursor (fun i : Fin (k + 1) => fields i.succ) j := by
        rintro (h | ⟨i, h⟩)
        · exact hcur h
        · exact hj (Or.inr ⟨i.succ, h⟩)
      rw [hyregs j hnot]
      simp [x₂, x₁, Data.set_regs, Function.update_of_ne hcur, Function.update_of_ne hf0]

/-- Execute `loadRecord` in `2 * k` exact instructions, loading `x.mem (x.regs addr + i)` into
`fields i` and preserving memory and all registers outside `LoadRecordLocal cursor fields`. -/
theorem loadRecord_exec {k w : ℕ} [NeZero k] (addr cursor one : Fin r) (fields : Fin k → Fin r)
    (x : Data r) (hone_ne : one ≠ cursor) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hone : x.regs one = 1) (hfit : Fits w (x.regs addr + (k - 1))) :
    ∃ y, Exec w (loadRecord addr cursor one fields) x y (2 * k) ∧
      y.mem = x.mem ∧
      (∀ i, y.regs (fields i) = x.mem (x.regs addr + i.val)) ∧
      y.regs cursor = x.regs addr + (k - 1) ∧
      ∀ j, ¬LoadRecordLocal cursor fields j → y.regs j = x.regs j := by
  refine initCursor_exec (k := k) addr cursor one (loadCursor cursor one fields) x hone_ne hone
    fun x₀ hx₀ hx₀_one hx₀_cur => ?_
  obtain ⟨y, hy, hymem, hyfields, hycur, hyregs⟩ :=
    loadCursor_exec cursor one fields x₀ hone_ne hfields_cur hfields_one hinj hx₀_one
      (by rwa [hx₀_cur])
  refine ⟨y, hy, by simpa [hx₀] using hymem, ?_, ?_, ?_⟩
  · intro i
    have hi := hyfields i
    rw [hx₀_cur] at hi
    simpa only [hx₀, Data.set_mem] using hi
  · rwa [hx₀_cur] at hycur
  · intro j hj
    have hcur : j ≠ cursor := fun h => hj (Or.inl h)
    rw [hyregs j hj, hx₀]
    simp [Data.set_regs, Function.update_of_ne hcur]

/-- Execute `loadRecord` when `R.HoldsAt (x.regs addr) v x.mem`, placing `R.toWords v i` in each
`fields i`. -/
theorem RecordSpec.load_exec {α : Type*} {k w : ℕ} [NeZero k] (R : RecordSpec α k)
    (addr cursor one : Fin r) (fields : Fin k → Fin r) (v : α) (x : Data r)
    (hone_ne : one ≠ cursor) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hone : x.regs one = 1) (hmem : R.HoldsAt (x.regs addr) v x.mem)
    (hfit : Fits w (x.regs addr + (k - 1))) :
    ∃ y, Exec w (loadRecord addr cursor one fields) x y (2 * k) ∧
      y.mem = x.mem ∧
      (∀ i, y.regs (fields i) = R.toWords v i) ∧
      ∀ j, ¬LoadRecordLocal cursor fields j → y.regs j = x.regs j := by
  obtain ⟨y, hy, hymem, hyfields, _, hyregs⟩ :=
    loadRecord_exec addr cursor one fields x hone_ne hfields_cur hfields_one hinj hone hfit
  exact ⟨y, hy, hymem, fun i => (hyfields i).trans (hmem i), hyregs⟩

/-- Reloading a `k`-word record whose memory cells at `x.regs addr` already match `x.regs ∘ fields`
leaves every register except `cursor` unchanged. -/
theorem loadRecord_exec_self {k w : ℕ} [NeZero k] (addr cursor one : Fin r)
    (fields : Fin k → Fin r) (x : Data r)
    (hone_ne : one ≠ cursor) (hfields_cur : ∀ i, fields i ≠ cursor)
    (hfields_one : ∀ i, fields i ≠ one) (hinj : Function.Injective fields)
    (hone : x.regs one = 1) (hmem : ∀ i, x.mem (x.regs addr + i.val) = x.regs (fields i))
    (hfit : Fits w (x.regs addr + (k - 1))) :
    ∃ y, Exec w (loadRecord addr cursor one fields) x y (2 * k) ∧
      y.mem = x.mem ∧
      ∀ j, j ≠ cursor → y.regs j = x.regs j := by
  obtain ⟨y, hy, hymem, hyfields, _, hyregs⟩ :=
    loadRecord_exec addr cursor one fields x hone_ne hfields_cur hfields_one hinj hone hfit
  refine ⟨y, hy, hymem, ?_⟩
  intro j hj
  by_cases hloc : LoadRecordLocal cursor fields j
  · rcases hloc with rfl | ⟨i, rfl⟩
    · exact absurd rfl hj
    · exact (hyfields i).trans (hmem i)
  · exact hyregs j hloc

end Routines

end Cslib.WordRAM

end
