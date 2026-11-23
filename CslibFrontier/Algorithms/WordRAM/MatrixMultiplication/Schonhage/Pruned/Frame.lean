/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
public import CslibFrontier.Computability.WordRAM.Record

/-!
# Native stack layout and frame loading

## Main results

* `PrunedQuery.exec_locate`: compute the actual stack/list/value/timestamp region addresses.
* `PrunedQuery.exec_loadFrame`: load all four stored frame words via `Cslib.WordRAM.loadRecord`
  and compute row addresses.

Every index multiplication, pointer addition and load is an ordinary charged instruction.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Target field registers of `loadFrame`. -/
private abbrev frameFields : Fin 4 → Fin registers := ![count, leafPrefix, stride, term]

/-- Exactly the registers used to locate the concrete workspace regions. -/
def LocateLocal (i : Fin registers) : Prop :=
  i = frames ∨ i = temporary ∨ i = temporary₂ ∨ i = lists ∨ i = values ∨ i = stamps

instance (i : Fin registers) : Decidable (LocateLocal i) :=
  inferInstanceAs (Decidable
    (i = frames ∨ i = temporary ∨ i = temporary₂ ∨ i = lists ∨ i = values ∨ i = stamps))

private theorem locate_preserves (i : Fin registers) :
    ¬LocateLocal i → locate.Preserves i := by decide +kernel +revert

/-- The seven actual instructions compute the workspace partition from depth and array size. -/
theorem exec_locate {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4)
    (hw : Fits w (x.regs scratch + 4 * (x.regs inputDepth + 1) +
      2 * (x.regs inputDepth + 1) * x.regs span + x.regs inputDepth + 8)) :
    ∃ y, ExecWithin w locate x y 7 ∧ y.mem = x.mem ∧
      y.regs frames = x.regs scratch ∧
      y.regs lists = x.regs scratch + 4 * (x.regs inputDepth + 1) ∧
      y.regs values = x.regs scratch + 4 * (x.regs inputDepth + 1) +
        (x.regs inputDepth + 1) * x.regs span ∧
      y.regs stamps = x.regs scratch + 4 * (x.regs inputDepth + 1) +
        2 * (x.regs inputDepth + 1) * x.regs span ∧
      (∀ i, ¬LocateLocal i → y.regs i = x.regs i) := by
  have hds : Fits w ((x.regs inputDepth + 1) * x.regs span) := hw.of_le (by nlinarith)
  have hv : Fits w (x.regs scratch + 4 * (x.regs inputDepth + 1) +
      (x.regs inputDepth + 1) * x.regs span) := hw.of_le (by nlinarith)
  have hs : Fits w (x.regs scratch + 4 * (x.regs inputDepth + 1) +
      (x.regs inputDepth + 1) * x.regs span + (x.regs inputDepth + 1) * x.regs span) :=
    hw.of_le (by nlinarith)
  refine WP.exists_execWithin_preserves locate_preserves ?_
  unfold locate
  wram_exec [h1, h4, hds, hv, hs]
  intro hregs
  wram_simp
  exact ⟨by ring, by ring, by ring, hregs⟩

/-- Registers written while loading one stack frame and computing the two depth rows. -/
def LoadFrameLocal (i : Fin registers) : Prop :=
  i = frame ∨ i = address ∨ i = count ∨ i = leafPrefix ∨ i = stride ∨ i = term ∨
    i = temporary ∨ i = listBase ∨ i = valueBase ∨ i = nextLevel ∨ i = childList ∨
    i = childValues

instance (i : Fin registers) : Decidable (LoadFrameLocal i) :=
  inferInstanceAs (Decidable
    (i = frame ∨ i = address ∨ i = count ∨ i = leafPrefix ∨ i = stride ∨ i = term ∨
      i = temporary ∨ i = listBase ∨ i = valueBase ∨ i = nextLevel ∨ i = childList ∨
      i = childValues))

private theorem loadFrame_preserves (i : Fin registers) :
    ¬LoadFrameLocal i → loadFrame.Preserves i := by decide +kernel +revert

/-- Seventeen native instructions load the four words at the computed frame address and
locate the current and child rows. The memory words are read, not supplied as frame arguments. -/
theorem exec_loadFrame {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (h4 : x.regs frameWidth = 4)
    (hw : Fits w (x.regs frames + 4 * (x.regs level + 1) + x.regs lists +
      x.regs values + (x.regs level + 1) * x.regs span + x.regs level + 8)) :
    ∃ y, ExecWithin w loadFrame x y 17 ∧ y.mem = x.mem ∧
      y.regs frame = x.regs frames + 4 * x.regs level ∧
      y.regs count = x.mem (x.regs frames + 4 * x.regs level) ∧
      y.regs leafPrefix = x.mem (x.regs frames + 4 * x.regs level + 1) ∧
      y.regs stride = x.mem (x.regs frames + 4 * x.regs level + 2) ∧
      y.regs term = x.mem (x.regs frames + 4 * x.regs level + 3) ∧
      y.regs listBase = x.regs lists + x.regs level * x.regs span ∧
      y.regs valueBase = x.regs values + x.regs level * x.regs span ∧
      y.regs nextLevel = x.regs level + 1 ∧
      y.regs childList = x.regs lists + (x.regs level + 1) * x.regs span ∧
      y.regs childValues = x.regs values + (x.regs level + 1) * x.regs span ∧
      (∀ i, ¬LoadFrameLocal i → y.regs i = x.regs i) := by
  have hcode : loadFrame = ram[
      frame ← level * frameWidth; frame ← frames + frame;
      ⟪appendCode (loadRecord frame address one frameFields) (ram[
        temporary ← level * span; listBase ← lists + temporary;
        valueBase ← values + temporary;
        nextLevel ← level + one; temporary ← nextLevel * span;
        childList ← lists + temporary; childValues ← values + temporary ])⟫ ] := rfl
  refine WP.exists_execWithin_preserves loadFrame_preserves ?_
  rw [hcode]
  wram_exec [h1, h4]
  refine WP.of_append_exec
    (loadRecord_exec frame address one frameFields _
      (by decide) (by decide) (by decide) (by decide)
      (by wram_simp; exact h1)
      (by wram_simp; exact hw.of_le (by omega))) ?_
  rintro u ⟨humem, hufields, _, huregs⟩
  wram_simp at humem hufields
  have u1 : u.regs one = 1 := (huregs one (by decide)).trans (by wram_simp; exact h1)
  have ulev : u.regs level = x.regs level := (huregs level (by decide)).trans (by wram_simp)
  have uspan : u.regs span = x.regs span := (huregs span (by decide)).trans (by wram_simp)
  have ulists : u.regs lists = x.regs lists := (huregs lists (by decide)).trans (by wram_simp)
  have uvals : u.regs values = x.regs values := (huregs values (by decide)).trans (by wram_simp)
  have uframe : u.regs frame = x.regs frames + 4 * x.regs level :=
    (huregs frame (by decide)).trans (by wram_simp; ring)
  have hf0 : x.regs frames + x.regs level * 4 = x.regs frames + 4 * x.regs level := by ring
  wram_exec [u1, ulev, uspan, ulists, uvals,
    show Fits w (x.regs level * x.regs span) from hw.of_le (by nlinarith),
    show Fits w ((x.regs level + 1) * x.regs span) from hw.of_le (by nlinarith),
    show Fits w (x.regs lists + x.regs level * x.regs span) from hw.of_le (by nlinarith),
    show Fits w (x.regs values + x.regs level * x.regs span) from hw.of_le (by nlinarith),
    show Fits w (x.regs lists + (x.regs level + 1) * x.regs span) from hw.of_le (by nlinarith),
    show Fits w (x.regs values + (x.regs level + 1) * x.regs span) from hw.of_le (by nlinarith)]
  intro hregs
  wram_simp [uframe, humem]
  exact ⟨by simpa [frameFields, hf0] using hufields 0,
    by simpa [frameFields, hf0] using hufields 1,
    by simpa [frameFields, hf0] using hufields 2,
    by simpa [frameFields, hf0] using hufields 3, hregs⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
