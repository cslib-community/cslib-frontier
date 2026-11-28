/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Control
public import CslibFrontier.Computability.WordRAM.Record

/-!
# Computed child-frame writes

## Main results

* `PrunedQuery.exec_push`: compute the next stack address, prefix and stride, store all four
  child-frame words via `Cslib.WordRAM.storeRecord_exec`, and enter that frame in fifteen
  native instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed while constructing and entering one child frame. -/
def PushLocal (i : Fin registers) : Prop :=
  i = childFrame ∨ i = temporary₂ ∨ i = childPrefix ∨ i = childStride ∨ i = address ∨
    i = level ∨ i = mode

instance (i : Fin registers) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable
    (i = childFrame ∨ i = temporary₂ ∨ i = childPrefix ∨ i = childStride ∨ i = address ∨
      i = level ∨ i = mode))

private theorem push_preserves (i : Fin registers) : ¬PushLocal i → push.Preserves i := by
  decide +kernel +revert

/-- Source field registers of `push`. -/
private abbrev pushFields : Fin 4 → Fin registers :=
  ![childCount, childPrefix, childStride, nil]

/-- The child list's actual count is written to the computed frame, followed by the new leaf
prefix, stride and zero term counter. All scalar fit premises follow from the displayed budget. -/
theorem exec_push {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (h4 : x.regs frameWidth = 4) (h10 : x.regs ten = 10)
    (hw : Fits w (x.regs frames + x.regs nextLevel * 4 + x.regs leafPrefix +
      x.regs term * x.regs stride + x.regs stride * 10 + 8)) :
    ∃ y, ExecWithin w push x y 15 ∧ y.regs level = x.regs nextLevel ∧ y.regs mode = 0 ∧
      y.regs childFrame = x.regs frames + x.regs nextLevel * 4 ∧
      y.regs childPrefix = x.regs leafPrefix + x.regs term * x.regs stride ∧
      y.regs childStride = x.regs stride * 10 ∧
      y.mem = writeWords x.mem (x.regs frames + x.regs nextLevel * 4)
        ![x.regs childCount, x.regs leafPrefix + x.regs term * x.regs stride,
          x.regs stride * 10, 0] ∧
      Modifies (Block.mk (x.regs frames + x.regs nextLevel * 4) 4).footprint x.mem y.mem ∧
      (∀ i, ¬PushLocal i → y.regs i = x.regs i) := by
  have hcode : push = ram[
      childFrame ← nextLevel * frameWidth; childFrame ← frames + childFrame;
      temporary₂ ← term * stride; childPrefix ← leafPrefix + temporary₂;
      childStride ← stride * ten;
      ⟪appendCode (storeRecord childFrame address one pushFields)
        (ram[ level ← nextLevel; mode ← #0 ])⟫ ] := rfl
  refine WP.exists_execWithin_preserves push_preserves ?_
  rw [hcode]
  wram_exec [h0, h1, h4, h10]
  refine WP.of_append_exec
    (storeRecord_exec childFrame address one pushFields _
      (by decide) (by decide)
      (by wram_simp; exact h1)
      (by wram_simp; exact hw.of_le (by omega))) ?_
  rintro u ⟨humem, humod, _, huregs⟩
  wram_simp at humem humod
  have humem' : u.mem = writeWords x.mem (x.regs frames + x.regs nextLevel * 4)
      ![x.regs childCount, x.regs leafPrefix + x.regs term * x.regs stride,
        x.regs stride * 10, 0] := by
    rw [humem]
    congr 1
    funext i
    match i with
    | 0 | 1 => wram_simp
    | 2 => wram_simp; rfl
    | 3 => wram_simp; exact h0
  have unext : u.regs nextLevel = x.regs nextLevel :=
    (huregs nextLevel (by decide)).trans (by wram_simp)
  wram_exec [unext]
  intro hregs
  wram_simp [huregs childFrame (by decide), huregs childPrefix (by decide),
    huregs childStride (by decide)]
  exact ⟨humem', humod, hregs⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
