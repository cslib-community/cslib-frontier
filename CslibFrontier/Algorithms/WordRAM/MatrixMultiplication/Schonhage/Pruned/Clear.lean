/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Control

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Sparse initialization of requested accumulators

## Main definitions

* `PrunedQuery.zeroQueryPrefix`: the memory after zeroing a listed prefix of query addresses.

## Main results

* `PrunedQuery.exec_clearRequested`: actual indexed clearing within `7 N + 3` instructions.

Repeated requests are permitted. Unlisted cells are preserved, and no dense value directory
is initialized by this routine.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Finset

/-- Clear precisely the addresses named in the processed prefix of an explicit query list. -/
def zeroQueryPrefix (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  ((range k).image (fun i => base + input i)).piecewise (fun _ => 0) mem

/-- Clearing no requests leaves memory unchanged. -/
@[simp]
theorem zeroQueryPrefix_zero (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) :
    zeroQueryPrefix mem base input 0 = mem := by
  funext a
  simp only [zeroQueryPrefix, Finset.range_zero, Finset.image_empty, Finset.piecewise,
    Finset.notMem_empty, ↓reduceIte]

/-- One additional listed request is exactly one memory store, including repeated requests. -/
theorem zeroQueryPrefix_succ (mem : ℕ → ℕ) (base : ℕ) (input : ℕ → ℕ) (k : ℕ) :
    zeroQueryPrefix mem base input (k + 1) =
      Function.update (zeroQueryPrefix mem base input k) (base + input k) 0 := by
  unfold zeroQueryPrefix
  rw [Finset.range_add_one, Finset.image_insert, Finset.piecewise_insert]

/-- Every cell outside the concrete value directory is preserved by a bounded prefix. -/
theorem zeroQueryPrefix_outside {mem : ℕ → ℕ} {base capacity k : ℕ} {input : ℕ → ℕ}
    (hcode : ∀ i < k, input i < capacity) {a : ℕ}
    (ha : ¬(Block.mk base capacity).Owns a) : zeroQueryPrefix mem base input k a = mem a := by
  simp only [zeroQueryPrefix, piecewise, mem_image, mem_range, ite_eq_right_iff,
    forall_exists_index, and_imp]
  rintro i hi rfl
  exact absurd (show (Block.mk base capacity).Owns (base + input i) from
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (hcode i hi) _⟩) ha

/-- Every requested value in the processed prefix is actually zero in the resulting memory. -/
theorem zeroQueryPrefix_at {mem : ℕ → ℕ} {base k i : ℕ} {input : ℕ → ℕ} (hi : i < k) :
    zeroQueryPrefix mem base input k (base + input i) = 0 := by
  have hmem : base + input i ∈ (range k).image (fun j => base + input j) :=
    mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
  simp only [zeroQueryPrefix, piecewise, hmem, ↓reduceIte]

/-- Registers modified by sparse clearing. -/
def ClearLocal (i : Fin registers) : Prop := i = address ∨ i = query ∨ i = index

instance (i : Fin registers) : Decidable (ClearLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = query ∨ i = index))

/-- Each requested word costs an indexed source load, indexed zero store and increment. -/
theorem exec_clearValueStep {w : ℕ} (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hr : Fits w (x.regs listBase + x.regs index))
    (hv : Fits w (x.regs valueBase + q)) (hi : Fits w (x.regs index + 1)) :
    ∃ y, ExecWithin w clearValueStep x y 5 ∧ y.regs index = x.regs index + 1 ∧
      y.mem = Function.update x.mem (x.regs valueBase + q) 0 ∧
      (∀ i, ¬ClearLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [clearValueStep, hq, h0, h1, hr, hv, hi]
  refine ⟨by wram_simp, by wram_simp, fun i h => ?_⟩
  simp only [ClearLocal, not_or] at h
  rcases h with ⟨h1', h2', h3'⟩
  wram_simp

/-- The fixed native clearing loop visits only explicit requests. Width follows from concrete
source/destination endpoints and lengths, and source preservation follows from their separation. -/
theorem exec_clearRequested {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcode : ∀ i < N, input i < capacity)
    (hsep : x.regs listBase + N ≤ x.regs valueBase ∨
      x.regs valueBase + capacity ≤ x.regs listBase)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (hw : Fits w (x.regs listBase + N + x.regs valueBase + capacity + N + 2)) :
    ∃ y, ExecWithin w clearRequested x y (7 * N + 3) ∧ y.regs index = N ∧
      y.mem = zeroQueryPrefix x.mem (x.regs valueBase) input N ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ i, ¬ClearLocal i → y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data registers) : Prop :=
    y.mem = zeroQueryPrefix x.mem (x.regs valueBase) input j ∧
    (∀ i, ¬ClearLocal i → y.regs i = x.regs i)
  have hread (j : ℕ) (y : Data registers) (hj : j ≤ N) (hy : P j y) (i : ℕ) (hi : i < N) :
      y.mem (x.regs listBase + i) = input i := by
    rw [hy.1, zeroQueryPrefix_outside (fun j hj => hcode j (by omega))]
    · exact hinput i hi
    · change ¬(x.regs valueBase ≤ x.regs listBase + i ∧
        x.regs listBase + i < x.regs valueBase + capacity)
      rcases hsep with h | h <;> omega
  have hstep (y : Data registers) (hy : P (y.regs index) y) (hk : y.regs index < N) :
      ∃ z, ExecWithin w clearValueStep y z 5 ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1 := by
    obtain ⟨hm, hf⟩ := hy
    have hb := hf listBase (by decide)
    have hv := hf valueBase (by decide)
    have hq := hcode (y.regs index) hk
    obtain ⟨z, hz, hi, hmem, hregs⟩ := exec_clearValueStep y (input (y.regs index))
      (by rw [hb]; exact hread (y.regs index) y hk.le ⟨hm, hf⟩ _ hk) (by regs_frame) (by regs_frame)
      (hw.of_le (by rw [hb]; omega)) (hw.of_le (by rw [hv]; omega)) (hw.of_le (by omega))
    refine ⟨z, hz, ⟨?_, fun i hi => (hregs i hi).trans (hf i hi)⟩, hi⟩
    rw [hmem, hm, hv, zeroQueryPrefix_succ]
  refine WP.exists_execWithin ?_
  wram_exec [clearRequested]
  wram_call (ExecWithin.loop_count P (fun _ hy => (hy.2 count (by decide)).trans hN) hstep
    (by wram_simp; exact Nat.zero_le _)
    ⟨by wram_simp; exact (zeroQueryPrefix_zero _ _ _).symm, fun i hi => by
      simp only [ClearLocal, not_or] at hi; rcases hi with ⟨_, _, h3⟩; wram_simp⟩)
    with y ⟨hIy, hindex⟩
  exact ⟨by wram_simp; omega, hindex, hIy.1, hread N y le_rfl hIy, hIy.2⟩

/-- Registers changed by a complete internal-node initialization. -/
def ClearValuesLocal (i : Fin registers) : Prop := ClearLocal i ∨ AdvanceLocal i

instance (i : Fin registers) : Decidable (ClearValuesLocal i) :=
  inferInstanceAs (Decidable (ClearLocal i ∨ AdvanceLocal i))

/-- Sparse clearing and actual stored-frame initialization together cost `7 N + 8` instructions.
The source list is preserved; the only additional memory write is its frame's fourth word. -/
theorem exec_clearValues {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcode : ∀ i < N, input i < capacity)
    (hsep : x.regs listBase + N ≤ x.regs valueBase ∨
      x.regs valueBase + capacity ≤ x.regs listBase)
    (hframeSep : x.regs frame + 4 ≤ x.regs listBase ∨
      x.regs listBase + N ≤ x.regs frame)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1) (h4 : x.regs frameWidth = 4)
    (hw : Fits w (x.regs listBase + N + x.regs valueBase + capacity + N + 2))
    (hf : Fits w (x.regs frame + 4)) :
    ∃ y, ExecWithin w clearValues x y (7 * N + 8) ∧ y.regs index = N ∧
      y.regs term = 0 ∧ y.regs mode = 1 ∧
      y.mem = Function.update (zeroQueryPrefix x.mem (x.regs valueBase) input N)
        (x.regs frame + 3) 0 ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ i, ¬ClearValuesLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  unfold clearValues
  wram_call (exec_clearRequested x input hN hinput hcode hsep h0 h1 hw)
    with z ⟨hindex, hmem, hread, hregs⟩
  have hframe := hregs frame (by decide)
  wram_call (exec_clearValuesFinish z (by regs_frame) (by regs_frame) (by rwa [hframe]))
    with y ⟨hterm, hmode, hmem', hregs'⟩
  have hm : y.mem = Function.update z.mem (x.regs frame + 3) 0 := by simpa only [hframe] using hmem'
  refine ⟨by omega, by regs_frame, hterm, hmode, by rw [hm, hmem], ?_, fun i hi => ?_⟩
  · intro i hi
    have hne : x.regs listBase + i ≠ x.regs frame + 3 := by
      rcases hframeSep with h | h <;> omega
    rw [hm, Function.update_of_ne hne]
    exact hread i hi
  · simp only [ClearValuesLocal, not_or] at hi
    exact (hregs' i hi.2).trans (hregs i hi.1)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
