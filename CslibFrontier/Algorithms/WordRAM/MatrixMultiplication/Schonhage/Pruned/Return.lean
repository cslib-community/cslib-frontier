/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Accumulate
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# The actual controller phase after a child returns

## Main results

* `PrunedQuery.exec_node_return`: load the parent frame, add the returned child only at
  contributing requests, and advance the stored term counter.

The value-directory hypotheses describe ordinary memory established by the child proof.
They do not assume a child execution or its cost. All native accumulation and controller
instructions are proved and charged here.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed Finset

/-- The complete parent-return phase, including its real frame loads, two mode comparisons,
signed indexed-add loop and stored counter increment. Unselected child cells are not read. -/
theorem exec_node_return {w L f a0 b0 d N k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 2) (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ) (V B : ℕ → ℤ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L) (hinj : Set.InjOn input {i | i < N})
    (hparent : ∀ i < N,
      x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + input i) =
        encode (V (input i)))
    (hchild : ∀ i < N, selected true k (input i) →
      x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + (d + 1) * 10 ^ L + input i / 10) =
        encode (B (input i / 10)))
    (hV : ∀ i < N, GenericRAM.Signed.Fits w (V (input i)))
    (hB : ∀ i < N, GenericRAM.Signed.Fits w (B (input i / 10)))
    (hw : Fits (w + 2) (8 * f + 64 * (L + 1) * 10 ^ L + 128)) :
    ∃ y, ExecWithin (w + 2) step x y (31 * N + 29) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d ∧ y.regs mode = 1 ∧ y.regs active = x.regs active ∧
      y.regs epoch = x.regs epoch ∧
      (∀ i < N,
        y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + input i) =
          encode (V (input i) + if selected true k (input i) then B (input i / 10) else 0)) ∧
      (∀ j < 3, y.mem (f + 4 * d + j) = x.mem (f + 4 * d + j)) ∧
      y.mem (f + 4 * d + 3) = k + 1 ∧
      (∀ q < 10 ^ L,
        y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) =
          x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q)) ∧
      Modifies (nodeWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.mul_le_mul_right _ (by omega)
  let vb := f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L
  obtain ⟨u, hu, humem, huf', huc, _, _, hut, hul', (huv' : u.regs valueBase = vb), _, _,
      huch', hureg⟩ := hregs.exec_loadFrame hd hdL.le hw
  have huc' : u.regs count = N := huc.trans hN
  have hut' : u.regs term = k := hut.trans hterm
  obtain ⟨hum, hu0, hu1, hunine, huten⟩ :
      u.regs mode = 2 ∧ u.regs nil = 0 ∧ u.regs one = 1 ∧
      u.regs nine = 9 ∧ u.regs ten = 10 := by regs_frame
  obtain ⟨v, hv, _, hvmem, hvFrame, _, hvreg⟩ := exec_accumulateLoop u input V B huc'
    (by simpa only [hul', humem] using hinput) hcodes hinj
    (by simpa only [huv', humem] using hparent)
    (by simpa only [huch', humem, hut'] using hchild) hV hB
    (Or.inl (by rw [hul', huv']; dsimp [vb]; nlinarith only [hcap, hpow]))
    (Or.inl (by rw [huv', huch']; dsimp [vb]; nlinarith only []))
    hu1 hunine huten
    (hw.of_le (by rw [hul', huv', huch']; dsimp [vb]; nlinarith only [hcap, hpow, hmul, hL]))
  obtain ⟨hvf, hvt⟩ : v.regs frame = f + 4 * d ∧ v.regs term = k := by regs_frame
  obtain ⟨y, hy, _, hym, hymem, _⟩ := exec_advance v (by regs_frame) (by regs_frame)
    (hw.of_le (by rw [hvt]; omega)) (hw.of_le (by rw [hvf]; nlinarith only [hL, hdL]))
  have hbranch : ExecWithin (w + 2)
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y (31 * N + 12) :=
    (((hv.seq hy).mono (by omega)).branch_neg
      (by simp only [Cond.holds_eq, hum, hu1]; decide)).branch_neg
      (by simp only [Cond.holds_eq, hum, hu0]; decide)
  have he : ExecWithin (w + 2) step x y (31 * N + 29) := (hu.seq hbranch).mono (by omega)
  obtain ⟨hyl, hya, hye⟩ :
      y.regs level = d ∧ y.regs active = x.regs active ∧ y.regs epoch = x.regs epoch := by
    regs_frame
  let written := ((range N).filter fun i => selected true k (input i)).image
    fun i => vb + input i
  have hvmem' : v.mem = written.piecewise
      (fun a => encode (V (a - vb) + B ((a - vb) / 10))) x.mem := by
    rwa [huv', hut', humem] at hvmem
  have hyframe : Modifies (Block.mk (f + 4 * d) 4).footprint v.mem y.mem := by
    rw [hymem, hvf]; exact Modifies.write_of_owns (by constructor <;> omega) _
  have hvframe : Modifies (Block.mk vb (10 ^ L)).footprint x.mem v.mem := by
    simpa only [huv', humem] using hvFrame
  have frameBeforeValue : f + 4 * d + 4 ≤ vb := by dsimp [vb]; omega
  refine ⟨y, he, hregs.of_step he, hyl, hym, hya, hye, ?_, ?_,
    by simp only [hymem, hvf, hvt, Function.update_self], ?_, ?_⟩
  · intro i hi
    change y.mem (vb + input i) = _
    rw [hyframe _ (by simp only [Block.mem_footprint, Block.Owns]; omega), hvmem']
    by_cases hsel : selected true k (input i)
    · have hmem : vb + input i ∈ written := mem_image.mpr
        ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hsel⟩, rfl⟩
      simp only [piecewise, hmem, hsel, ↓reduceIte, Nat.add_sub_cancel_left]
    · have hmem : vb + input i ∉ written := fun h =>
        let ⟨_, hj, hji⟩ := mem_image.mp h; hsel (Nat.add_left_cancel hji ▸ (mem_filter.mp hj).2)
      simpa only [piecewise, hmem, hsel, ↓reduceIte, add_zero] using hparent i hi
  · intro j hj
    rw [hymem, hvf, Function.update_of_ne (by omega : f + 4 * d + j ≠ f + 4 * d + 3)]
    exact hvframe _ (by simp only [Block.mem_footprint, Block.Owns]; omega)
  · intro q _
    have hafter : vb + 10 ^ L ≤ f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q := by
      dsimp only [vb]; nlinarith only [hmul]
    exact (hyframe _ (by simp only [Block.mem_footprint, Block.Owns]; omega)).trans
      (hvframe _ (by simp only [Block.mem_footprint, Block.Owns]; omega))
  · intro c hc
    refine (hvframe.trans hyframe) c fun hc' => hc ?_
    have hlen := Nat.mul_le_mul_right (10 ^ L) (by omega : 1 ≤ L + 1 - d)
    simp only [nodeWrites, mem_union, Block.mem_footprint, Block.Owns] at hc' ⊢
    rcases hc' with hc' | hc'
    · exact Or.inl (Or.inr ⟨hc'.1, by dsimp [vb] at hc' ⊢; omega⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨hc'.1, by omega⟩))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
