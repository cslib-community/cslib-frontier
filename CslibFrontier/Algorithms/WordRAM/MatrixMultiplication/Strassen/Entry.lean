/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Zero
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Prepare
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Control
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Dispatch
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Actual positive-depth Strassen entry

The first parent stage clears only its current output and materializes the first child.
Original coefficient arrays and older frames are protected by the derived native footprint.
Together with the scalar case, this is an internal stage composed by `Strassen.Traversal`.
The modular triangle counter still requires its own complete pipeline composition.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The first real parent stage clears its output and computes both first-child operands.
No clean output or preformed child input is required. -/
theorem exec_stage_zero {w p k A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (stage 0) x y (68 * (4 ^ k * p) + 54) ∧
      NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
        (scratch + 3 * (4 ^ k * p)) frames (frame + 7) y ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u 0 j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 4 ^ k * p + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v 0 j)) ∧
      (∀ j < 4 ^ (k + 1) * p, y.mem (out + j) = 0) ∧
      y.mem (frame + 6) = 1 ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) →
        (d < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ d) →
        (d < frame + 6 ∨ frame + 14 ≤ d) → y.mem d = x.mem d := by
  let q := 4 ^ k * p
  have hsize : 4 ^ (k + 1) * p = 4 * q := by rw [pow_succ]; ring
  have ho := hl.output_before; have hs := hl.scratch_before
  have hf := hl.frames_before
  obtain ⟨s, he, hm, hr⟩ := exec_clear x hx.zero_eq hx.one_eq
    (by rw [hx.output_eq, hx.size_eq]
        exact haddr.of_le (by unfold addressBound; omega))
  have sc : ChildBuffers p k scratch s := hc.of_regs_eq fun i hi hi' =>
    hr i (by rintro rfl; contradiction)
      (by rintro rfl; contradiction)
  have houtside (d : ℕ) (hd : d < out ∨ out + 4 ^ (k + 1) * p ≤ d) : s.mem d = x.mem d := by
    rw [hm, hx.output_eq, hx.size_eq]
    exact WordRAM.clear_of_not_owns (by simp only [Block.Owns]; omega)
  obtain ⟨hleft', hright'⟩ := hl.inputs_of_outside houtside
  obtain ⟨y, hy, ready, leftValues, rightValues, parentPhase, memory⟩ := exec_prepareChild 0
    s u v (hx.of_regs_eq_cursors hr) sc hl hu hv
    (fun i hi => (hleft' i hi).trans (hleft i hi))
    (fun i hi => (hright' i hi).trans (hright i hi)) hmag haddr
  refine ⟨y, (he.seq hy).mono (by rw [hx.size_eq, hsize]; omega), ready,
    leftValues, rightValues, fun j hj => ?_, parentPhase,
    fun d hd hds hdf => (memory d hds hdf).trans (houtside d hd)⟩
  rw [memory _ (Or.inl (by omega)) (Or.inl (by omega)), hm, hx.output_eq, hx.size_eq]
  exact WordRAM.clear_of_owns (by simp only [Block.Owns]; omega)

/-- The actual first positive-depth controller iteration includes frame loading, depth
comparison, computed child pointers, phase dispatch, clearing and both operand loops. -/
theorem exec_step_entry {w p k A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeReady p (k + 1) a b out scratch frames frame x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ (k + 1) * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ (k + 1) * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) step x y (68 * (4 ^ k * p) + 77) ∧
      NodeReady p k scratch (scratch + 4 ^ k * p) (scratch + 2 * (4 ^ k * p))
        (scratch + 3 * (4 ^ k * p)) frames (frame + 7) y ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u 0 j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 4 ^ k * p + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v 0 j)) ∧
      (∀ j < 4 ^ (k + 1) * p, y.mem (out + j) = 0) ∧
      y.mem (frame + 6) = 1 ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) →
        (d < scratch ∨ scratch + 2 * (4 ^ k * p) ≤ d) →
        (d < frame + 6 ∨ frame + 14 ≤ d) → y.mem d = x.mem d := by
  refine WP.exists_execWithin ?_
  unfold step
  refine WP.seq (WP.of_spec (exec_loadCurrent x hx.one_eq
    (by rw [hx.frame_eq]
        exact haddr.of_le (by unfold addressBound; omega))
    (by simpa only [hx.frame_eq] using hx.frame_words)) ?_)
  rintro s ⟨sm, sr⟩
  have sh := hx.toNodeHeader.of_regs_eq_cursors (fun i hi _ => sr i hi)
  wram_exec [sh.depth_eq, sh.zero_eq]
  wram_call (exec_locateChild_header s sh hl haddr) with r ⟨rh, rc, rm, rr⟩
  obtain ⟨y, hy, ready, valuesA, valuesB, zeros, parentPhase, memory⟩ :=
    exec_stage_zero r u v rh rc hl hu hv
      (by simpa only [rm, sm] using hleft) (by simpa only [rm, sm] using hright) hmag haddr
  refine WP.of_execWithin (exec_dispatch 0 r y rh.zero_eq (by regs_frame)
    (haddr.of_le (by unfold addressBound; omega)) (by simpa [dispatchState] using hy))
    ⟨by norm_num [dispatchBudget], ready, valuesA, valuesB, zeros, parentPhase,
      fun d hd' hds hdf => by simpa only [rm, sm] using memory d hd' hds hdf⟩

end Cslib.Algorithms.WordRAM.Strassen
