/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PrefixStep
public import CslibFrontier.Computability.WordRAM.Sequence

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete native tile-prefix pass

## Main results

* `Wanted.exec_prefix`: compute every exact tile span and initialize its scatter cursor,
  including the terminal query-count offset, with native loads, stores and loop controls.

This is an internal implementation API of the complete routing program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The actual prefix loop initializes every immutable span and mutable cursor. Neither
the offsets nor the total input length are supplied as precomputed memory certificates. -/
theorem exec_prefix {w L m N Q : ℕ} (key : ℕ → ℕ)
    (hkey : ∀ i < Q, key i < numBands L m N ^ 2) (x : Data 96)
    (hx : Parameters L m N Q x)
    (hcounts : ∀ t < numBands L m N ^ 2,
      x.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prefixCode x y (10 * numBands L m N ^ 2 + 6) ∧
      Parameters L m N Q y ∧
      (∀ t ≤ numBands L m N ^ 2,
        y.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
      y.mem (offsetAddress L m N Q + numBands L m N ^ 2) = Q ∧
      (∀ a, a < offsetAddress L m N Q ∨ codeAddress L m N Q ≤ a → y.mem a = x.mem a) := by
  have hoa : offsetAddress L m N Q = countAddress L Q + numBands L m N ^ 2 := rfl
  have hca : cursorAddressBase L m N Q = offsetAddress L m N Q + numBands L m N ^ 2 + 1 := rfl
  have hda : codeAddress L m N Q = cursorAddressBase L m N Q + numBands L m N ^ 2 := rfl
  let P (j : ℕ) (z : Data 96) : Prop := Parameters L m N Q z ∧
    z.regs total = Nat.count (fun k => key k < j) Q ∧
    (∀ t < j,
      z.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      z.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q) ∧
    (∀ t < numBands L m N ^ 2,
      z.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q) ∧
    (∀ a, a < offsetAddress L m N Q ∨ codeAddress L m N Q ≤ a → z.mem a = x.mem a)
  have hb (z : Data 96) (hz : P (z.regs index) z) (hn : z.regs index < numBands L m N ^ 2) :
      ∃ u, ExecWithin w prefixStep z u 8 ∧
        P (z.regs index + 1) u ∧ u.regs index = z.regs index + 1 := by
    obtain ⟨u, he, hu, hidx, hsum, hoff, hcur, hf⟩ := exec_prefixStep key hn z hz.1 rfl
      hz.2.1 (hz.2.2.2.1 _ hn) hfit
    refine ⟨u, he, ⟨hu, hsum, fun t ht => ?_, fun t ht => ?_, fun a ha => ?_⟩, hidx⟩
    · by_cases ht' : t = z.regs index
      · subst t
        exact ⟨hoff, hcur⟩
      · rw [hf _ (by omega) (by omega), hf _ (by omega) (by omega)]
        exact hz.2.2.1 t (by omega)
    · exact (hf _ (by omega) (by omega)).trans (hz.2.2.2.1 t ht)
    · exact (hf _ (by omega) (by omega)).trans (hz.2.2.2.2 a ha)
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have haddr : Fits w (offsetAddress L m N Q + numBands L m N ^ 2) := hl.of_le (by
    unfold offsetAddress countAddress tableAddress inputLimit
    omega)
  have hlast : Nat.count (fun k => key k < numBands L m N ^ 2) Q = Q := Nat.count_of_forall hkey
  refine WP.exists_execWithin ?_
  unfold prefixCode
  wram_exec
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.tileCount) hb (Nat.zero_le _)
    ⟨by regs_frame, by wram_simp; simp, by wram_simp; simp, hcounts, fun _ _ => rfl⟩)
    with y ⟨⟨hyp, hsum, hyoff, _, hyframe⟩, _⟩
  wram_exec * [haddr]
  refine ⟨by regs_frame, fun t ht => ?_, fun t ht => ?_, by wram_simp [hlast], fun a ha => ?_⟩
  · by_cases h : t = numBands L m N ^ 2
    · subst t
      wram_simp
    · have hne : offsetAddress L m N Q + t ≠ offsetAddress L m N Q + numBands L m N ^ 2 := by omega
      wram_simp [hne, (hyoff t (by omega)).1]
  · have hne : cursorAddressBase L m N Q + t ≠ offsetAddress L m N Q + numBands L m N ^ 2 := by
      omega
    wram_simp [hne, (hyoff t ht).2]
  · have hne : a ≠ offsetAddress L m N Q + numBands L m N ^ 2 := by omega
    wram_simp [hne, hyframe a ha]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
