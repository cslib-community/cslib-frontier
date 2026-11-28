/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual matrix-word adaptation between producer inputs

## Main results

* `QueriedProduct.exec_prepareBits`: copy each original raw unsigned entry while actually
  doubling it for the canonical signed producer convention.

The conversion uses a native load/multiply/store loop. Its original-entry bound derives
every arithmetic fit; its invariant protects unread source words and all caller scalars.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Source and destination blocks in the actual matrix adaptation are disjoint and fit. -/
public theorem matrix_transfer_bounds (L m N Q : ℕ) :
    4 + 2 * (N * D m) ≤ snapshotBase L m N Q + 5 ∧
      snapshotBase L m N Q + 5 + 2 * (N * D m) ≤ memoryEnd L m N Q := by
  have h := transfer_bounds L m N Q
  unfold inputEnd at h
  omega

/-- Every raw entry is converted by an actual charged multiplication, with the complete
outside frame. The numerical bound concerns original source words, not intermediate states. -/
public theorem exec_prepareBits {w L m N Q A : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q))
    (hA : Fits w (2 * A))
    (hentries : ∀ i < 2 * (N * D m), x.mem (snapshotBase L m N Q + 5 + i) ≤ A) :
    ∃ y, ExecWithin w (prepareMatrices true) x y (8 * (2 * (N * D m)) + 4) ∧
      Parameters L m N Q y ∧
      (∀ i < 2 * (N * D m),
        y.mem (4 + i) = 2 * x.mem (snapshotBase L m N Q + 5 + i)) ∧
      (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
  let M := 2 * (N * D m)
  let S := snapshotBase L m N Q + 5
  have hb := matrix_transfer_bounds L m N Q
  have hsource : Fits w S := allocated_fits hfit (by dsimp [S]; omega)
  let P (k : ℕ) (z : Data 160) : Prop := Parameters L m N Q z ∧ z.regs Reg.source = S ∧
    (∀ j < k, z.mem (4 + j) = 2 * x.mem (S + j)) ∧
    (∀ a, a < 4 ∨ 4 + k ≤ a → z.mem a = x.mem a)
  have hbody (z : Data 160) (hz : P (z.regs Reg.index) z) (hi : z.regs Reg.index < M) :
      ∃ u, ExecWithin w bitCopyStep z u 6 ∧ P (z.regs Reg.index + 1) u ∧
        u.regs Reg.index = z.regs Reg.index + 1 := by
    obtain ⟨hzp, hzs, hzj, hza⟩ := hz
    have hload : z.mem (S + z.regs Reg.index) = x.mem (S + z.regs Reg.index) :=
      hza _ (Or.inr (by dsimp [S, M] at *; omega))
    have hsrc : Fits w (S + z.regs Reg.index) := allocated_fits hfit (by dsimp [S, M] at *; omega)
    have hdst : Fits w (4 + z.regs Reg.index) := allocated_fits hfit (by dsimp [S, M] at *; omega)
    have hnext : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by dsimp [S, M] at *; omega)
    have hvalue : Fits w (x.mem (S + z.regs Reg.index) * 2) := hA.of_le (by
      have hv := hentries (z.regs Reg.index) hi
      dsimp only [S]
      omega)
    refine WP.exists_execWithin ?_
    wram_exec * [bitCopyStep, hload, hsrc, hdst, hnext, hvalue]
    refine ⟨⟨by regs_frame, by wram_simp [hzs], ?_, ?_⟩, by wram_simp⟩
    · intro j hj
      by_cases h : j = z.regs Reg.index
      · subst h
        wram_simp
        exact Nat.mul_comm _ _
      · wram_simp
        exact hzj j (by omega)
    · intro a ha
      have hne : a ≠ 4 + z.regs Reg.index := by rcases ha with ha | ha <;> omega
      wram_simp [hne]
      exact hza a (by rcases ha with ha | ha <;> omega)
  refine WP.exists_execWithin ?_
  dsimp only [S] at hsource
  unfold prepareMatrices
  simp only [↓reduceIte]
  wram_exec * [hsource]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.matrixWords) hbody
    (by wram_simp; exact Nat.zero_le _)
    ⟨by regs_frame, by wram_simp; rfl, by wram_simp; simp, fun _ _ => rfl⟩)
    with y ⟨⟨hyp, _, hyj, hya⟩, _⟩
  exact ⟨by wram_simp; omega, hyp, hyj, hya⟩

/-- Canonical signed inputs use actual dynamic copying with no conversion arithmetic. -/
public theorem exec_prepareSigned {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w (prepareMatrices false) x y (7 * (2 * (N * D m)) + 10) ∧
      Parameters L m N Q y ∧
      (∀ i < 2 * (N * D m),
        y.mem (4 + i) = x.mem (snapshotBase L m N Q + 5 + i)) ∧
      (∀ a, a < 4 ∨ 4 + 2 * (N * D m) ≤ a → y.mem a = x.mem a) := by
  have hb := matrix_transfer_bounds L m N Q
  have hs : Fits w (snapshotBase L m N Q + 5) := allocated_fits hfit (by omega)
  have hz : ExecWithin (B := .standard) w (ram[
      Reg.source ← Reg.snapshot + Reg.five;
      Reg.destination ← Reg.four;
      Reg.length ← Reg.matrixWords ]) x
      (((x.set Reg.source (snapshotBase L m N Q + 5)).set Reg.destination 4).set
        Reg.length (2 * (N * D m))) 3 := by
    wram_exec * [hs]
  obtain ⟨y, he, hy, hm, -⟩ :=
    exec_setupCopy x hp hfit hz (by omega) (by omega) (Or.inr (Or.inl (by omega)))
  refine ⟨y, he, hy, fun i hi => ?_, fun a ha => ?_⟩
  · rw [hm]
    exact ArrayCopy.copyPrefix_read hi
  · rw [hm]
    exact ArrayCopy.copyPrefix_outside (by rcases ha with ha | ha <;> omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
