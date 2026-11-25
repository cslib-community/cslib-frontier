/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.Instances
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame

/-!
# Prepared catalogue readback after workspace reuse

Every catalogue, query, record and matrix word described by `Instances.Output` lies below its
heap boundary. A consumer may change the workspace above that boundary while preserving all
those words and the producer registers. The readback contract can then be framed against the
current state. This does not assert that the producer ran again, or that its original external
frame survived: the original producer execution and its initial state remain separate facts.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Instances

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Transport the actual prepared readback through changes above the heap. The new frame is
relative to the current state, not to the original producer input. No execution is asserted. -/
theorem Output.reframe {n D g p : ℕ} (values : ℕ → ℤ) {initial y z : Data 64}
    (h : Output n D g p values initial y) (hregs : z.regs = y.regs)
    (hmem : Set.EqOn z.mem y.mem (Set.Iio (y.regs heap))) :
    Output n D g p values z z := by
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let stop := out + (K * H) * (6 + 2 * (n * D))
  have hh : y.regs heap = stop := h.2.2.2.2.2.1
  have mem_eq (a : ℕ) (ha : a < stop) : z.mem a = y.mem a :=
    hmem (by simpa only [Set.mem_Iio, hh] using ha)
  have desc_lt {i : ℕ} (hi : i < K) : desc + 3 * i + 2 < stop := by
    have : 3 * (i + 1) ≤ 3 * K := Nat.mul_le_mul_left 3 hi
    omega
  have query_lt {rho q : ℕ} (hrho : rho < p) (hq : q < N) :
      5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q + 1 < stop := by
    have := Nat.count_le (fun k => R k = rho) (n := q)
    have hm := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hm; dsimp only [stop, out, desc]; omega
  dsimp only [stop, out, desc, K, H, C, R, N] at mem_eq desc_lt query_lt
  struct_frame h
  · rw [mem_eq _ (by have := query_lt ‹_› ‹_›; omega)]; exact ‹_›
  · rw [mem_eq _ (query_lt ‹_› ‹_›)]; exact ‹_›
  · rw [mem_eq _ (by have := desc_lt (ChunkCatalogue.before_add_lt _ _ ‹_› ‹_›); omega)]; exact ‹_›
  · rw [mem_eq _ (by have := desc_lt (ChunkCatalogue.before_add_lt _ _ ‹_› ‹_›); omega)]; exact ‹_›
  · rw [mem_eq _ (desc_lt (ChunkCatalogue.before_add_lt _ _ ‹_› ‹_›))]; exact ‹_›
  all_goals
    have hH : 0 < numPieces n D g := Nat.pos_of_ne_zero fun hz => by
      have hi : _ < _ * numPieces n D g := ‹_›; simp [hz] at hi
    have hlt : _ < _ * numPieces n D g := ‹_›
    have hd := desc_lt ((Nat.div_lt_iff_lt_mul hH).mpr hlt)
    have hm := Nat.mul_le_mul_right (6 + 2 * (n * D)) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at hm
    dsimp only [Block.Realizes]
    intro j
    have hj := j.isLt
    change z.mem _ = _
    dsimp only
    rw [mem_eq _ (by omega)]
    rw [mem_eq (5 + 6 * (n * n) + p + 2 * (n * n) * p +
      3 * (_ / numPieces n D g)) (by omega)]
    try rw [mem_eq (5 + 6 * (n * n) + p + 2 * (n * n) * p +
      3 * (_ / numPieces n D g) + 1) (by omega)]
    try rw [mem_eq (5 + 6 * (n * n) + p + 2 * (n * n) * p +
      3 * (_ / numPieces n D g) + 2) hd]
    exact ‹Block.Realizes _ _ _› j

/-- Transport prepared readback to a protected-prefix-equivalent state with its own explicit
external frame. The prefix premise covers only genuine prepared words; the external frame
is relative to the chosen initial state, and no new execution is asserted. -/
theorem Output.transfer {n D g p : ℕ} (values : ℕ → ℤ) {initial y initial' z : Data 64}
    (h : Output n D g p values initial y) (hregs : z.regs = y.regs)
    (hmem : Set.EqOn z.mem y.mem (Set.Iio (y.regs heap)))
    (hframe : ∀ q, q < 5 + 3 * (n * n) ∨ z.regs heap ≤ q → z.mem q = initial'.mem q) :
    Output n D g p values initial' z := by
  obtain ⟨hn, hD, hp, ho, hc, hh, hr, hcounts, hqueries, hdesc, hblocks, -⟩ :=
    h.reframe values hregs hmem
  exact ⟨hn, hD, hp, ho, hc, hh, hr, hcounts, hqueries, hdesc, hblocks,
    by simpa only [hh] using hframe⟩

/-- Original headers and signed matrices precede every prepared record and its workspace. -/
theorem Output.inputEnd_le_heap {n D g p : ℕ} {values : ℕ → ℤ} {initial y : Data 64}
    (h : Output n D g p values initial y) : 5 + 3 * (n * n) ≤ y.regs heap := by
  obtain ⟨-, -, -, -, -, hh, -⟩ := h
  dsimp only at hh
  omega

/-- The computed heap fits the original preparation budget, independently of old registers
or dirty memory outside the original arrays. -/
theorem Output.heap_le_budget {n D g p : ℕ} (values : ℕ → ℤ) {initial y : Data 64}
    (h : Output n D g p values initial y) (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) :
    y.regs heap ≤ budget n D g p := by
  let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  have hK : K ≤ p * (n * n) := ChunkCatalogue.before_le
    (one_le_queryCap hD hDn) (fun _ _ => Nat.count_le _) le_rfl
  have hB : 0 < pieceSize D g := by
    have hs : 0 < sOf D := Nat.sqrt_pos.mpr hD
    have hc : sOf D ≤ pieceSize D g * g := Nat.le_ceilDiv_mul (a := sOf D) (by omega)
    exact Nat.pos_of_ne_zero fun hz => by rw [hz, Nat.zero_mul] at hc; omega
  have hH : H ≤ n := (Nat.ceilDiv_le_iff hB).mpr (Nat.le_mul_of_pos_right n hB)
  have hKH := Nat.mul_le_mul hK hH
  have hprod := Nat.mul_le_mul_right (6 + 2 * (n * D)) hKH
  obtain ⟨-, -, -, -, -, hh, -⟩ := h
  change y.regs heap = 5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * K +
    (K * H) * (6 + 2 * (n * D)) at hh
  dsimp only [budget]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.Instances
