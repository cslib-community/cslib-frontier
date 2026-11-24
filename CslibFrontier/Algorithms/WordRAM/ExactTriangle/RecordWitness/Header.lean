/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Spec
import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Actual record and interval-header execution

These internal rules read the producer's real scalar/record words and run the existing native
square-root loop. Record and piece metadata are never supplied as predecoded algorithm inputs.
The original producer/product bank and all memory are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM
open Cslib.Algorithms.ExactTriangle

private theorem sqrtBank_injective : Function.Injective sqrtBank := by
  intro i j h
  apply Fin.ext
  simpa only [sqrtBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

private theorem squareRoot_preserves (i : Fin 400) (hi : i.val < 336 ∨ 342 ≤ i.val) :
    squareRoot.Preserves i := by
  exact Code.preserves_rename_of_offset _ _ (fun _ => rfl) i hi

/-- Read the original dimension/divisor and this actual six-word record, then reset the
per-record search state. The record address is computed from the native selected ordinal. -/
theorem exec_readRecord {W n D g i records heap out : ℕ} (x : Data 400) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hg : x.mem 2 = g) (hn : x.mem 3 = n)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hrecords : x.regs (productBank (RecordProduct.producerBank Instances.output)) = records)
    (hout : x.regs (productBank RecordProduct.Reg.result) = out)
    (hrec : records + i * (6 + 2 * (n * D)) + 6 ≤ heap)
    (hv : ∀ j : Fin 6, x.mem (records + i * (6 + 2 * (n * D)) + j.val) = v j)
    (hfit : Fits W (heap + 2 * (n * D) + D + n + g + 128)) :
    ∃ y, ExecWithin W readRecord x y 28 ∧ y.mem = x.mem ∧
      y.regs (sqrtBank NatSqrt.arg) = D ∧ y.regs Reg.size = n ∧
      y.regs Reg.divisor = g ∧ y.regs Reg.output = out ∧
      y.regs Reg.piece = v 1 ∧ y.regs Reg.queries = v 2 ∧ y.regs Reg.count = v 3 ∧
      y.regs Reg.found = 0 ∧ y.regs Reg.witnessA = 0 ∧ y.regs Reg.witnessB = 0 ∧
      y.regs Reg.witnessC = 0 ∧ y.regs Reg.scans = 0 ∧ y.regs Reg.index = 0 ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧
      ∀ j : Fin 400, j.val < 320 → y.regs j = x.regs j := by
  let stride := n * D + n * D + 6
  let r := records + i * stride
  have heq : stride = 6 + 2 * (n * D) := by dsimp only [stride]; omega
  have hrange : r + 6 ≤ heap := by simpa only [r, heq] using hrec
  have hmul : Fits W (i * stride) := hfit.of_le (by dsimp only [r] at hrange; omega)
  have hv1 : x.mem (r + 1) = v 1 := by simpa +decide [r, heq] using hv ⟨1, by decide⟩
  have hv2 : x.mem (r + 1 + 1) = v 2 := by
    change x.mem (r + 2) = v 2
    simpa +decide [r, heq] using hv ⟨2, by decide⟩
  have hv3 : x.mem (r + 1 + 1 + 1) = v 3 := by
    change x.mem (r + 3) = v 3
    simpa +decide [r, heq] using hv ⟨3, by decide⟩
  dsimp only [r, stride] at hmul hv1 hv2 hv3
  unfold readRecord
  wram_exec [hD, hg, hn, hi, hrecords, hout, hv1, hv2, hv3]
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, fun _ hj => by
      rw [show sqrtBank NatSqrt.arg = 336 from rfl]
      update_simp [Reg.one, Reg.zero, Reg.address, Reg.size, Reg.temp, Reg.divisor, Reg.output,
        Reg.piece, Reg.queries, Reg.count, Reg.found, Reg.witnessA, Reg.witnessB, Reg.witnessC,
        Reg.scans, Reg.index]⟩

/-- The local interval decoder executes the actual square-root loop, preserving the complete
old bank and controller registers. Its result is derived, not a square-root certificate. -/
theorem exec_squareRoot {W D : ℕ} (x : Data 400)
    (hD : x.regs (sqrtBank NatSqrt.arg) = D) (hfit : Fits W (4 * D + 4)) :
    ∃ y, ExecWithin W squareRoot x y (5 * Nat.sqrt D + 7) ∧
      y.regs (sqrtBank NatSqrt.root) = Nat.sqrt D ∧ y.mem = x.mem ∧
      ∀ i : Fin 400, i.val < 336 ∨ 342 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, hy, hr, -, hm, -⟩ := NatSqrt.exec_rename sqrtBank sqrtBank_injective x (by
    rw [hD]; exact hfit)
  refine ⟨y, ?_, ?_, hm, fun i hi => hy.regs_eq (squareRoot_preserves i hi)⟩
  · simpa only [squareRoot, hD] using hy
  · simpa only [hD] using hr

/-- Compute the actual interval and original signed-array pointers after the real root loop.
All query/output metadata and success/counter initialization are preserved. -/
theorem exec_finishHeader {W n S g k : ℕ} (x : Data 400)
    (hroot : x.regs (sqrtBank NatSqrt.root) = S) (hn : x.regs Reg.size = n)
    (hg : x.regs Reg.divisor = g) (hk : x.regs Reg.piece = k)
    (h1 : x.regs Reg.one = 1) (hc : k * (S ⌈/⌉ g) ≤ n)
    (hfit : Fits W (S + g + 3 * (n * n) + n + 64)) :
    let B := S ⌈/⌉ g
    let first := k * B
    let length := min B (n - first)
    ∃ y, ExecWithin W finishHeader x y 15 ∧ y.mem = x.mem ∧
      y.regs Reg.blockLength = B ∧ y.regs Reg.first = first ∧ y.regs Reg.length = length ∧
      y.regs (scanBank WitnessScan.Reg.ab) = 5 ∧
      y.regs (scanBank WitnessScan.Reg.bc) = 5 + n * n ∧
      y.regs (scanBank WitnessScan.Reg.ac) = 5 + n * n + n * n ∧
      y.regs (scanBank WitnessScan.Reg.size) = n ∧
      y.regs (scanBank WitnessScan.Reg.first) = first ∧
      y.regs (scanBank WitnessScan.Reg.length) = length ∧
      ∀ i : Fin 400, i.val < 324 ∨ i = Reg.index ∨ i = Reg.one ∨ i = Reg.piece ∨
        i = Reg.divisor ∨ 392 ≤ i.val → y.regs i = x.regs i := by
  intro B first length
  have hquot : (S + g - 1) / g = B := by simp only [B, Nat.ceilDiv_eq_add_pred_div]
  have hsub : Fits W (S + g - 1) := hfit.of_le (by omega)
  have hB : Fits W B := by rw [← hquot]; exact hsub.of_le (Nat.div_le_self ..)
  have hfirst : Fits W first := hfit.of_le (by change k * B ≤ n at hc; dsimp only [first]; omega)
  unfold finishHeader
  by_cases hlt : B < n - first
  · have hl : B = length := (min_eq_left hlt.le).symm
    wram_exec [hroot, hn, hg, hk, h1, hquot, hlt]
    exact ⟨rfl, by wram_simp [B], by wram_simp [first], by wram_simp [hl], by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp [first], by wram_simp [hl],
      fun i hi => by
        dsimp only [Reg.index, Reg.one, Reg.piece, Reg.divisor] at hi
        rw [show scanBank WitnessScan.Reg.ab = 345 from rfl,
          show scanBank WitnessScan.Reg.bc = 346 from rfl,
          show scanBank WitnessScan.Reg.ac = 347 from rfl,
          show scanBank WitnessScan.Reg.size = 348 from rfl,
          show scanBank WitnessScan.Reg.first = 351 from rfl,
          show scanBank WitnessScan.Reg.length = 352 from rfl]
        update_simp [Reg.blockLength, Reg.first, Reg.length, Reg.temp]⟩
  · have hl : n - first = length := (min_eq_right (by omega)).symm
    wram_exec [hroot, hn, hg, hk, h1, hquot, hlt]
    exact ⟨rfl, by wram_simp [B], by wram_simp [first], by wram_simp [first, hl], by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp [first], by wram_simp [first, hl],
      fun i hi => by
        dsimp only [Reg.index, Reg.one, Reg.piece, Reg.divisor] at hi
        rw [show scanBank WitnessScan.Reg.ab = 345 from rfl,
          show scanBank WitnessScan.Reg.bc = 346 from rfl,
          show scanBank WitnessScan.Reg.ac = 347 from rfl,
          show scanBank WitnessScan.Reg.size = 348 from rfl,
          show scanBank WitnessScan.Reg.first = 351 from rfl,
          show scanBank WitnessScan.Reg.length = 352 from rfl]
        update_simp [Reg.blockLength, Reg.first, Reg.length, Reg.temp]⟩

/-- Complete charged local setup from real scalar and descriptor reads. The computed original
piece interval and all verifier arguments are conclusions of the actual code. -/
theorem exec_header {W n D g i records heap out : ℕ} (x : Data 400) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hg : x.mem 2 = g) (hn : x.mem 3 = n)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hrecords : x.regs (productBank (RecordProduct.producerBank Instances.output)) = records)
    (hout : x.regs (productBank RecordProduct.Reg.result) = out)
    (hrec : records + i * (6 + 2 * (n * D)) + 6 ≤ heap)
    (hv : ∀ j : Fin 6, x.mem (records + i * (6 + 2 * (n * D)) + j.val) = v j)
    (hfirst : v 1 * pieceSize D g ≤ n)
    (hfit : Fits W (heap + 4 * D + 2 * (n * D) + 3 * (n * n) + n + g + 512)) :
    let first := v 1 * pieceSize D g
    let length := min (pieceSize D g) (n - first)
    ∃ y, ExecWithin W header x y (5 * Nat.sqrt D + 50) ∧
      Fixed n first length out (v 2) (v 3) y ∧ y.mem = x.mem ∧
      y.regs Reg.found = 0 ∧ y.regs Reg.witnessA = 0 ∧ y.regs Reg.witnessB = 0 ∧
      y.regs Reg.witnessC = 0 ∧ y.regs Reg.scans = 0 ∧ y.regs Reg.index = 0 ∧
      ∀ j : Fin 400, j.val < 320 → y.regs j = x.regs j := by
  have hsqrt := Nat.sqrt_le_self D
  unfold header
  wram_exec
  wram_call (exec_readRecord x v hD hg hn hi hrecords hout hrec hv (hfit.of_le (by omega)))
    with a ⟨am, aD, an, ag, ao, ak, aq, aQ, af, aa, ab, ac, as, ai, a1, a0, ar⟩
  wram_exec
  wram_call (exec_squareRoot a aD (hfit.of_le (by omega))) with b ⟨bS, bm, br⟩
  wram_call (exec_finishHeader b bS (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) hfirst (hfit.of_le (by omega)))
    with y ⟨ym, yB, yf, yl, yab, ybc, yac, yn, yfirst, ylength, yr⟩
  exact ⟨by omega, by regs_frame, ym.trans (bm.trans am),
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    fun j hj => (yr j (Or.inl (by omega))).trans ((br j (Or.inl (by omega))).trans (ar j hj))⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
