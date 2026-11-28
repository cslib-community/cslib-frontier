/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Spec
import CslibFrontier.Computability.WordRAM.RegisterFrame

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Real coordinate delivery, verifier calls and witness returns

The internal call rule invokes the complete native signed-weight verifier, preserves the
controller and old product bank, and returns its original zero-sum vertex. Query delivery
loads the actual interleaved words and increments the actual scan counter. No run or witness
routine is supplied by a caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

private theorem scanBank_injective : Function.Injective scanBank := fun _ _ h =>
  Fin.ext (by simpa only [scanBank, Nat.add_left_cancel_iff] using congrArg Fin.val h)

/-- Execute the real original-weight verifier on the disjoint bank. Every scanned weight
comes from the original arrays; a nonzero product answer supplies no original-weight witness. -/
theorem exec_scan {w U n first length out queries count a b : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hargA : x.regs (scanBank WitnessScan.Reg.a) = a)
    (hargB : x.regs (scanBank WitnessScan.Reg.b) = b)
    (ha : a < n) (hb : b < n) (hc : first + length ≤ n)
    (hmem : ∀ i < n, ∀ j < n,
      x.mem (5 + (i * n + j)) = Signed.encode (AB i j) ∧
      x.mem (5 + n * n + (i * n + j)) = Signed.encode (BC i j) ∧
      x.mem (5 + n * n + n * n + (i * n + j)) = Signed.encode (AC i j))
    (hmag : ∀ i < n, ∀ j < n,
      (AB i j).natAbs ≤ U ∧ (BC i j).natAbs ≤ U ∧ (AC i j).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) (6 * (n * n) + n + first + length + 24)) :
    ∃ y, ExecWithin (w + 2) scan x y (42 * length + 17) ∧
      Fixed n first length out queries count y ∧ y.mem = x.mem ∧
      y.regs (scanBank WitnessScan.Reg.a) = a ∧
      y.regs (scanBank WitnessScan.Reg.b) = b ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 0 ∨
        y.regs (scanBank WitnessScan.Reg.found) = 1) ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 1 ↔
        ∃ c, first ≤ c ∧ c < first + length ∧ AB a b + BC b c + AC a c = 0) ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 1 →
        first ≤ y.regs (scanBank WitnessScan.Reg.witness) ∧
        y.regs (scanBank WitnessScan.Reg.witness) < first + length ∧
        AB a b + BC b (y.regs (scanBank WitnessScan.Reg.witness)) +
          AC a (y.regs (scanBank WitnessScan.Reg.witness)) = 0) ∧
      ∀ i : Fin 400, i.val < 336 ∨ 368 ≤ i.val → y.regs i = x.regs i := by
  let A : WitnessScan.Args := ⟨5, 5 + n * n, 5 + n * n + n * n, n, a, b, first, length⟩
  obtain ⟨y, he, ⟨⟨sab, sbc, sac, sn, sa', sb', sfirst, slength⟩, sm, sf, si, sw⟩, _⟩ :=
    ExecWithin.rename_post scanBank_injective (WitnessScan.exec A AB BC AC (x.comap scanBank)
      ⟨hx.ab, hx.bc, hx.ac, hx.scanSize, hargA, hargB, hx.scanFirst, hx.scanLength⟩ ha hb hc
      hmem hmag hU (hfit.of_le (by dsimp only [A, WitnessScan.Args.addressBound]; omega)))
  exact ⟨y, he, by regs_frame, sm, sa', sb', sf, si, sw,
    fun i hi => he.regs_eq (Code.preserves_rename_of_offset _ _ (fun _ => rfl) i hi)⟩

/-- Load the actual query occurrence into the verifier arguments and increment the native
scan count. No query enumeration or pair supplied as an algorithm argument replaces the loads. -/
theorem exec_deliverPair {W n first length out queries count i scans a b : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hi : x.regs Reg.index = i) (hs : x.regs Reg.scans = scans)
    (ha : x.mem (queries + 2 * i) = a) (hb : x.mem (queries + 2 * i + 1) = b)
    (hfit : Fits W (queries + 2 * i + scans + 8)) :
    ∃ y, ExecWithin W deliverPair x y 6 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs (scanBank WitnessScan.Reg.a) = a ∧
      y.regs (scanBank WitnessScan.Reg.b) = b ∧ y.regs Reg.scans = scans + 1 ∧
      y.regs Reg.index = i ∧ y.regs Reg.found = x.regs Reg.found ∧
      ∀ j : Fin 400, j.val < 326 ∨ j = Reg.one ∨ j = Reg.zero ∨
        (345 ≤ j.val ∧ j.val ≤ 348) ∨ (351 ≤ j.val ∧ j.val ≤ 352) →
        y.regs j = x.regs j := by
  have hreadA : x.mem (i + i + queries) = a := by simpa only [two_mul, Nat.add_comm] using ha
  have hreadB : x.mem (i + i + queries + 1) = b := by
    simpa only [two_mul, Nat.add_comm] using hb
  wram_exec [deliverPair, hi, hs, hx.queries, hx.one, hreadA, hreadB]
  exact ⟨by regs_frame, rfl, by wram_simp, by wram_simp, by wram_simp,
    by regs_frame, by regs_frame, fun j hj => by
      dsimp only [Reg.one, Reg.zero] at hj
      rw [show scanBank WitnessScan.Reg.a = 349 from rfl,
        show scanBank WitnessScan.Reg.b = 350 from rfl]
      update_simp [Reg.address, Reg.scans]⟩

/-- Copy back only a genuinely reported verifier success and its actual original coordinates.
This is a charged native branch, preserving all fixed arguments, memory and the scan count. -/
theorem exec_receiveWitness {W n first length out queries count flag a b c : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hf : x.regs (scanBank WitnessScan.Reg.found) = flag)
    (ha : x.regs (scanBank WitnessScan.Reg.a) = a)
    (hb : x.regs (scanBank WitnessScan.Reg.b) = b)
    (hc : x.regs (scanBank WitnessScan.Reg.witness) = c) :
    ∃ y, ExecWithin W receiveWitness x y 5 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs Reg.found = (if flag = 1 then 1 else x.regs Reg.found) ∧
      y.regs Reg.witnessA = (if flag = 1 then a else x.regs Reg.witnessA) ∧
      y.regs Reg.witnessB = (if flag = 1 then b else x.regs Reg.witnessB) ∧
      y.regs Reg.witnessC = (if flag = 1 then c else x.regs Reg.witnessC) ∧
      y.regs Reg.scans = x.regs Reg.scans ∧ y.regs Reg.index = x.regs Reg.index ∧
      ∀ j : Fin 400, j.val < 326 ∨ j = Reg.one ∨ j = Reg.zero ∨
        (345 ≤ j.val ∧ j.val ≤ 348) ∨ (351 ≤ j.val ∧ j.val ≤ 352) →
        y.regs j = x.regs j := by
  unfold receiveWitness
  by_cases h : flag = 1 <;>
    wram_exec [h, hf, ha, hb, hc, hx.one] <;>
    exact ⟨by regs_frame, rfl, by wram_simp [h], by wram_simp [h], by wram_simp [h],
      by wram_simp [h], by regs_frame, by regs_frame, fun j hj => by
        dsimp only [Reg.one, Reg.zero] at hj
        update_simp [Reg.found, Reg.witnessA, Reg.witnessB, Reg.witnessC]⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
