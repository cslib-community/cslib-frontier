/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.InputLayout
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Shared native construction before a query batch

The fourth original header is a query count. One extra native addition moves the shared
directory beyond the wanted-code array. The existing constructor then computes the real
table once. Eleven final instructions initialize both batch cursors and the answer pointer.
No computed table, execution, enumeration or resource certificate is supplied to the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Keep every original wanted code before the shared geometry allocation. -/
@[expose] def relocateDirectory : Code .standard registers := ram[
  BoxTable.Reg.directory ← BoxTable.Reg.directory + BoxQuery.Reg.query ]

/-- Compute actual cursors and reserve the same uncleared stack as the reusable kernel. -/
@[expose] def initializeCursors : Code .standard registers := ram[
  Reg.next ← BoxTable.Reg.arrayB + BoxTable.Reg.span;
  Reg.stop ← Reg.next + BoxQuery.Reg.query;
  BoxTable.Reg.temporary ← #1;
  Reg.output ← BoxTable.Reg.levels + BoxTable.Reg.temporary;
  Reg.output ← Reg.output * BoxTable.Reg.span;
  BoxTable.Reg.temporary ← #10;
  Reg.output ← Reg.output + BoxTable.Reg.temporary;
  BoxTable.Reg.temporary ← #5;
  Reg.output ← Reg.output * BoxTable.Reg.temporary;
  Reg.output ← Reg.output + BoxTable.Reg.values;
  Reg.output ← Reg.output + BoxTable.Reg.count ]

/-- Adapt original words, construct one real table, and initialize the actual batch. -/
@[expose] def prepare : Code .standard registers :=
  .seq BoxQuery.loadInput (.seq relocateDirectory
    (.seq (.seq BoxTable.geometry BoxTable.tile) initializeCursors))

/-- Complete ordinary-input program: shared preparation followed by all wanted queries. -/
@[expose] def program : Code .standard registers := .seq prepare queryProgram

/-- The actual batch adapter constructs the retained table and initializes all batch cursors. -/
theorem exec_prepare {w L m t N A B : ℕ} (hmL : m ≤ L) (x : Data registers)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t) (hN : x.mem 4 = N)
    (hleft : ∀ i : Fin (10 ^ L), x.mem (5 + i.val) = Signed.encode (a i))
    (hright : ∀ i : Fin (10 ^ L), x.mem (5 + 10 ^ L + i.val) = Signed.encode (b i))
    (haddr : Fits (w + 2) (originalAddressBound L m t N))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) prepare x y (preparationTime L m t) ∧
      y.regs BoxTable.Reg.levels = L ∧ y.regs BoxTable.Reg.threshold = t ∧
      y.regs BoxTable.Reg.span = 10 ^ L ∧
      y.regs BoxTable.Reg.arrayA = 5 ∧ y.regs BoxTable.Reg.arrayB = 5 + 10 ^ L ∧
      y.regs BoxTable.Reg.directory = directoryBase L N ∧
      y.regs BoxTable.Reg.values = valueBase L m t N ∧
      y.regs BoxTable.Reg.count = (boxes L m t).card ∧
      y.regs Reg.next = queryBase L ∧ y.regs Reg.stop = queryBase L + N ∧
      y.regs Reg.output = outputBase L m t N ∧
      BoxQuery.Readback m t (directoryBase L N) (valueBase L m t N) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L N ≤ p ∧ p < stackBase L m t N) → y.mem p = x.mem p) := by
  have hp : 0 < 10 ^ L := Nat.pow_pos (by decide)
  have hT0 : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  have hK := Nat.count_le (BoxTable.Eligible L (m - t)) (n := (m - t + 1) * 10 ^ L)
  rw [BoxTable.count_eligible_eq_card_boxes] at hK
  have hS := Nat.mul_le_mul_right (10 ^ L) (by omega : m - t + 1 ≤ L + 1)
  have hcurFit : Fits (w + 2)
      (100 * (L + N + valueBase L m t N + (boxes L m t).card + (L + 1) * 10 ^ L + 64)) :=
    haddr.of_le (by
      unfold originalAddressBound valueBase recordBase directoryBase queryBase
      omega)
  have hfReloc : Fits (w + 2) (BoxQuery.directoryBase L + N) :=
    haddr.of_le (by unfold BoxQuery.directoryBase originalAddressBound; omega)
  have htable : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ) :=
    hmag.of_natAbs_le (by
      simpa only [← Int.natCast_add, ← Int.natCast_mul, ← Int.natCast_pow,
        Int.natAbs_natCast] using BoxQuery.table_magnitudeBound_le L A B)
  refine WP.exists_execWithin ?_
  unfold prepare
  wram_call (BoxQuery.exec_loadInput (L := L) (m := m) (t := t) (Q := N) x hL hm ht hN
    (haddr.of_le (by unfold originalAddressBound; omega)))
    with u ⟨uL, um, ut, uN, uA, uB, uD, uμ⟩
  have hreloc : ∃ v, ExecWithin (w + 2) relocateDirectory u v 1 ∧
      v = u.set BoxTable.Reg.directory (BoxQuery.directoryBase L + N) := by
    wram_exec [relocateDirectory, *]; rfl
  wram_call hreloc with v rfl
  wram_call (BoxTable.exec_constructor (L := L) (m := m) (t := t) (D := directoryBase L N)
    (AA := 5) (BB := 5 + 10 ^ L) _
    (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))
    (fun τ => ha _) (fun τ => hb _)
    (by wram_simp [uL]) (by wram_simp [um]) (by wram_simp [ut])
    (by wram_simp; unfold directoryBase queryBase BoxQuery.directoryBase; omega)
    (by wram_simp [uA]) (by wram_simp [uB])
    (by unfold directoryBase queryBase; omega) (by unfold directoryBase queryBase; omega)
    (fun i => by simpa only [Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hleft i)
    (fun i => by simpa only [Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hright i)
    (haddr.of_le (constructor_address_le L m t N hmL)) htable)
    with z ⟨zL, zm, zt, zH, zT, zD, zR, zV, zK, zA, zB, zdir, zvalues, zframe⟩
  have zN : z.regs BoxQuery.Reg.query = N := by regs_frame
  have zV' : z.regs BoxTable.Reg.values = valueBase L m t N := zV
  wram_exec [initializeCursors, zB, zT, zN, zL, zV', zK]
  refine ⟨by unfold preparationTime BoxQuery.preparationTime; omega,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, ?_, ?_, ?_, ?_, ?_⟩
  · wram_simp; unfold queryBase; omega
  · wram_simp; unfold queryBase; omega
  · wram_simp; unfold outputBase stackBase BoxQuery.stackCapacity; omega
  · constructor
    · intro i
      wram_simp
      rw [zframe _ (by unfold directoryBase queryBase; have := i.isLt; omega)]
      simpa only [Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hleft i
    · intro i
      wram_simp
      rw [zframe _ (by unfold directoryBase queryBase; have := i.isLt; omega)]
      simpa only [Data.set_mem, uμ, BoxTable.leafIndex_leafAt] using hright i
    · intro s hs; wram_simp; exact zdir s hs
    · intro s hs hv; wram_simp; exact zvalues s hs hv
  · intro p hp'
    wram_simp
    rw [zframe p (by unfold stackBase valueBase recordBase at hp'; omega)]
    exact congrFun uμ p

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
