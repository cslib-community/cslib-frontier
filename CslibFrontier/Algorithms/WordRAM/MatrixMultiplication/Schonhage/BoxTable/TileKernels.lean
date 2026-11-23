/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native compact-table reads and signed arithmetic

The descriptor loads, leaf multiplication and child accumulation execute the actual
fixed-register program. The bounds include address arithmetic and operand loads as
well as the existing signed kernels. None of these routines changes memory.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers written while loading one three-word descriptor. -/
@[expose] def RecordLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.completion ∨ i = Reg.stars ∨ i = Reg.starPower

instance (i : Fin registers) : Decidable (RecordLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.completion ∨
    i = Reg.stars ∨ i = Reg.starPower))

/-- Read the three actual descriptor cells within seven native instructions. -/
theorem exec_loadRecord {w R j c e p : ℕ} (x : Data registers)
    (hR : x.regs Reg.records = R) (hj : x.regs Reg.current = j)
    (h1 : x.regs Reg.one = 1) (h3 : x.regs Reg.three = 3)
    (hc : x.mem (R + j * 3) = c) (he : x.mem (R + j * 3 + 1) = e)
    (hp : x.mem (R + j * 3 + 2) = p) (hfit : Fits w (R + j * 3 + 2)) :
    ∃ y, ExecWithin w loadRecord x y 7 ∧ y.regs Reg.completion = c ∧
      y.regs Reg.stars = e ∧ y.regs Reg.starPower = p ∧ y.mem = x.mem ∧
      (∀ i, ¬RecordLocal i → y.regs i = x.regs i) := by
  have hp' : x.mem (R + j * 3 + 1 + 1) = p := by simpa only [Nat.add_assoc] using hp
  suffices ∃ y, ExecWithin w loadRecord x y 7 ∧ y.regs Reg.completion = c ∧
      y.regs Reg.stars = e ∧ y.regs Reg.starPower = p ∧ y.mem = x.mem by
    obtain ⟨y, hy, hc', he', hp'', hm⟩ := this
    exact ⟨y, hy, hc', he', hp'', hm,
      fun i hi => hy.regs_eq (by unfold RecordLocal at hi; decide +revert)⟩
  unfold loadRecord
  wram_exec *
  wram_simp

/-- The signed workspace, indexed address and returned accumulator. -/
@[expose] def ProductLocal (i : Fin registers) : Prop :=
  i.val < 9 ∨ i = Reg.address ∨ i = Reg.accumulator

instance (i : Fin registers) : Decidable (ProductLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.address ∨ i = Reg.accumulator))

/-- Actual encoded leaf loads, signed multiplication and result delivery cost nineteen. -/
theorem exec_leafProduct {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers)
    (hleft : x.mem (x.regs Reg.arrayA + x.regs Reg.completion) = Signed.encode a)
    (hright : x.mem (x.regs Reg.arrayB + x.regs Reg.completion) = Signed.encode b)
    (hp : Fits (w + 2) (x.regs Reg.arrayA + x.regs Reg.completion))
    (hq : Fits (w + 2) (x.regs Reg.arrayB + x.regs Reg.completion)) :
    ∃ y, ExecWithin (w + 2) leafProduct x y 19 ∧
      y.regs Reg.accumulator = Signed.encode (a * b) ∧ y.mem = x.mem ∧
      (∀ i, ¬ProductLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin (w + 2) leafProduct x y 19 ∧
      y.regs Reg.accumulator = Signed.encode (a * b) ∧ y.mem = x.mem by
    obtain ⟨y, hy, hacc, hm⟩ := this
    exact ⟨y, hy, hacc, hm,
      fun i hi => hy.regs_eq (by unfold ProductLocal at hi; decide +revert)⟩
  unfold leafProduct leafLoad leafFinish
  wram_exec [*]
  wram_call (Signed.exec_multiply (r := 55) ha hb hab _
    (by wram_simp) (by wram_simp)) with u ⟨hproduct, hframe⟩
  wram_exec [hproduct]
  exact ⟨by wram_simp; rfl, by simpa only [Data.set_mem] using hframe.1⟩

/-- The signed workspace and native directory/value-address temporaries of one child. -/
@[expose] def ChildLocal (i : Fin registers) : Prop :=
  i.val < 9 ∨ i = Reg.temporary ∨ i = Reg.childCode ∨ i = Reg.childSlot ∨
    i = Reg.address ∨ i = Reg.childRank ∨ i = Reg.accumulator ∨ i = Reg.term

instance (i : Fin registers) : Decidable (ChildLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.temporary ∨ i = Reg.childCode ∨
    i = Reg.childSlot ∨ i = Reg.address ∨ i = Reg.childRank ∨
    i = Reg.accumulator ∨ i = Reg.term))

/-- Read the actual offset-one directory rank and child value, add it, and advance the term.
The caller supplies mathematical readback equalities, not an execution or time contract. -/
theorem exec_addChild {w D V c e T p d r : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hc : x.regs Reg.completion = c) (he : x.regs Reg.stars = e)
    (hT : x.regs Reg.span = T) (hTpos : 0 < T) (hp : x.regs Reg.starPower = p)
    (hd : x.regs Reg.term = d) (hacc : x.regs Reg.accumulator = Signed.encode a)
    (h9 : x.regs Reg.nine = 9) (h1 : x.regs Reg.one = 1)
    (hrank : x.mem (D + ((e - 1) * T + (c - (9 - d) * p))) = r + 1)
    (hvalue : x.mem (V + r) = Signed.encode b)
    (hfit : Fits (w + 2) (D + V + c + e * T + 10 * p + r + d + 20)) :
    ∃ y, ExecWithin (w + 2) addChild x y 29 ∧
      y.regs Reg.accumulator = Signed.encode (a + b) ∧ y.regs Reg.term = d + 1 ∧
      y.mem = x.mem ∧ (∀ i, ¬ChildLocal i → y.regs i = x.regs i) := by
  have hmp : (9 - d) * p ≤ 10 * p := Nat.mul_le_mul_right p (by omega)
  have hmt : (e - 1) * T ≤ e * T := Nat.mul_le_mul_right T (Nat.sub_le ..)
  have heT : e ≤ e * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left e hTpos
  suffices ∃ y, ExecWithin (w + 2) addChild x y 29 ∧
      y.regs Reg.accumulator = Signed.encode (a + b) ∧ y.regs Reg.term = d + 1 ∧
      y.mem = x.mem by
    obtain ⟨y, hy, hacc', hterm, hm⟩ := this
    exact ⟨y, hy, hacc', hterm, hm,
      fun i hi => hy.regs_eq (by unfold ChildLocal at hi; decide +revert)⟩
  unfold addChild childLoad childFinish
  wram_exec [*]
  wram_call (Signed.exec_add (r := 55) ha hb _
    (by wram_simp) (by wram_simp)) with u ⟨hsum, hframe⟩
  have hud : u.regs Reg.term = d :=
    (hframe.2 _ (Or.inr (by decide))).trans (by wram_simp [hd])
  have hu1 : u.regs Reg.one = 1 :=
    (hframe.2 _ (Or.inr (by decide))).trans (by wram_simp [h1])
  have hfinc : Fits (w + 2) (d + 1) := hfit.of_le (by omega)
  wram_exec [hsum, hud, hu1]
  exact ⟨by wram_simp; rfl, by wram_simp, by simpa only [Data.set_mem] using hframe.1⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
