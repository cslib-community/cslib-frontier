/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual native query addends

Low-order leaves read two canonical signed array words and multiply them. Threshold
leaves compute the real directory key and read its stored value. Both paths add that
word to the actual signed accumulator using the existing unsigned arithmetic code.
Memory is unchanged; the caller supplies readback, not an execution or time contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- Registers changed while reading and adding one complete query leaf. -/
@[expose] def LeafLocal (i : Fin registers) : Prop :=
  i.val < 9 ∨ i = BoxTable.Reg.completion ∨ i = BoxTable.Reg.address ∨
    i = BoxTable.Reg.accumulator ∨ i = BoxTable.Reg.childRank ∨
    i = Reg.temporary ∨ i = Reg.answer

instance (i : Fin registers) : Decidable (LeafLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = BoxTable.Reg.completion ∨
    i = BoxTable.Reg.address ∨ i = BoxTable.Reg.accumulator ∨
    i = BoxTable.Reg.childRank ∨ i = Reg.temporary ∨ i = Reg.answer))

/-- The actual low-order addend costs at most twenty-one instructions and preserves memory. -/
theorem exec_lowAddend {w : ℕ} {a b : ℤ} (x : Data registers)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hab : GenericRAM.Signed.Fits w (a * b))
    (hleft : x.mem (x.regs BoxTable.Reg.arrayA + x.regs Reg.code) = Signed.encode a)
    (hright : x.mem (x.regs BoxTable.Reg.arrayB + x.regs Reg.code) = Signed.encode b)
    (hp : Fits (w + 2) (x.regs BoxTable.Reg.arrayA + x.regs Reg.code))
    (hq : Fits (w + 2) (x.regs BoxTable.Reg.arrayB + x.regs Reg.code)) :
    ∃ y, ExecWithin (w + 2) lowAddend x y 21 ∧
      y.regs Signed.right = Signed.encode (a * b) ∧ y.mem = x.mem ∧
      (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin (w + 2) lowAddend x y 21 ∧
      y.regs Signed.right = Signed.encode (a * b) ∧ y.mem = x.mem by
    obtain ⟨y, he, hr, hm⟩ := this
    exact ⟨y, he, hr, hm, fun i hi => he.regs_eq (by unfold LeafLocal at hi; decide +revert)⟩
  unfold lowAddend lowProduct
  wram_exec
  wram_call (BoxTable.exec_leafProduct ha hb hab _
    (by wram_simp; exact hleft) (by wram_simp; exact hright)
    (by wram_simp; exact hp) (by wram_simp; exact hq)) with v ⟨hprod, hmem, _⟩
  wram_exec [hprod]
  exact ⟨by wram_simp, by simpa only [Data.set_mem] using hmem⟩

/-- The threshold addend is an actual offset-one directory lookup and stored signed load. -/
theorem exec_boxAddend {w D V T c e r : ℕ} {a : ℤ} (x : Data registers)
    (hD : x.regs BoxTable.Reg.directory = D) (hV : x.regs BoxTable.Reg.values = V)
    (hT : x.regs BoxTable.Reg.span = T) (hc : x.regs Reg.code = c)
    (he : x.regs Reg.stars = e) (h1 : x.regs BoxTable.Reg.one = 1)
    (hrank : x.mem (D + (e * T + c)) = r + 1)
    (hvalue : x.mem (V + r) = Signed.encode a)
    (hfit : Fits w (D + V + e * T + c + r + 10)) :
    ∃ y, ExecWithin w boxAddend x y 7 ∧ y.regs Signed.right = Signed.encode a ∧
      y.mem = x.mem ∧ (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin w boxAddend x y 7 ∧ y.regs Signed.right = Signed.encode a ∧
      y.mem = x.mem by
    obtain ⟨y, hy, hr, hm⟩ := this
    exact ⟨y, hy, hr, hm, fun i hi => hy.regs_eq (by unfold LeafLocal at hi; decide +revert)⟩
  unfold boxAddend
  wram_exec * [hrank, hvalue]
  exact ⟨by wram_simp, rfl⟩

/-- Canonical signed addition and delivery preserve all memory and every nonlocal register. -/
theorem exec_addAnswer {w : ℕ} {a b : ℤ} (x : Data registers)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hacc : x.regs Reg.answer = Signed.encode a)
    (hadd : x.regs Signed.right = Signed.encode b) :
    ∃ y, ExecWithin (w + 2) addAnswer x y 17 ∧
      y.regs Reg.answer = Signed.encode (a + b) ∧ y.mem = x.mem ∧
      (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin (w + 2) addAnswer x y 17 ∧
      y.regs Reg.answer = Signed.encode (a + b) ∧ y.mem = x.mem by
    obtain ⟨y, he, hr, hm⟩ := this
    exact ⟨y, he, hr, hm, fun i hi => he.regs_eq (by unfold LeafLocal at hi; decide +revert)⟩
  unfold addAnswer
  wram_exec [*]
  wram_call (Signed.exec_add (r := 55) ha hb _ (by wram_simp) (by wram_simp [hadd]))
    with v ⟨hsum, hframe⟩
  wram_exec [hsum]
  exact ⟨by wram_simp; rfl, by simpa only [Data.set_mem] using hframe.1⟩

/-- The complete actual leaf branch charges direct products or stored-box lookup and addition. -/
theorem exec_leaf {w D V AA BB T c e d t r : ℕ} {a b v z : ℤ} (x : Data registers)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hab : GenericRAM.Signed.Fits w (a * b)) (hv : GenericRAM.Signed.Fits w v)
    (hz : GenericRAM.Signed.Fits w z)
    (hD : x.regs BoxTable.Reg.directory = D) (hV : x.regs BoxTable.Reg.values = V)
    (hAA : x.regs BoxTable.Reg.arrayA = AA) (hBB : x.regs BoxTable.Reg.arrayB = BB)
    (hT : x.regs BoxTable.Reg.span = T) (hc : x.regs Reg.code = c)
    (he : x.regs Reg.stars = e) (hd : x.regs Reg.used = d)
    (ht : x.regs BoxTable.Reg.threshold = t) (h1 : x.regs BoxTable.Reg.one = 1)
    (hacc : x.regs Reg.answer = Signed.encode z)
    (hlow : d < t → x.mem (AA + c) = Signed.encode a ∧
      x.mem (BB + c) = Signed.encode b)
    (hhigh : ¬d < t → x.mem (D + (e * T + c)) = r + 1 ∧
      x.mem (V + r) = Signed.encode v)
    (hfit : Fits (w + 2) (D + V + AA + BB + e * T + c + r + 10)) :
    ∃ y, ExecWithin (w + 2) leaf x y 39 ∧
      y.regs Reg.answer = Signed.encode (z + if d < t then a * b else v) ∧
      y.mem = x.mem ∧ (∀ i, ¬LeafLocal i → y.regs i = x.regs i) := by
  by_cases hdt : d < t
  · obtain ⟨u, hu, hvu, hum, huf⟩ := exec_lowAddend x ha hb hab
      (by simpa only [hAA, hc] using (hlow hdt).1)
      (by simpa only [hBB, hc] using (hlow hdt).2)
      (hfit.of_le (by rw [hAA, hc]; omega))
      (hfit.of_le (by rw [hBB, hc]; omega))
    have hua : u.regs Reg.answer = Signed.encode z := (hu.regs_eq (by decide)).trans hacc
    obtain ⟨y, hy, hya, hym, _⟩ := exec_addAnswer u hz hab hua hvu
    have hex : ExecWithin (w + 2) leaf x y 39 :=
      ((hu.branch_pos (by simpa only [Cond.holds_lt, hd, ht] using hdt)).seq hy).mono (by omega)
    exact ⟨y, hex, by simpa only [ite_eq_left hdt] using hya, hym.trans hum,
      fun i hi => hex.regs_eq (by unfold LeafLocal at hi; decide +revert)⟩
  · obtain ⟨u, hu, hvu, hum, _⟩ := exec_boxAddend x hD hV hT hc he h1
      (hhigh hdt).1 (hhigh hdt).2 (hfit.of_le (by omega))
    have hua : u.regs Reg.answer = Signed.encode z := (hu.regs_eq (by decide)).trans hacc
    obtain ⟨y, hy, hya, hym, _⟩ := exec_addAnswer u hz hv hua hvu
    have hex : ExecWithin (w + 2) leaf x y 39 :=
      ((hu.branch_neg (by simpa only [Cond.holds_lt, hd, ht] using hdt)).seq hy).mono (by omega)
    exact ⟨y, hex, by simpa only [ite_eq_right hdt] using hya, hym.trans hum,
      fun i hi => hex.regs_eq (by unfold LeafLocal at hi; decide +revert)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
