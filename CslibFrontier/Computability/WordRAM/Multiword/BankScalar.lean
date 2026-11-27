/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Bank
public import CslibFrontier.Computability.WordRAM.Multiword.Transfer
public import CslibFrontier.Computability.WordRAM.Multiword.Shift
import CslibFrontier.Tactic.WramOmega

/-!
# Scalar operations and variable shifts on multiword banks

Scalar operations assemble both operands before writing the destination, so the destination
may coincide with either source. Their inputs and result must fit the physical word width.
Variable right shifts assemble only the shift amount; the shifted input remains multiword.

## Main definitions

* `Bank.scalarLeft`, `Bank.scalarRight`, `Bank.scalarResult`: physical registers four, five, and
  six used for assembled scalar operands and results.
* `Bank.scalar`: a checked physical binary operation between bank entries.
* `Bank.shift`: a variable right shift into a distinct bank entry.

## Main results

* `Bank.exec_scalar`: exact execution in 133 instructions, preserving other entries and memory.
* `Bank.exec_shift`: execution within 123 instructions, preserving other entries and memory.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bank

open Workspace

variable {n : ℕ}

/-- Physical register four stores the assembled left operand or shift amount. -/
abbrev scalarLeft : Fin (capacity n + 4) := ⟨4, by dsimp [capacity]; omega⟩
/-- Physical register five stores the assembled right operand. -/
abbrev scalarRight : Fin (capacity n + 4) := ⟨5, by dsimp [capacity]; omega⟩
/-- Physical register six stores the checked scalar result. -/
abbrev scalarResult : Fin (capacity n + 4) := ⟨6, by dsimp [capacity]; omega⟩

private theorem value_preserved {w : ℕ} {x y : Data (capacity n + 4)} (j : Fin n)
    (hp : ∀ i, 44 ≤ i.val → y.regs i = x.regs i) :
    value (radix w) y (regs j) = value (radix w) x (regs j) :=
  value_congr fun i hi => hp i (by have := mem_regs hi; omega)

private theorem exec_assemble_bank {w : ℕ} (hw : 2 ≤ w) (j : Fin n)
    (s : Fin (capacity n + 4)) (hs : s.val < 44)
    (x : Data (capacity n + 4)) {val : ℕ}
    (hval : value (radix w) x (regs j) = val) (hf : Fits w val) :
    ∃ u, Exec w (Transfer.assemble (regs j) s) x u 44 ∧
      u.regs s = val ∧ u.mem = x.mem ∧
      (∀ i, IsDigit i → i ≠ s → u.regs i = x.regs i) ∧
      (∀ i, 44 ≤ i.val → u.regs i = x.regs i) := by
  obtain ⟨u, heu, hus, huf, hup⟩ := Transfer.exec_assemble hw (regs j) s
    (digit_regs j) x (hval.symm ▸ hf)
  refine ⟨u, by simpa only [length_regs] using heu, hus.trans hval, huf.1, hup, fun i hi =>
    hup i (by dsimp [IsDigit]; omega) fun h => by have := congrArg Fin.val h; omega⟩

/-- Assemble into physical registers four and five, compute in register six, and split the
checked result into the destination. Both inputs are read before any bank entry is written. -/
def scalar (f : BinOp) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Transfer.assemble (regs a) scalarLeft)
    (.seq (Transfer.assemble (regs b) scalarRight)
      (.seq (.op (.bin f scalarResult scalarLeft scalarRight))
        (Transfer.split scalarResult (regs d))))

/-- Scalar operations compile to exactly 133 instructions, independently of word width. -/
theorem size_scalar (f : BinOp) (a b d : Fin n) : (scalar f a b d).size = 133 := by
  simp [scalar, Transfer.size_assemble, Transfer.size_split, length_regs]

/-- Checked scalar arithmetic permits either source to coincide with the destination. -/
theorem exec_scalar {w : ℕ} (hw : 2 ≤ w) (f : BinOp) (a b d : Fin n)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v)
    (hfa : Fits w (v a)) (hfb : Fits w (v b))
    (hresult : Fits w (f.eval (v a) (v b))) :
    ∃ y, Exec w (scalar f a b d) x y 133 ∧
      Encodes w y (Function.update v d (f.eval (v a) (v b))) ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hua, hum, _, hup⟩ := exec_assemble_bank hw a scalarLeft (by simp) x
    (hx a).2 hfa
  obtain ⟨t, het, htb, htm, htp_d, htp⟩ := exec_assemble_bank hw b scalarRight (by simp) u
    ((value_preserved b hup).trans (hx b).2) hfb
  have hta : t.regs scalarLeft = v a :=
    (htp_d scalarLeft (by simp [IsDigit]) (by simp [Fin.ext_iff])).trans hua
  let z := t.set scalarResult (f.eval (t.regs scalarLeft) (t.regs scalarRight))
  have hzv : z.regs scalarResult = f.eval (v a) (v b) := by
    simp only [z, Data.set_regs, Function.update_self, hta, htb]
  have hez : Exec w (.op (.bin f scalarResult scalarLeft scalarRight)) t z 1 :=
    Exec.bin (by rwa [hta, htb])
  obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := Transfer.exec_split_eighteen hw scalarResult
    (regs d) (length_regs d) (by simp [IsDigit]) (digit_regs d) (nodup_regs d) z
    (by rwa [hzv])
  refine ⟨y, heu.seq (het.seq (hez.seq hey)), encodes_update hx d _ hyb (hyv.trans hzv) ?_,
    hyf.1.trans (htm.trans hum)⟩
  intro i hi hid
  have hs : i ≠ scalarResult := fun h => by have := congrArg Fin.val h; dsimp at this; omega
  rw [hyp i (by wram_omega) hid, show z.regs i = t.regs i from Function.update_of_ne hs _ _,
    htp i hi, hup i hi]

/-- Assemble the scalar shift amount in physical register four, then shift the multiword input.
The destination must be distinct from the input, but may contain the original shift amount. -/
def shift (w : ℕ) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Transfer.assemble (regs b) scalarLeft) (Shift.program w (regs a) (regs d) scalarLeft)

/-- The compiled size is independent of physical word width. -/
theorem size_shift (w : ℕ) (a b d : Fin n) : (shift w a b d).size = 1014 := by
  simp only [shift, Code.size, Transfer.size_assemble, length_regs,
    Shift.size_program_eighteen w (regs a) (regs d) scalarLeft (length_regs a) (length_regs d)]

/-- Multiword right shifts require only the shift amount to fit a physical word. -/
theorem exec_shift {w : ℕ} (hw : 2 ≤ w) (a b d : Fin n) (hda : d ≠ a)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v)
    (hfb : Fits w (v b)) :
    ∃ y, ExecWithin w (shift w a b d) x y 123 ∧
      Encodes w y (Function.update v d (v a >>> v b)) ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hub, hum, _, hup⟩ := exec_assemble_bank hw b scalarLeft (by simp) x
    (hx b).2 hfb
  have hua : Bounded (radix w) u (regs a) := fun i hi =>
    hup i (by have := mem_regs hi; omega) ▸ (hx a).1 i hi
  have hnot : scalarLeft ∉ regs d := fun h => by have := mem_regs h; dsimp at this; omega
  obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := Shift.exec_eighteen hw (regs a) (regs d)
    scalarLeft (length_regs a) (length_regs d) (digit_regs a) (digit_regs d)
    (by simp [IsDigit]) (nodup_regs d) (disjoint_regs hda) hnot u hua (hub ▸ hfb)
  rw [value_preserved a hup, (hx a).2, hub] at hyv
  refine ⟨y, heu.within.seq hey, encodes_update hx d _ hyb hyv fun i hi hid => ?_,
    hyf.1.trans hum⟩
  rw [hyp i (by wram_omega) hid, hup i hi]

end Cslib.WordRAM.Multiword.Bank

end
