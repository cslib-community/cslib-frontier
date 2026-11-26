/-
Copyright (c) 2026 Jonathan Katz, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import Mathlib.Data.Nat.Size

/-!
# Binary-indexed lookup in logarithmic space

A counter program reads the bit of a word at a binary index: it scans the word to learn its
length, then reads the index bit by bit, stopping as soon as the index provably exceeds the word,
and finally reads the indexed bit. It stores counters of `O(log (|w| + |i|))` bits.

## Main results

* `Turing.MultiTapeTM.computableInLogSpace_natBitLength`: the binary length of a number.
* `Turing.MultiTapeTM.computableInLogSpace_bitsGetElem?`: the optional bit of a word at a binary
  index.
-/

public section

namespace Turing.MultiTapeTM

open CounterProgram CounterProgram.Instr CounterProgram.Expr ComputableInSpace

/-- Number of binary digits of a natural number, computed in logarithmic space. -/
theorem computableInLogSpace_natBitLength :
    ComputableInLogSpace (fun m : ℕ => (encNat m).length) encNat encNat :=
  computableInLogSpace_bitsLength.comp
    (ComputableInLogSpace.of_eq (f := fun m : ℕ => encNat m)
      (encIn := encNat) (encMid := encBits) fun _ => rfl)

section BitsGetElem

private def bitsGetElemProgram : CounterProgram where
  code :=
    [read (mul (const 2) (reg 0)) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0,
     assign 2 (const 1) 3,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 4 6 9,
     lt (reg 0) (reg 2) 13 5,
     assign 3 (add (reg 3) (reg 2)) 7,
     lt (reg 0) (reg 2) 13 7,
     assign 2 (mul (const 2) (reg 2)) 8,
     assign 1 (add (reg 1) (const 1)) 3,
     lt (reg 3) (reg 0) 10 13,
     read (add (mul (const 2) (reg 3)) (const 1)) 11 12 13,
     halt [true, true],
     halt [true, false],
     halt []]
  registers := 4

private theorem bounded4_regs {B a₀ a₁ a₂ a₃ : ℕ}
    (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B) (h₃ : a₃ ≤ B) :
    ∀ r ∈ [a₀, a₁, a₂, a₃], r ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private def valBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * valBits bs

private theorem valBits_lt_two_pow : ∀ bs : List Bool, valBits bs < 2 ^ bs.length
  | [] => by simp [valBits]
  | b :: bs => by
    have ih := valBits_lt_two_pow bs
    simp only [valBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

private theorem valBits_bits (n : ℕ) : valBits n.bits = n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · rw [Nat.bit0_bits m hm.ne', valBits, valBits_bits m]
      simp
  · rw [Nat.bit1_bits m, valBits, valBits_bits m]
    simp [Nat.add_comm]
termination_by n

private theorem valBits_take_succ :
    ∀ (bs : List Bool) (j : ℕ) (hj : j < bs.length),
      valBits (bs.take (j + 1)) = valBits (bs.take j) + (if bs[j] then 2 ^ j else 0)
  | [], _, hj => absurd hj (by simp)
  | b :: bs, 0, _ => by
    simp only [List.take_succ_cons, List.take_zero, valBits, List.getElem_cons_zero, pow_zero]
    cases b <;> simp
  | b :: bs, j + 1, hj => by
    have hj' : j < bs.length := Nat.lt_of_succ_lt_succ hj
    simp only [List.take_succ_cons, valBits, List.getElem_cons_succ, valBits_take_succ bs j hj',
      pow_succ]
    (cases bs[j] <;> simp); omega

private theorem bitsGetElem_run (w : List Bool) (i : ℕ) {B : ℕ}
    (hB : 2 * w.length + 1 + i.bits.length + 1 ≤ B) :
    ∃ s, bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
      bitsGetElemProgram.init s ∧
      bitsGetElemProgram.instr s.1 = .halt (encOption encBool w[i]?) ∧
      ∀ r ∈ s.2, r ≤ B := by
  have scan : ∀ j ≤ w.length,
      bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
        (0, [j, 0, 0, 0]) (2, [w.length, 0, 0, 0]) := by
    intro j hj
    induction h : w.length - j generalizing j with
    | zero =>
      obtain rfl : j = w.length := by omega
      refine CounterProgram.Reaches.read (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simpa [getElem?_frame_append_length, readLabel] using
        CounterProgram.Reaches.refl (2, [w.length, 0, 0, 0])
    | succ _ ih =>
      refine CounterProgram.Reaches.read (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
        (getElem?_frame_append w i.bits (show j < w.length by omega)).1, readLabel]
      refine CounterProgram.Reaches.assign (by rfl)
        (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
      simpa using ih (j + 1) (by omega) (by omega)
  have setPow : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
      (2, [w.length, 0, 0, 0]) (3, [w.length, 0, 2 ^ 0, valBits (i.bits.take 0)]) := by
    refine CounterProgram.Reaches.assign (by rfl)
      (bounded4_regs (by omega) (by omega) (by omega) (by omega)) ?_
    simpa [valBits] using CounterProgram.Reaches.refl (3, [w.length, 0, 1, 0])
  have loop : ∀ j ≤ i.bits.length, 2 ^ j ≤ 2 * w.length + 1 →
      valBits (i.bits.take j) ≤ 2 * w.length →
      ∃ s, bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
        (3, [w.length, j, 2 ^ j, valBits (i.bits.take j)]) s ∧
        bitsGetElemProgram.instr s.1 = .halt (encOption encBool w[i]?) ∧
        ∀ r ∈ s.2, r ≤ B := by
    intro j hj
    induction h : i.bits.length - j generalizing j with
    | zero =>
      intro hpow hrem
      obtain rfl : j = i.bits.length := by omega
      have hval_eq : valBits (i.bits.take i.bits.length) = i := by
        rw [List.take_length, valBits_bits]
      rw [hval_eq] at hrem ⊢
      have hb := bounded4_regs (B := B) (a₀ := w.length) (a₁ := i.bits.length)
        (a₂ := 2 ^ i.bits.length) (a₃ := i) (by omega) (by omega) (by omega) (by omega)
      have h3 : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
          (3, [w.length, i.bits.length, 2 ^ i.bits.length, i])
          (9, [w.length, i.bits.length, 2 ^ i.bits.length, i]) := by
        refine CounterProgram.Reaches.read (by rfl) hb ?_
        simpa [getElem?_frame_append_boundary, readLabel] using
          CounterProgram.Reaches.refl (9, [w.length, i.bits.length, 2 ^ i.bits.length, i])
      by_cases hiw : i < w.length
      · have h9 : bitsGetElemProgram.Reaches (frame w ++ i.bits) (bitsGetElemProgram.Running B)
            (9, [w.length, i.bits.length, 2 ^ i.bits.length, i])
            (10, [w.length, i.bits.length, 2 ^ i.bits.length, i]) := by
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simpa [hiw] using CounterProgram.Reaches.refl _
        refine ⟨(if w[i] then 11 else 12, [w.length, i.bits.length, 2 ^ i.bits.length, i]),
          (h3.trans h9).trans ?_, ?_, hb⟩
        · refine CounterProgram.Reaches.read (by rfl) hb ?_
          cases hbit : w[i] <;>
            simpa [(getElem?_frame_append w i.bits hiw).2, hbit, readLabel] using
              CounterProgram.Reaches.refl _
        · cases hbit : w[i] <;>
            simp [List.getElem?_eq_getElem hiw, hbit, bitsGetElemProgram, instr]
      · refine ⟨(13, [w.length, i.bits.length, 2 ^ i.bits.length, i]), h3.trans ?_, ?_, hb⟩
        · refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simpa [hiw] using CounterProgram.Reaches.refl _
        · simp [List.getElem?_eq_none (by omega : w.length ≤ i), bitsGetElemProgram, instr]
    | succ _ ih =>
      intro hpow hrem
      have hj_lt : j < i.bits.length := by omega
      have hb := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ j)
        (a₃ := valBits (i.bits.take j)) (by omega) (by omega) (by omega) (by omega)
      by_cases hgt : w.length < 2 ^ j
      · have hj_sz : j < i.size := Nat.size_eq_bits_len i ▸ hj_lt
        have hi_ge : 2 ^ j ≤ i := Nat.lt_size.mp hj_sz
        have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
        refine ⟨(13, [w.length, j, 2 ^ j, valBits (i.bits.take j)]), ?_, ?_, hb⟩
        · refine CounterProgram.Reaches.read (by rfl) hb ?_
          simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
            List.getD_cons_succ, getElem?_frame_append_boundary, List.getElem?_eq_getElem hj_lt]
          cases i.bits[j] <;> dsimp only [readLabel] <;>
            exact CounterProgram.Reaches.lt (by rfl) hb
              (by simpa [hgt] using CounterProgram.Reaches.refl _)
        · simp [hnone, bitsGetElemProgram, instr]
      · have hpow_le_w : 2 ^ j ≤ w.length := by omega
        have hnext_pow : 2 ^ (j + 1) ≤ 2 * w.length + 1 := by
          rw [pow_succ]
          omega
        have hnext_rem : valBits (i.bits.take (j + 1)) ≤ 2 * w.length := by
          have hv := valBits_lt_two_pow (i.bits.take (j + 1))
          have htl : (i.bits.take (j + 1)).length = j + 1 :=
            List.length_take_of_le (by omega)
          rw [htl, pow_succ] at hv
          omega
        obtain ⟨s, hs, hout, hsB⟩ := ih (j + 1) (by omega) (by omega) hnext_pow hnext_rem
        refine ⟨s, ?_, hout, hsB⟩
        have hb7 := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ j)
          (a₃ := valBits (i.bits.take (j + 1))) (by omega) (by omega) (by omega) (by omega)
        have hb8 := bounded4_regs (B := B) (a₀ := w.length) (a₁ := j) (a₂ := 2 ^ (j + 1))
          (a₃ := valBits (i.bits.take (j + 1))) (by omega) (by omega) (by omega) (by omega)
        have htail7 : bitsGetElemProgram.Reaches (frame w ++ i.bits)
            (bitsGetElemProgram.Running B) (7, [w.length, j, 2 ^ j, valBits (i.bits.take (j + 1))])
            s := by
          refine CounterProgram.Reaches.assign (by rfl) hb7 ?_
          have hmul : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
          simp only [eval_mul, eval_const, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            List.set_cons_succ, List.set_cons_zero, hmul]
          refine CounterProgram.Reaches.assign (by rfl) hb8 ?_
          simpa using hs
        refine CounterProgram.Reaches.read (by rfl) hb ?_
        simp only [eval_add, eval_mul, eval_const, eval_reg, List.getD_cons_zero,
          List.getD_cons_succ, getElem?_frame_append_boundary, List.getElem?_eq_getElem hj_lt]
        have hstep_val := (valBits_take_succ i.bits j hj_lt).symm
        cases htb : i.bits[j]
        · simp only [htb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hstep_val
          dsimp only [readLabel]
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, hgt, ↓reduceIte]
          rwa [hstep_val]
        · simp only [htb, ↓reduceIte] at hstep_val
          dsimp only [readLabel]
          refine CounterProgram.Reaches.lt (by rfl) hb ?_
          simp only [eval_reg, List.getD_cons_zero, List.getD_cons_succ, hgt, ↓reduceIte]
          refine CounterProgram.Reaches.assign (by rfl) hb ?_
          simpa only [eval_add, eval_reg, List.getD_cons_succ, List.getD_cons_zero,
            List.set_cons_succ, List.set_cons_zero, hstep_val] using htail7
  obtain ⟨s, hs, hout, hsB⟩ := loop 0 (Nat.zero_le _) (by simp) (by simp [valBits])
  dsimp only [CounterProgram.init, bitsGetElemProgram, List.replicate]
  exact ⟨s, ((scan 0 (Nat.zero_le _)).trans setPow).trans hs, hout, hsB⟩

/-- Looking up an optional bit of `w` at a binary index `i` is computable in logarithmic space. -/
theorem computableInLogSpace_bitsGetElem? :
    ComputableInLogSpace (fun (w, i) => w[i]?) (encPair encBits encNat) (encOption encBool) := by
  refine bitsGetElemProgram.computableInLogSpace_of_reaches 1 fun ⟨w, i⟩ => ?_
  rw [pow_one, encPair_apply, encBits_apply, encNat_apply]
  refine bitsGetElem_run w i ?_
  rw [List.length_append, length_frame]

end BitsGetElem

end Turing.MultiTapeTM
