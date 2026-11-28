/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Workspace
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Checked limbwise Boolean operations

Little-endian half-word digits support bitwise operations independently in each limb.
The fixed register lists determine the code. Four workspace registers are reserved as in
schoolbook multiplication.

## Main definitions

* `Cslib.WordRAM.Multiword.Bitwise.Supported`: and, or, and exclusive or.
* `Cslib.WordRAM.Multiword.Bitwise.program`: one standard instruction per limb.

## Main results

* `Cslib.WordRAM.Multiword.Bitwise.exec`: checked execution, exact reconstructed result,
  bounded output digits, and preservation of every register outside the output list.

## References

* [T. Hagerup, *Sorting and searching on the word RAM*][Hagerup1998].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bitwise

open Workspace

variable {r : ℕ}

/-- The binary Boolean operations supported by the limbwise routine. -/
def Supported (f : BinOp) : Prop := f = .and ∨ f = .or ∨ f = .xor

/-- Boolean operations preserve a power-of-two digit bound. -/
theorem eval_lt {f : BinOp} (hf : Supported f) {k a b : ℕ}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) : f.eval a b < 2 ^ k := by
  rcases hf with rfl | rfl | rfl
  · exact Nat.and_lt_two_pow a hb
  · exact Nat.or_lt_two_pow ha hb
  · exact Nat.xor_lt_two_pow ha hb

/-- A Boolean operation commutes with adjoining one low power-of-two digit. -/
theorem eval_cons {f : BinOp} (hf : Supported f) {k a b : ℕ}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) (A B : ℕ) :
    f.eval (a + 2 ^ k * A) (b + 2 ^ k * B) =
      f.eval a b + 2 ^ k * f.eval A B := by
  have hlt := eval_lt hf ha hb
  rw [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (f.eval a b)]
  apply Nat.eq_of_testBit_eq
  intro j
  rcases hf with rfl | rfl | rfl
  all_goals
    simp only [BinOp.eval] at hlt ⊢
    simp only [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
      Nat.testBit_two_pow_mul_add _ hlt,
      Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    split <;> rfl

/-- Unrolled limbwise code. A final workspace self-copy makes the empty program executable. -/
def program (f : BinOp) : List (Fin (r + 4)) → List (Fin (r + 4)) →
    List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, b :: bs, d :: ds => .seq (.op (.bin f d a b)) (program f as bs ds)
  | _, _, _ => .op (.copy carry carry)

/-- Exact code size, including the final self-copy. -/
theorem size_program (f : BinOp) (as bs ds : List (Fin (r + 4)))
    (hab : as.length = bs.length) (had : as.length = ds.length) :
    (program f as bs ds).size = ds.length + 1 := by
  induction as generalizing bs ds with
  | nil => cases bs <;> cases ds <;> simp_all [program]
  | cons a as ih =>
    cases bs <;> cases ds <;> simp_all [program, Code.size, Nat.add_comm]

/-- Execute a Boolean operation on equal-length bounded digit lists. Source lists may share
registers; destinations are distinct and disjoint from both sources. All non-output registers,
including all four workspace registers, are preserved. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) {f : BinOp} (hf : Supported f)
    (as bs ds : List (Fin (r + 4)))
    (hab : as.length = bs.length) (had : as.length = ds.length)
    (hin : ∀ i ∈ as ++ bs, IsDigit i) (hout : ∀ i ∈ ds, IsDigit i)
    (hnd : ds.Nodup) (hdis : List.Disjoint ds (as ++ bs))
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs) :
    ∃ y, Exec w (program f as bs ds) x y (ds.length + 1) ∧
      Bounded (radix w) y ds ∧
      value (radix w) y ds = f.eval (value (radix w) x as) (value (radix w) x bs) ∧
      Frame x y ds ∧ ∀ i ∉ ds, y.regs i = x.regs i := by
  induction as generalizing bs ds x with
  | nil =>
    obtain rfl := List.eq_nil_of_length_eq_zero hab.symm
    obtain rfl := List.eq_nil_of_length_eq_zero had.symm
    refine WP.Exact.exists_exec ?_
    wram_exec [program, List.length_nil]
    rcases hf with rfl | rfl | rfl <;>
      exact ⟨by simp [Bounded], by simp [value, BinOp.eval], frame_set_carry _ _ [], by simp⟩
  | cons a as ih =>
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_length_eq_add_one hab.symm
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_length_eq_add_one had.symm
    have sub_in {i : Fin (r + 4)} (hi : i ∈ as ++ bs) : i ∈ a :: as ++ b :: bs := by
      simp only [List.mem_append, List.mem_cons] at hi ⊢; tauto
    have hdis' : List.Disjoint ds (as ++ bs) :=
      List.disjoint_left.mpr fun i hi hj =>
        List.disjoint_left.mp hdis (List.mem_cons_of_mem d hi) (sub_in hj)
    have hne (i : Fin (r + 4)) (hi : i ∈ as ++ bs) : i ≠ d := by
      rintro rfl
      exact List.disjoint_left.mp hdis List.mem_cons_self (sub_in hi)
    have hzlt := eval_lt hf (ha a List.mem_cons_self) (hb b List.mem_cons_self)
    have hzfit : Fits w (f.eval (x.regs a) (x.regs b)) := hzlt.trans (radix_fits hw)
    refine WP.Exact.exists_exec ?_
    unfold program
    refine WP.Exact.seq (WP.Exact.bin rfl rfl rfl hzfit ?_)
    have hza (i : Fin (r + 4)) (hi : i ∈ as ++ bs) :
        (x.set d (f.eval (x.regs a) (x.regs b))).regs i = x.regs i := by
      have := hne i hi; wram_simp
    wram_call (ih bs ds (by simpa using hab) (by simpa using had)
      (fun i hi => hin i (sub_in hi)) (fun i hi => hout i (List.mem_cons_of_mem d hi))
      (List.nodup_cons.mp hnd).2 hdis' _
      (fun i hi => hza i (List.mem_append_left _ hi) ▸ ha i (List.mem_cons_of_mem a hi))
      (fun i hi => hza i (List.mem_append_right _ hi) ▸ hb i (List.mem_cons_of_mem b hi))) with
      y ⟨hyb, hyv, hyf, hyp⟩
    have hyd : y.regs d = f.eval (x.regs a) (x.regs b) := by
      rw [hyp d (List.nodup_cons.mp hnd).1]; wram_simp
    have hp : ∀ i ∉ d :: ds, y.regs i = x.regs i := fun i hi => by
      rw [hyp i (fun hm => hi (List.mem_cons_of_mem d hm))]
      have : i ≠ d := fun h => hi (h ▸ List.mem_cons_self)
      wram_simp
    refine ⟨by simp only [List.length_cons], fun i hi => ?_, ?_,
      ⟨hyf.1, fun i hi _ _ => hp i hi⟩, hp⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact hyd ▸ hzlt
      · exact hyb i hi
    · rw [value_cons, value_cons, value_cons, hyd, hyv,
        value_congr fun i hi => hza i (List.mem_append_left _ hi),
        value_congr fun i hi => hza i (List.mem_append_right _ hi)]
      exact (eval_cons hf (ha a List.mem_cons_self) (hb b List.mem_cons_self) _ _).symm

end Cslib.WordRAM.Multiword.Bitwise

end
