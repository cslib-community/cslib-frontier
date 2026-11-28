/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Workspace
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.Nat.Choose.Basic

/-!
# Schoolbook multiplication on the checked word RAM

The code is unrolled for fixed operand lengths. Each row adds one shifted digit product
to the accumulator and appends its final carry. Leading zero updates make the active
accumulator and shifted operand have the same length.

## Main definitions

* `Cslib.WordRAM.Multiword.Schoolbook.cell`, `Cslib.WordRAM.Multiword.Schoolbook.row`: one
  multiply-add cell and one complete multiply-add row.
* `Cslib.WordRAM.Multiword.Schoolbook.rows`, `Cslib.WordRAM.Multiword.Schoolbook.rowCost`,
  `Cslib.WordRAM.Multiword.Schoolbook.clear`, `Cslib.WordRAM.Multiword.Schoolbook.program`:
  the unrolled schoolbook rows, their instruction cost, accumulator clearing, and full
  multiplication routine.
* `Cslib.WordRAM.Multiword.Schoolbook.registers`,
  `Cslib.WordRAM.Multiword.Schoolbook.leftRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.rightRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.outputRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.lowRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.highRegs`,
  `Cslib.WordRAM.Multiword.Schoolbook.fixedProgram`,
  `Cslib.WordRAM.Multiword.Schoolbook.input`: a concrete register allocation and input
  encoding for arbitrary fixed operand lengths.

## Main results

* `Cslib.WordRAM.Multiword.Schoolbook.registers_bounds`,
  `Cslib.WordRAM.Multiword.Schoolbook.nodup_registers`: index bounds and duplicate-freedom for
  contiguous digit-register slices.
* `Cslib.WordRAM.Multiword.Schoolbook.exec_fixedProgram`: exact multiplication, bounded digits,
  preservation of operands and memory, and an exact width-independent instruction count.
* `Cslib.WordRAM.Multiword.Schoolbook.exec_eighteen`: 18-digit operands, 36 result digits,
  76 registers, and 2465 instructions for every physical word width at least two.

Inputs and outputs use little-endian half-word digits. Conversion from other representations
is not part of the routine. Odd widths use the same floor-half radix. Widths zero and one
are excluded: their floor-half radix is one and cannot represent a nonzero integer.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Schoolbook

open Workspace

variable {r : ℕ}

/-- The in-place form of `LimbUpdate.program`: five ordinary instructions for one multiply-add,
overwriting the destination digit after reading it. -/
def cell (a b d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  total ← a * b;
  total ← total + d;
  total ← total + carry;
  d ← total % base;
  carry ← total / base ]

private theorem exec_cell {w : ℕ} (x : Data (r + 4)) (a b d : Fin (r + 4))
    (hd : IsDigit d) (hbase : x.regs base = radix w)
    (ha : x.regs a < radix w) (hb : x.regs b < radix w)
    (hx : x.regs d < radix w) (hc : x.regs carry < radix w) :
    ∃ y, Exec w (cell a b d) x y 5 ∧
      y.regs d < radix w ∧ y.regs carry < radix w ∧
      y.regs d + radix w * y.regs carry = x.regs a * x.regs b + x.regs d + x.regs carry ∧
      Frame x y [d] := by
  obtain ⟨hdt, hdc, hdb, _⟩ := digit_ne hd
  have hs := limb_update_fits ha hb hx hc
  have hβ : 0 < radix w := Nat.two_pow_pos _
  refine WP.Exact.exists_exec ?_
  wram_exec [cell, hbase, hs]
  refine ⟨?_, ?_, ?_, rfl, fun i hi _ _ => by simp only [List.mem_singleton] at hi; wram_simp⟩
  · wram_simp; exact Nat.mod_lt _ hβ
  · wram_simp
    exact (Nat.div_lt_iff_lt_mul hβ).mpr
      (by simpa only [pow_two] using limb_update_lt_sq ha hb hx hc)
  · wram_simp; exact Nat.mod_add_div _ _

/-- Update a full row. The final self-copy gives the empty row a one-instruction execution. -/
def row (a : Fin (r + 4)) : List (Fin (r + 4)) → List (Fin (r + 4)) →
    Code .standard (r + 4)
  | b :: bs, d :: ds => .seq (cell a b d) (row a bs ds)
  | _, _ => .op (.copy carry carry)

/-- A row has one five-instruction cell per digit and one final self-copy. -/
theorem size_row (a : Fin (r + 4)) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) : (row a bs ds).size = 5 * ds.length + 1 := by
  induction bs generalizing ds with
  | nil => cases ds <;> simp_all [row]
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds => simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
                   simp only [row, Code.size, cell, ih ds hlen, List.length_cons]
                   omega

/-- Execute an entire row, with exact reconstruction including its final carry.
`I` is any set of preserved input registers, disjoint from the destination registers. -/
private theorem exec_row {w : ℕ} (I : Set (Fin (r + 4)))
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (a : Fin (r + 4)) (haI : a ∈ I)
    (bs ds : List (Fin (r + 4))) (hlen : bs.length = ds.length)
    (hbs : ∀ b ∈ bs, b ∈ I) (hds : ∀ d ∈ ds, IsDigit d ∧ d ∉ I)
    (hnd : ds.Nodup) (x : Data (r + 4)) (hbase : x.regs base = radix w)
    (ha : x.regs a < radix w) (hb : Bounded (radix w) x bs)
    (hd : Bounded (radix w) x ds) (hc : x.regs carry < radix w) :
    ∃ y, Exec w (row a bs ds) x y (5 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs carry < radix w ∧
      value (radix w) y ds + radix w ^ ds.length * y.regs carry =
        x.regs a * value (radix w) x bs + value (radix w) x ds + x.regs carry ∧
      Frame x y ds := by
  induction bs generalizing ds x with
  | nil =>
    cases ds with
    | nil =>
      refine WP.Exact.exists_exec ?_
      unfold row
      wram_exec [List.length_nil]
      exact ⟨by simp [Bounded], by wram_simp [hc], by simp [value], frame_set_carry _ _ []⟩
    | cons => simp_all
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hd0 := hds d List.mem_cons_self
      have hds_d : ∀ i ∈ ds, IsDigit i := fun i hi => (hds i (List.mem_cons_of_mem d hi)).1
      have hdnot : d ∉ ds := (List.nodup_cons.mp hnd).1
      refine WP.Exact.exists_exec ?_
      unfold row
      wram_call (exec_cell x a b d hd0.1 hbase ha (hb b List.mem_cons_self)
        (hd d List.mem_cons_self) hc) with z ⟨hzd, hzc, hzeq, hzf⟩
      have hzI {i : Fin (r + 4)} (hi : i ∈ I) : z.regs i = x.regs i :=
        hzf.2 i (fun hm => hd0.2 (List.mem_singleton.mp hm ▸ hi)) (hI i hi).1 (hI i hi).2
      wram_call (ih ds (by simpa using hlen)
        (fun i hi => hbs i (List.mem_cons_of_mem b hi))
        (fun i hi => hds i (List.mem_cons_of_mem d hi))
        (List.nodup_cons.mp hnd).2 z ((hzf.base_regs (by simpa using hd0.1)).trans hbase)
        (hzI haI ▸ ha)
        (fun i hi => hzI (hbs i (List.mem_cons_of_mem b hi)) ▸ hb i (List.mem_cons_of_mem b hi))
        (hzf.bounded_of_digits hds_d (fun _ hi hm => hdnot (List.mem_singleton.mp hm ▸ hi))
          fun i hi => hd i (List.mem_cons_of_mem d hi)) hzc) with y ⟨hyd, hyc, hyeq, hyf⟩
      obtain ⟨hyd0, hvalds, hyb, hyframe⟩ := hzf.cons_step hyf hd0.1 hds_d hdnot hzd hyd
      have hvalbs : value (radix w) z bs = value (radix w) x bs :=
        value_congr fun i hi => hzI (hbs i (List.mem_cons_of_mem b hi))
      rw [hzI haI, hvalbs, hvalds] at hyeq
      refine ⟨by simp only [List.length_cons]; omega, hyb, hyc, ?_, hyframe⟩
      simp only [value_cons, List.length_cons, pow_succ, hyd0]
      linarith [congrArg (radix w * ·) hyeq]

/-- Unrolled schoolbook rows. `ds` is the current accumulator and `os` supplies one fresh
high digit per remaining multiplicand digit. The multiplier gains a leading zero each row. -/
def rows : List (Fin (r + 4)) → List (Fin (r + 4)) → List (Fin (r + 4)) →
    List (Fin (r + 4)) → Code .standard (r + 4)
  | a :: as, bs, ds, d :: os =>
    .seq (.op (.const carry 0)) (.seq (row a bs ds)
      (.seq (.op (.copy d carry)) (rows as (zero :: bs) (ds ++ [d]) os)))
  | _, _, _, _ => .op (.const carry 0)

/-- Exact instruction count of the unrolled rows, including empty-row self-copies. -/
def rowCost : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, n => 5 * n + 3 + rowCost m (n + 1)

/-- The extra cells are the leading-zero updates in successive shifted rows. -/
theorem rowCost_eq (m n : ℕ) :
    rowCost m n = 5 * (m * n + m * (m - 1) / 2) + 3 * m + 1 := by
  have h : rowCost m n = 5 * (m * n + m.choose 2) + 3 * m + 1 := by
    induction m generalizing n with
    | zero => simp [rowCost]
    | succ m ih =>
      have hs : (m + 1).choose 2 = m + m.choose 2 := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
      rw [rowCost, ih, hs]
      ring
  simpa only [Nat.choose_two_right] using h

/-- The instruction count of `rows` equals `rowCost` on the operand lengths. -/
theorem size_rows (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length) :
    (rows as bs ds os).size = rowCost as.length bs.length := by
  induction as generalizing bs ds os with
  | nil => cases os <;> simp_all [rows, rowCost]
  | cons a as ih =>
    cases os with
    | nil => simp_all
    | cons d os =>
      have hos' : os.length = as.length := by simpa using hos
      simp only [rows, Code.size, size_row a bs ds hlen,
        ih (zero :: bs) (ds ++ [d]) os (by simp [hlen]) hos',
        List.length_cons, rowCost]
      omega

/-- The runtime is constant for fixed operand lengths, independently of the physical width. -/
theorem rowCost_le (m n : ℕ) : rowCost m n ≤ 5 * m * (n + m) + 3 * m + 1 := by
  induction m generalizing n with
  | zero => simp [rowCost]
  | succ m ih =>
    have := ih (n + 1)
    simp only [rowCost]
    nlinarith

private theorem frame_input {x y : Data (r + 4)} {I : Set (Fin (r + 4))}
    {ds : List (Fin (r + 4))} (hf : Frame x y ds)
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (hd : ∀ d ∈ ds, d ∉ I)
    {i : Fin (r + 4)} (hi : i ∈ I) : y.regs i = x.regs i :=
  hf.2 i (fun hm => hd i hm hi) (hI i hi).1 (hI i hi).2

/-- Complete schoolbook multiplication with an arbitrary initial accumulator. The theorem
constructs an execution and proves its product equation; no multiplication specification is
assumed. The accumulator grows by one carry digit per row. -/
private theorem exec_rows {w : ℕ} (hw : 2 ≤ w) (I : Set (Fin (r + 4)))
    (hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry) (hzI : zero ∈ I)
    (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (has : ∀ a ∈ as, a ∈ I) (hbs : ∀ b ∈ bs, b ∈ I)
    (hds : ∀ d ∈ ds ++ os, IsDigit d ∧ d ∉ I) (hnd : (ds ++ os).Nodup)
    (x : Data (r + 4)) (hbase : x.regs base = radix w) (hz : x.regs zero = 0)
    (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs)
    (hd : Bounded (radix w) x ds) :
    ∃ y, Exec w (rows as bs ds os) x y (rowCost as.length bs.length) ∧
      Bounded (radix w) y (ds ++ os) ∧
      value (radix w) y (ds ++ os) =
        value (radix w) x ds + value (radix w) x as * value (radix w) x bs ∧
      Frame x y (ds ++ os) := by
  induction as generalizing bs ds os x with
  | nil =>
    have hos' : os = [] := by simpa using hos
    subst os
    have hf := frame_set_carry x 0 []
    have hds_d : ∀ i ∈ ds, IsDigit i := fun i hi => (hds i (by simp [hi])).1
    refine WP.Exact.exists_exec ?_
    unfold rows
    wram_exec [List.length_nil, rowCost]
    exact ⟨by simpa only [List.append_nil] using hf.bounded_of_digits hds_d (by simp) hd,
      by rw [List.append_nil, hf.value_eq_of_digits hds_d (by simp)]; simp [value],
      by simpa only [List.append_nil] using frame_mono hf (by simp)⟩
  | cons a as ih =>
    cases os with
    | nil => simp_all
    | cons d os =>
      have hdd := hds d (by simp)
      have hds' : ∀ i ∈ ds, IsDigit i ∧ i ∉ I := fun i hi => hds i (by simp [hi])
      have hds_d : ∀ i ∈ ds, IsDigit i := fun i hi => (hds' i hi).1
      have hdnot : d ∉ ds := fun hm => (List.nodup_append.mp hnd).2.2 d hm d (by simp) rfl
      have hdis_d : ∀ i ∈ ds, i ∉ [d] := fun _ hi hm => hdnot (List.mem_singleton.mp hm ▸ hi)
      have hx₀ : Frame x (x.set carry 0) [] := frame_set_carry x 0 []
      have hx₀I {i : Fin (r + 4)} (hi : i ∈ I) : (x.set carry 0).regs i = x.regs i :=
        frame_input hx₀ hI (by simp) hi
      refine WP.Exact.exists_exec ?_
      unfold rows
      wram_exec
      wram_call (exec_row I hI a (has a List.mem_cons_self) bs ds hlen hbs hds'
        (List.nodup_append.mp hnd).1 _ (by wram_simp [hbase])
        (hx₀I (has a List.mem_cons_self) ▸ ha a List.mem_cons_self)
        (fun i hi => hx₀I (hbs i hi) ▸ hb i hi)
        (hx₀.bounded_of_digits hds_d (by simp) hd)
        (by wram_simp; exact Nat.zero_lt_of_lt (one_lt_radix hw))) with z ⟨hzd, hzc, hzeq, hzf⟩
      wram_exec
      have hfzu : Frame z (z.set d (z.regs carry)) [d] := frame_set_mem z _
      have hfxu : Frame x (z.set d (z.regs carry)) (ds ++ [d]) :=
        frame_trans (frame_mono (frame_trans (frame_mono hx₀ (by simp)) hzf) (by simp))
          (frame_mono hfzu (by simp))
      have hds1 : ∀ j ∈ ds ++ [d], IsDigit j ∧ j ∉ I := fun j hj =>
        hds j (by simp only [List.mem_append, List.mem_cons] at hj ⊢; tauto)
      have huI {i : Fin (r + 4)} (hi : i ∈ I) : (z.set d (z.regs carry)).regs i = x.regs i :=
        frame_input hfxu hI (fun j hj => (hds1 j hj).2) hi
      have huDs : Bounded (radix w) (z.set d (z.regs carry)) (ds ++ [d]) := fun i hi => by
        rcases List.mem_append.mp hi with hi | hi
        · exact hfzu.bounded_of_digits hds_d hdis_d hzd i hi
        · rw [List.mem_singleton.mp hi]; wram_simp [hzc]
      have hnext : (ds ++ [d]) ++ os = ds ++ d :: os := by simp
      wram_call (ih (zero :: bs) (ds ++ [d]) os (by simp [hlen]) (by simpa using hos)
        (fun i hi => has i (List.mem_cons_of_mem a hi))
        (fun i hi => by rcases List.mem_cons.mp hi with rfl | hi; exacts [hzI, hbs i hi])
        (hnext.symm ▸ hds) (hnext.symm ▸ hnd) _
        ((hfxu.base_regs fun j hj => (hds1 j hj).1).trans hbase) (huI hzI ▸ hz)
        (fun i hi => huI (has i (List.mem_cons_of_mem a hi)) ▸ ha i (List.mem_cons_of_mem a hi))
        (fun i hi => by
          rcases List.mem_cons.mp hi with rfl | hi
          · rw [huI hzI, hz]; exact Nat.zero_lt_of_lt (one_lt_radix hw)
          · exact huI (hbs i hi) ▸ hb i hi)
        huDs) with y ⟨hyd, hyeq, hyf⟩
      rw [hnext] at hyd hyeq hyf
      refine ⟨by simp only [hlen, List.length_cons, rowCost]; omega, hyd, ?_,
        frame_trans (frame_mono hfxu (by simp)) hyf⟩
      have huValDs : value (radix w) (z.set d (z.regs carry)) (ds ++ [d]) =
          value (radix w) x ds + x.regs a * value (radix w) x bs := by
        simp only [value, List.map_append, Nat.ofDigits_append, List.length_map,
          List.map_singleton, Nat.ofDigits_singleton]
        change value (radix w) _ ds + radix w ^ ds.length * (z.set d (z.regs carry)).regs d = _
        wram_simp [hfzu.value_eq_of_digits (β := radix w) hds_d hdis_d, hzeq,
          hx₀I (has a List.mem_cons_self),
          value_congr (β := radix w) fun i hi => hx₀I (hbs i hi),
          hx₀.value_eq_of_digits (β := radix w) hds_d (by simp)]
        exact Nat.add_comm _ _
      rw [huValDs, value_congr (β := radix w) fun i hi => huI (has i (List.mem_cons_of_mem a hi)),
        value_cons, huI hzI, hz, zero_add,
        value_congr (β := radix w) fun i hi => huI (hbs i hi)] at hyeq
      rw [hyeq, value_cons]
      ring

/-- Clear the initial accumulator; the empty clear uses one carry self-copy. -/
def clear : List (Fin (r + 4)) → Code .standard (r + 4)
  | [] => .op (.copy carry carry)
  | d :: ds => .seq (.op (.const d 0)) (clear ds)

/-- Clearing `ds` takes one constant instruction per digit plus one final self-copy. -/
theorem size_clear (ds : List (Fin (r + 4))) : (clear ds).size = ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [clear, Code.size, ih, List.length_cons]; omega

/-- Clearing distinct digit registers zeroes them in `ds.length + 1` instructions, changing only
them and the carry workspace. -/
theorem exec_clear {w : ℕ} (ds : List (Fin (r + 4)))
    (hds : ∀ i ∈ ds, IsDigit i) (hnd : ds.Nodup) (x : Data (r + 4)) :
    ∃ y, Exec w (clear ds) x y (ds.length + 1) ∧
      (∀ i ∈ ds, y.regs i = 0) ∧ Frame x y ds := by
  induction ds generalizing x with
  | nil =>
    refine WP.Exact.exists_exec ?_
    unfold clear
    wram_exec [List.length_nil]
    exact ⟨by simp, frame_set_carry _ _ []⟩
  | cons d ds ih =>
    refine WP.Exact.exists_exec ?_
    unfold clear
    wram_exec
    wram_call (ih (fun i hi => hds i (List.mem_cons_of_mem d hi))
      (List.nodup_cons.mp hnd).2 _) with y ⟨hy, hyf⟩
    refine ⟨by simp only [List.length_cons], fun i hi => ?_,
      frame_trans (frame_set_mem x 0) (frame_mono hyf (by simp))⟩
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hyf.digit_regs (hds i List.mem_cons_self) (List.nodup_cons.mp hnd).1]; wram_simp
    · exact hy i hi

/-- Complete multiplication: initialize the radix and zero, clear the initial accumulator,
and execute all rows. Operand and output register lists are fixed at code construction time. -/
def program (as bs ds os : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq setup (.seq (clear ds) (rows as bs ds os))

/-- Exact code size, which is also the exact execution time on valid inputs. -/
theorem size_program (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length) :
    (program as bs ds os).size = 7 + bs.length + rowCost as.length bs.length := by
  simp only [program, Code.size, setup, size_clear, size_rows as bs ds os hlen hos]
  omega

/-- Multiplication of two arbitrary fixed-length little-endian digit lists. All outputs
start arbitrary: initialization is part of the charged code. Every arithmetic operation uses
the original physical width and checked overflow. The complete product occupies `ds ++ os`.
The layout assumptions express only nonaliasing and reserved-register separation. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (hin : ∀ i ∈ as ++ bs, IsDigit i) (hout : ∀ i ∈ ds ++ os, IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4)) (ha : Bounded (radix w) x as) (hb : Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y
        (7 + bs.length + rowCost as.length bs.length) ∧
      Bounded (radix w) y (ds ++ os) ∧
      value (radix w) y (ds ++ os) = value (radix w) x as * value (radix w) x bs ∧
      y.mem = x.mem ∧ ∀ i ∈ as ++ bs, y.regs i = x.regs i := by
  let I : Set (Fin (r + 4)) := {i | i = zero ∨ i ∈ as ++ bs}
  have hI : ∀ i ∈ I, i ≠ total ∧ i ≠ carry := by
    rintro i (rfl | hi)
    · simp [zero, total, carry]
    · exact ⟨(digit_ne (hin i hi)).1, (digit_ne (hin i hi)).2.1⟩
  have houtI : ∀ i ∈ ds ++ os, IsDigit i ∧ i ∉ I := fun i hi =>
    ⟨hout i hi, by
      rintro (hz | hin')
      · exact (digit_ne (hout i hi)).2.2.2 hz
      · exact List.disjoint_left.mp hdis hi hin'⟩
  have hds_digit : ∀ i ∈ ds, IsDigit i := fun i hi => hout i (List.mem_append_left _ hi)
  refine WP.Exact.exists_exec ?_
  unfold program
  wram_call (exec_setup hw x)
  wram_call (exec_clear (w := w) ds hds_digit (List.nodup_append.mp hnd).1 _)
    with u ⟨hu, huf⟩
  have hui {i : Fin (r + 4)} (hi : i ∈ as ++ bs) : u.regs i = x.regs i :=
    (huf.digit_regs (hin i hi) fun hm =>
      List.disjoint_left.mp hdis (List.mem_append_left _ hm) hi).trans
      (setup_digit w x (hin i hi))
  wram_call (exec_rows hw I hI (Or.inl rfl) as bs ds os hlen hos
    (fun i hi => Or.inr (List.mem_append_left _ hi))
    (fun i hi => Or.inr (List.mem_append_right _ hi)) houtI hnd u
    ((huf.base_regs hds_digit).trans (by simp [setupResult, base, zero]))
    ((huf.zero_regs hds_digit).trans (by simp [setupResult]))
    (fun i hi => hui (List.mem_append_left _ hi) ▸ ha i hi)
    (fun i hi => hui (List.mem_append_right _ hi) ▸ hb i hi)
    (fun i hi => hu i hi ▸ Nat.zero_lt_of_lt (one_lt_radix hw))) with y ⟨hyb, hyval, hyf⟩
  rw [value_eq_zero_of_forall hu, zero_add,
    value_congr (β := radix w) fun i hi => hui (List.mem_append_left _ hi),
    value_congr (β := radix w) fun i hi => hui (List.mem_append_right _ hi)] at hyval
  exact ⟨by omega, hyb, hyval, hyf.1.trans huf.1, fun i hi =>
    (frame_input hyf hI (fun j hj => (houtI j hj).2) (Or.inr hi)).trans (hui hi)⟩

/-- A contiguous list of digit registers, after the four reserved workspace registers. -/
def registers (start len : ℕ) (h : start + len ≤ r) : List (Fin (r + 4)) :=
  List.ofFn fun i : Fin len => ⟨4 + start + i.val, by omega⟩

/-- Every register in `registers start len h` has physical index in
`[4 + start, 4 + start + len)`. -/
theorem registers_bounds {start len : ℕ} {h : start + len ≤ r}
    {i : Fin (r + 4)} (hi : i ∈ registers start len h) :
    4 + start ≤ i.val ∧ i.val < 4 + start + len := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  dsimp
  omega

/-- The contiguous register slice `registers start len h` has no duplicate registers. -/
theorem nodup_registers (start len : ℕ) (h : start + len ≤ r) :
    (registers start len h).Nodup :=
  List.nodup_ofFn_ofInjective fun _ _ hij =>
    Fin.ext (by simpa using congrArg Fin.val hij)

/-- The first operand occupies the first `m` digit registers. -/
def leftRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers 0 m (by omega)

/-- The second operand follows the first. -/
def rightRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers m n (by omega)

/-- The `m + n` result digits follow both operands. -/
def outputRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  registers (m + n) (n + m) (by omega)

/-- Initial zero accumulator, with the second operand's length. -/
def lowRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  (outputRegs m n).take n

/-- One fresh high digit for each schoolbook row. -/
def highRegs (m n : ℕ) : List (Fin (2 * (m + n) + 4)) :=
  (outputRegs m n).drop n

private theorem lengths (m n : ℕ) :
    (leftRegs m n).length = m ∧ (rightRegs m n).length = n ∧
      (lowRegs m n).length = n ∧ (highRegs m n).length = m := by
  simp [leftRegs, rightRegs, lowRegs, highRegs, outputRegs, registers]

private theorem output_split (m n : ℕ) :
    lowRegs m n ++ highRegs m n = outputRegs m n := List.take_append_drop _ _

private theorem layout (m n : ℕ) :
    (∀ i ∈ leftRegs m n ++ rightRegs m n, IsDigit i) ∧
      (∀ i ∈ lowRegs m n ++ highRegs m n, IsDigit i) ∧
      (lowRegs m n ++ highRegs m n).Nodup ∧
      List.Disjoint (lowRegs m n ++ highRegs m n) (leftRegs m n ++ rightRegs m n) := by
  have hin (i : Fin (2 * (m + n) + 4)) (hi : i ∈ leftRegs m n ++ rightRegs m n) :
      4 ≤ i.val ∧ i.val < 4 + m + n := by
    rcases List.mem_append.mp hi with hi | hi <;> have := registers_bounds hi <;> omega
  have hout (i : Fin (2 * (m + n) + 4)) (hi : i ∈ lowRegs m n ++ highRegs m n) :
      4 + m + n ≤ i.val := by
    rw [output_split] at hi
    have := registers_bounds hi
    omega
  refine ⟨fun i hi => (hin i hi).1, fun i hi => le_trans (by omega) (hout i hi),
    output_split m n ▸ nodup_registers _ _ _, List.disjoint_left.mpr fun i ho hi => ?_⟩
  have := hin i hi
  have := hout i ho
  omega

/-- A concrete schoolbook program with `2 * (m + n) + 4` registers and no address words.
The code and register count depend only on the limb counts, not on the physical word width. -/
def fixedProgram (m n : ℕ) : Code .standard (2 * (m + n) + 4) :=
  program (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)

/-- Exact code size of the fixed-register schoolbook multiplication program. -/
theorem size_fixedProgram (m n : ℕ) :
    (fixedProgram m n).size = 7 + n + rowCost m n := by
  obtain ⟨hl, hr, hd, ho⟩ := lengths m n
  simpa only [fixedProgram, hl, hr] using size_program
    (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)
    (hr.trans hd.symm) (ho.trans hl.symm)

/-- Closed form of the exact instruction count, including setup and initialization. -/
theorem size_fixedProgram_eq (m n : ℕ) :
    (fixedProgram m n).size = 5 * (m * n + m * (m - 1) / 2) + 3 * m + n + 8 := by
  rw [size_fixedProgram, rowCost_eq]
  omega

/-- The same constant bounds every choice of operand lengths up to eighteen digits. -/
theorem size_fixedProgram_le {m n : ℕ} (hm : m ≤ 18) (hn : n ≤ 18) :
    (fixedProgram m n).size ≤ 2465 := by
  have hmn : m * n ≤ 324 := Nat.mul_le_mul hm hn
  have hpred : m * (m - 1) ≤ 306 := Nat.mul_le_mul hm (show m - 1 ≤ 17 by omega)
  have hhalf : m * (m - 1) / 2 ≤ 153 := by omega
  rw [size_fixedProgram_eq]
  omega

/-- The concrete fixed-register schoolbook program multiplies all bounded operands, including
zero-length operands, at every physical width at least two. The output has `m + n` bounded
digits, reconstructs the exact product, and preserves memory and both operands. -/
theorem exec_fixedProgram {w : ℕ} (hw : 2 ≤ w) (m n : ℕ)
    (x : Data (2 * (m + n) + 4))
    (ha : Bounded (radix w) x (leftRegs m n))
    (hb : Bounded (radix w) x (rightRegs m n)) :
    ∃ y, Exec w (fixedProgram m n) x y (7 + n + rowCost m n) ∧
      Bounded (radix w) y (outputRegs m n) ∧
      value (radix w) y (outputRegs m n) =
        value (radix w) x (leftRegs m n) * value (radix w) x (rightRegs m n) ∧
      y.mem = x.mem ∧ ∀ i ∈ leftRegs m n ++ rightRegs m n, y.regs i = x.regs i := by
  obtain ⟨hl, hr, hd, ho⟩ := lengths m n
  obtain ⟨hi, hout, hnd, hdis⟩ := layout m n
  simpa only [fixedProgram, output_split, hl, hr] using exec hw
    (leftRegs m n) (rightRegs m n) (lowRegs m n) (highRegs m n)
    (hr.trans hd.symm) (ho.trans hl.symm) hi hout hnd hdis x ha hb

/-- Eighteen digits per operand give a fixed 76-register, 2465-instruction program.
This accommodates six physical words per operand even at odd widths, including width three. -/
theorem exec_eighteen {w : ℕ} (hw : 2 ≤ w) (x : Data 76)
    (ha : Bounded (radix w) x (leftRegs 18 18))
    (hb : Bounded (radix w) x (rightRegs 18 18)) :
    ∃ y, Exec w (fixedProgram 18 18) x y 2465 ∧
      Bounded (radix w) y (outputRegs 18 18) ∧
      value (radix w) y (outputRegs 18 18) =
        value (radix w) x (leftRegs 18 18) * value (radix w) x (rightRegs 18 18) ∧
      y.mem = x.mem ∧ ∀ i ∈ leftRegs 18 18 ++ rightRegs 18 18, y.regs i = x.regs i :=
  exec_fixedProgram hw 18 18 x ha hb

/-- Encode two fixed digit tuples into the concrete layout, with zero workspace and memory.
This is an input encoding, not a RAM conversion routine. -/
def input (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) : Data (2 * (m + n) + 4) :=
  ⟨fun i =>
    if h : 4 ≤ i.val ∧ i.val < 4 + m then a ⟨i.val - 4, by omega⟩
    else if h : 4 + m ≤ i.val ∧ i.val < 4 + m + n then
      b ⟨i.val - (4 + m), by omega⟩
    else 0, fun _ => 0⟩

private theorem input_left (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) (i : Fin m) :
    (input m n a b).regs ⟨4 + i.val, by omega⟩ = a i := by
  simp [input, i.isLt]

private theorem input_right (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) (i : Fin n) :
    (input m n a b).regs ⟨4 + m + i.val, by omega⟩ = b i := by
  have hy : 4 + m ≤ 4 + m + i.val ∧ 4 + m + i.val < 4 + m + n := by omega
  simp [input, hy]

private theorem value_input_left (β m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) :
    value β (input m n a b) (leftRegs m n) = Nat.ofDigits β (List.ofFn a) := by
  simp [value, leftRegs, registers, Function.comp_def, input_left]

private theorem value_input_right (β m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) :
    value β (input m n a b) (rightRegs m n) = Nat.ofDigits β (List.ofFn b) := by
  simp [value, rightRegs, registers, Function.comp_def, input_right]

private theorem bounded_input_left {β : ℕ} (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i < β) : Bounded β (input m n a b) (leftRegs m n) := by
  intro j hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  rw [input_left]
  exact ha i

private theorem bounded_input_right {β : ℕ} (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hb : ∀ i, b i < β) : Bounded β (input m n a b) (rightRegs m n) := by
  intro j hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  rw [input_right]
  exact hb i

/-- Bounded digit tuples encode globally bounded RAM data. -/
private theorem input_bounded {w : ℕ} (hw : 2 ≤ w) (m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i < radix w) (hb : ∀ i, b i < radix w) :
    (input m n a b).Bounded w := by
  refine ⟨fun i => ?_, fun _ => fits_zero _⟩
  dsimp [input]
  split
  · exact (ha _).trans (radix_fits hw)
  · split
    · exact (hb _).trans (radix_fits hw)
    · exact fits_zero _

/-- Any two values smaller than six physical words have a globally bounded digit encoding
on which the concrete checked program computes their full product in 2465 instructions.
The encoding is specified separately; the runtime starts with the encoded operands. -/
theorem six_word_product {w a b : ℕ} (hw : 2 ≤ w)
    (ha : a < 2 ^ (6 * w)) (hb : b < 2 ^ (6 * w)) :
    ∃ x y : Data 76, x.Bounded w ∧ y.Bounded w ∧
      Exec w (fixedProgram 18 18) x y 2465 ∧
      value (radix w) x (leftRegs 18 18) = a ∧
      value (radix w) x (rightRegs 18 18) = b ∧
      Bounded (radix w) y (outputRegs 18 18) ∧
      value (radix w) y (outputRegs 18 18) = a * b := by
  obtain ⟨as, has, hvalas⟩ := exists_six_word_digits hw ha
  obtain ⟨bs, hbs, hvalbs⟩ := exists_six_word_digits hw hb
  let x := input 18 18 as bs
  have hx := input_bounded hw 18 18 as bs has hbs
  obtain ⟨y, he, hyb, hyval, _⟩ := exec_eighteen hw x
    (bounded_input_left 18 18 as bs has) (bounded_input_right 18 18 as bs hbs)
  have hxa : value (radix w) x (leftRegs 18 18) = a :=
    (value_input_left _ _ _ _ _).trans hvalas
  have hxb : value (radix w) x (rightRegs 18 18) = b :=
    (value_input_right _ _ _ _ _).trans hvalbs
  exact ⟨x, y, hx, he.bounded hx, he, hxa, hxb, hyb, by rwa [hxa, hxb] at hyval⟩

end Cslib.WordRAM.Multiword.Schoolbook

end
