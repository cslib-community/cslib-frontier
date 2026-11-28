/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Mul
public import CslibFrontier.Computability.WordRAM.Multiword.Sub
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.FinIndex

/-!
# Framed checked multiword arithmetic

The arithmetic programs reserve registers zero through three for workspace. Their frame
preserves memory and every other register outside the destination list, including registers
that are not source operands. Register lists are fixed when constructing the code.

## Main definitions

* `Arithmetic.Frame`: preservation of all digit registers outside a destination list.
* `Difference.truncatingProgram`: subtraction with a branch that clears an underflowed result.

## Main results

* `Schoolbook.preserves_program`: the syntactic register frame for schoolbook multiplication.
* `Schoolbook.exec_framed`: full multiplication with the digit-register frame.
* `Schoolbook.exec_eighteen_framed`: arbitrary layouts of eighteen-digit operands and a
  thirty-six-digit product, in exactly 2465 instructions.
* `Difference.exec_framed`: nonnegative subtraction with the digit-register frame.
* `Difference.exec_eighteen_framed`: eighteen-digit nonnegative subtraction in exactly
  112 instructions.
* `Difference.exec_eighteen_truncating`: general eighteen-digit natural-number subtraction
  in at most 132 instructions, with the full digit-register frame.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword

variable {r : ℕ}

namespace Arithmetic

/-- Arithmetic preserves memory and all registers outside the destinations and the four
reserved workspace registers. -/
def Frame (x y : Data (r + 4)) (ds : List (Fin (r + 4))) : Prop :=
  y.mem = x.mem ∧ ∀ i, 4 ≤ i.val → i ∉ ds → y.regs i = x.regs i

end Arithmetic

namespace Schoolbook

/-- A multiplication cell writes only its output digit and arithmetic workspace. -/
private theorem preserves_cell (a b d i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ≠ d) :
    (cell a b d).Preserves i := by
  obtain ⟨ht, hc, _, _⟩ := Workspace.digit_ne hi
  simp only [cell, Code.Preserves, Op.dest_bin, ne_eq, Option.some.injEq]
  exact ⟨Ne.symm ht, Ne.symm ht, Ne.symm ht, Ne.symm hid, Ne.symm hc⟩

/-- Every digit register outside a row's destinations is syntactically preserved. -/
private theorem preserves_row (a : Fin (r + 4)) : (bs ds : List (Fin (r + 4))) →
    (i : Fin (r + 4)) → Workspace.IsDigit i → i ∉ ds → (row a bs ds).Preserves i
  | [], _, _, hi, _ | _ :: _, [], _, hi, _ =>
    by simpa only [row, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
      Ne.symm (Workspace.digit_ne hi).2.1
  | b :: bs, d :: ds, i, hi, hid =>
    ⟨preserves_cell a b d i hi (fun he => hid (by simp [he])),
      preserves_row a bs ds i hi (fun hm => hid (by simp [hm]))⟩

/-- Every digit register outside all row destinations is syntactically preserved. -/
private theorem preserves_rows : (as bs ds os : List (Fin (r + 4))) →
    (i : Fin (r + 4)) → Workspace.IsDigit i → i ∉ ds ++ os → (rows as bs ds os).Preserves i
  | [], _, _, _, _, hi, _ | _ :: _, _, _, [], _, hi, _ =>
    by simpa only [rows, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
      Ne.symm (Workspace.digit_ne hi).2.1
  | a :: as, bs, ds, d :: os, i, hi, hid => by
    simp only [rows, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    refine ⟨Ne.symm (Workspace.digit_ne hi).2.1,
      preserves_row a bs ds i hi (fun hm => hid (by simp [hm])),
      by simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
        (show d ≠ i from fun he => hid (by simp [he])),
      preserves_rows as (Workspace.zero :: bs) (ds ++ [d]) os i hi ?_⟩
    exact fun hm => hid (by
      simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] using hm)

/-- Clearing an accumulator preserves every digit register outside it. -/
private theorem preserves_clear : (ds : List (Fin (r + 4))) →
    (i : Fin (r + 4)) → Workspace.IsDigit i → i ∉ ds → (clear ds).Preserves i
  | [], _, hi, _ =>
    by simpa only [clear, Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
      Ne.symm (Workspace.digit_ne hi).2.1
  | d :: ds, i, hi, hid =>
    ⟨by simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using
        (show d ≠ i from fun he => hid (by simp [he])),
      preserves_clear ds i hi (fun hm => hid (by simp [hm]))⟩

/-- Radix initialization writes only the four reserved workspace registers. -/
private theorem preserves_setup (i : Fin (r + 4)) (hi : Workspace.IsDigit i) :
    (Workspace.setup (r := r)).Preserves i := by
  obtain ⟨ht, hc, hb, hz⟩ := Workspace.digit_ne hi
  simp only [Workspace.setup, Code.Preserves, Op.width, Op.bin, Op.dest,
    ne_eq, Option.some.injEq]
  exact ⟨Ne.symm ht, Ne.symm hc, Ne.symm hb, Ne.symm hc, Ne.symm hb, Ne.symm hz⟩

/-- Multiplication writes only destination digits and the four reserved workspace registers. -/
theorem preserves_program (as bs ds os : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : Workspace.IsDigit i) (hid : i ∉ ds ++ os) :
    (program as bs ds os).Preserves i :=
  ⟨preserves_setup i hi, preserves_clear ds i hi (fun hm => hid (by simp [hm])),
    preserves_rows as bs ds os i hi hid⟩

/-- Full multiplication preserves every non-destination digit register. The destination lists
and operands have arbitrary fixed lengths and arbitrary disjoint register layouts. -/
theorem exec_framed {w : ℕ} (hw : 2 ≤ w) (as bs ds os : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hos : os.length = as.length)
    (hin : ∀ i ∈ as ++ bs, Workspace.IsDigit i) (hout : ∀ i ∈ ds ++ os, Workspace.IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4))
    (ha : Multiword.Bounded (radix w) x as) (hb : Multiword.Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y
        (7 + bs.length + rowCost as.length bs.length) ∧
      Multiword.Bounded (radix w) y (ds ++ os) ∧
      Multiword.value (radix w) y (ds ++ os) =
        Multiword.value (radix w) x as * Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y (ds ++ os) := by
  obtain ⟨y, he, hy, hv, hm, _⟩ := exec hw as bs ds os hlen hos hin hout hnd hdis x ha hb
  exact ⟨y, he, hy, hv, hm, fun i hi hid =>
    he.regs_eq (preserves_program as bs ds os i hi hid)⟩

/-- An arbitrary eighteen-digit layout computes all thirty-six product digits in 2465
instructions while preserving every other digit register and memory. -/
theorem exec_eighteen_framed {w : ℕ} (hw : 2 ≤ w)
    (as bs ds os : List (Fin (r + 4)))
    (has : as.length = 18) (hbs : bs.length = 18)
    (hds : ds.length = 18) (hos : os.length = 18)
    (hin : ∀ i ∈ as ++ bs, Workspace.IsDigit i) (hout : ∀ i ∈ ds ++ os, Workspace.IsDigit i)
    (hnd : (ds ++ os).Nodup) (hdis : List.Disjoint (ds ++ os) (as ++ bs))
    (x : Data (r + 4))
    (ha : Multiword.Bounded (radix w) x as) (hb : Multiword.Bounded (radix w) x bs) :
    ∃ y, Exec w (program as bs ds os) x y 2465 ∧
      Multiword.Bounded (radix w) y (ds ++ os) ∧
      Multiword.value (radix w) y (ds ++ os) =
        Multiword.value (radix w) x as * Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y (ds ++ os) := by
  simpa only [has, hbs, rowCost] using
    exec_framed hw as bs ds os (hbs.trans hds.symm) (hos.trans has.symm)
      hin hout hnd hdis x ha hb

end Schoolbook

namespace Difference

open Workspace

/-- Subtraction without a sign hypothesis, retaining the exact final borrow equation.
This is the arithmetic core used before clearing a negative result. -/
private theorem exec_borrow_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow ≤ 1 ∧ y.regs one = 1 ∧
      Multiword.value (radix w) y ds + Multiword.value (radix w) x bs =
        Multiword.value (radix w) x ds + radix w ^ ds.length * y.regs borrow ∧
      Arithmetic.Frame x y ds := by
  refine WP.Exact.exists_exec ?_
  unfold program
  wram_exec [radix_fits hw]
  refine WP.Exact.name fun z hzx => ?_
  have hz (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    obtain ⟨_, hc, hb, ho⟩ := digit_ne hi
    rw [hzx]; wram_simp
  obtain ⟨y, he, hyd, hyc, hyeq, hyf⟩ := exec_digits hw bs ds hlen hbs hds hnd hdis z
    (by rw [hzx]; wram_simp) (by rw [hzx]; wram_simp)
    (fun i hi => hz i (hbs i hi) ▸ hb i hi)
    (fun i hi => hz i (hds i hi) ▸ hd i hi) (by rw [hzx]; wram_simp)
  have hzbor : z.regs borrow = 0 := by rw [hzx]; wram_simp
  refine WP.Exact.of_exec he ⟨rfl, hyd, hyc,
    (hyf.zero_regs hds).trans (by rw [hzx]; wram_simp), ?_,
    by rw [hyf.1, hzx]; rfl, fun i hi hid => (hyf.digit_regs hi hid).trans (hz i hi)⟩
  simpa only [Multiword.value_congr (β := radix w) fun i hi => hz i (hbs i hi),
    Multiword.value_congr (β := radix w) fun i hi => hz i (hds i hi), hzbor, Nat.add_zero]
    using hyeq

/-- Subtraction followed by clearing its output exactly when the final borrow is one.
The second alternative is a self-copy, so both branches are executable for empty lists. -/
def truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (program w bs ds)
    (.branch (.eq borrow one) (Schoolbook.clear ds) (.op (.copy borrow borrow)))

/-- Truncating subtraction writes only its destinations and reserved workspace. -/
theorem preserves_truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ∉ ds) :
    (truncatingProgram w bs ds).Preserves i := by
  refine ⟨preserves_program w bs ds i hi hid, Schoolbook.preserves_clear ds i hi hid, ?_⟩
  have hc : i ≠ borrow := by
    fin_index [IsDigit]
  simpa only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq] using Ne.symm hc

/-- Exact static size of truncating subtraction, including both branch bodies. -/
theorem size_truncatingProgram (w : ℕ) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) :
    (truncatingProgram w bs ds).size = 7 * ds.length + 8 := by
  simp only [truncatingProgram, Code.size, size_program w bs ds hlen, Schoolbook.size_clear]
  omega

/-- General natural-number subtraction, including underflow. The result is `Nat.sub`,
with bounded digits and preservation of every non-destination digit register and memory.
The clear branch costs `ds.length + 2`; the other branch costs three instructions. -/
theorem exec_truncating {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, ExecWithin w (truncatingProgram w bs ds) x y
        (6 * ds.length + 4 + max (ds.length + 2) 3) ∧
      Multiword.Bounded (radix w) y ds ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  obtain ⟨z, he, hzd, hzc, hzo, hzeq, hzf⟩ :=
    exec_borrow_framed hw bs ds hlen hbs hds hnd hdis x hb hd
  refine WP.exists_execWithin ?_
  unfold truncatingProgram
  refine WP.seq (WP.of_execWithin he.within ?_)
  wram_exec [hzo]
  case pos =>
    obtain ⟨y, hey, hy, hyf⟩ := Schoolbook.exec_clear (w := w) ds hds hnd z
    have hlt : Multiword.value (radix w) x ds < Multiword.value (radix w) x bs := by
      have hyv : Multiword.value (radix w) z ds < radix w ^ ds.length :=
        (Nat.ofDigits_lt_base_pow_length (one_lt_radix hw) fun a ha => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hzd i hi).trans_eq (by simp)
      rw [hc, Nat.mul_one] at hzeq; omega
    exact WP.of_execWithin hey.within ⟨by omega,
      fun i hi => hy i hi ▸ Nat.zero_lt_of_lt (one_lt_radix hw),
      (Multiword.value_eq_zero_of_forall hy).trans (Nat.sub_eq_zero_of_le hlt.le).symm,
      hyf.1.trans hzf.1, fun i hi hid => (hyf.digit_regs hi hid).trans (hzf.2 i hi hid)⟩
  case neg =>
    have hc0 : z.regs borrow = 0 := by omega
    have hyi (i : Fin (r + 4)) : (z.set borrow (z.regs borrow)).regs i = z.regs i := by simp
    refine ⟨fun i hi => hyi i ▸ hzd i hi, ?_, hzf.1,
      fun i hi hid => (hyi i).trans (hzf.2 i hi hid)⟩
    rw [Multiword.value_congr fun i _ => hyi i]
    simp only [hc0, Nat.mul_zero, Nat.add_zero] at hzeq
    omega

/-- General eighteen-digit natural-number subtraction takes at most 132 instructions. -/
theorem exec_eighteen_truncating {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hbslen : bs.length = 18) (hdslen : ds.length = 18)
    (hbs : ∀ b ∈ bs, IsDigit b) (hds : ∀ d ∈ ds, IsDigit d)
    (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds) :
    ∃ y, ExecWithin w (truncatingProgram w bs ds) x y 132 ∧
      Multiword.Bounded (radix w) y ds ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  simpa [hdslen, max_def] using
    exec_truncating hw bs ds (hbslen.trans hdslen.symm) hbs hds hnd hdis x hb hd

/-- Nonnegative subtraction preserves every digit register outside its in-place output. -/
theorem exec_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds)
    (hle : Multiword.value (radix w) x bs ≤ Multiword.value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  obtain ⟨y, he, hy, hc, hv, hm, _⟩ := exec hw bs ds hlen hbs hds hnd hdis x hb hd hle
  exact ⟨y, he, hy, hc, hv, hm, fun i hi hid =>
    he.regs_eq (preserves_program w bs ds i hi hid)⟩

/-- Eighteen-digit nonnegative subtraction has an exact 112-instruction execution and
preserves memory and every digit register outside the in-place destination list. -/
theorem exec_eighteen_framed {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hbslen : bs.length = 18) (hdslen : ds.length = 18)
    (hbs : ∀ b ∈ bs, IsDigit b) (hds : ∀ d ∈ ds, IsDigit d)
    (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4))
    (hb : Multiword.Bounded (radix w) x bs) (hd : Multiword.Bounded (radix w) x ds)
    (hle : Multiword.value (radix w) x bs ≤ Multiword.value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y 112 ∧
      Multiword.Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      Multiword.value (radix w) y ds =
        Multiword.value (radix w) x ds - Multiword.value (radix w) x bs ∧
      Arithmetic.Frame x y ds := by
  simpa only [hdslen, Nat.reduceMul, Nat.reduceAdd] using
    exec_framed hw bs ds (hbslen.trans hdslen.symm) hbs hds hnd hdis x hb hd hle

end Difference

end Cslib.WordRAM.Multiword
