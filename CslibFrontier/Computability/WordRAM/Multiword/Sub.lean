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
# Checked multiword subtraction

Digits use the half-word radix `β = 2 ^ (w / 2)`. A subtraction cell computes
`t = β + a - b - c`, then returns `t % β` and borrow `1 - t / β`.
For digits `a, b < β` and incoming borrow `c ≤ 1`, all intermediate values fit
the physical word, even at width two. In particular, no modular overflow is used.

## Main definitions

* `Difference.borrow`, `Difference.one`: reserved borrow and constant-one workspace registers
  (sharing `Workspace.total`, `Workspace.base`, `Workspace.IsDigit`, and `Workspace.Frame`).
* `Difference.cell`, `Difference.cellResult`: six standard instructions for a digit and
  outgoing borrow, and their mathematical state update.
* `Difference.digits`, `Difference.program`: unrolled digit cells and the fixed-length,
  in-place multiword difference routine.

## Main results

* `Difference.exec_cell`: checked execution and the exact borrow equation.
* `Difference.exec`: execution and reconstruction of a nonnegative difference.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Difference

open Workspace

variable {r : ℕ}

/-- Incoming and outgoing borrow, reusing workspace register 1 (`Workspace.carry`). -/
abbrev borrow : Fin (r + 4) := carry
/-- Preserved one, reusing workspace register 3 (`Workspace.zero`, which holds `0` in addition
and `1` in subtraction). -/
abbrev one : Fin (r + 4) := zero

/-- Subtract one digit and the incoming borrow, replacing the minuend digit. -/
def cell (b d : Fin (r + 4)) : Code .standard (r + 4) := ram[
  total ← base + d;
  total ← total - b;
  total ← total - borrow;
  d ← total % base;
  borrow ← total / base;
  borrow ← one - borrow ]

/-- Exact result, including arithmetic workspace. -/
def cellResult (x : Data (r + 4)) (b d : Fin (r + 4)) : Data (r + 4) :=
  let t := x.regs base + x.regs d - x.regs b - x.regs borrow
  ((x.set total t).set d (t % x.regs base)).set borrow (1 - t / x.regs base)

/-- Every cell uses six instructions, with a zero-or-one outgoing borrow and exact
reconstruction. The equality accounts for the borrow at both ends. -/
theorem exec_cell {w : ℕ} (hw : 2 ≤ w) (x : Data (r + 4))
    (b d : Fin (r + 4)) (hb : IsDigit b) (hd : IsDigit d)
    (hbase : x.regs base = radix w) (hone : x.regs one = 1)
    (hxb : x.regs b < radix w) (hxd : x.regs d < radix w)
    (hc : x.regs borrow ≤ 1) :
    Exec w (cell b d) x (cellResult x b d) 6 ∧
      (cellResult x b d).regs d < radix w ∧
      (cellResult x b d).regs borrow ≤ 1 ∧
      (cellResult x b d).regs d + x.regs b + x.regs borrow =
        x.regs d + radix w * (cellResult x b d).regs borrow ∧
      Frame x (cellResult x b d) [d] := by
  obtain ⟨hbt, hbc, hbb, hbo⟩ := digit_ne hb
  obtain ⟨hdt, hdc, hdb, hdo⟩ := digit_ne hd
  let t := radix w + x.regs d - x.regs b - x.regs borrow
  have hβ : 1 < radix w := one_lt_radix hw
  have h1 := fits_one (w := w) (by omega)
  have hsum : Fits w (radix w + x.regs d) := by
    have hs := radix_sq_le w; unfold Fits; nlinarith
  have hquot : t / radix w ≤ 1 :=
    Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by dsimp only [t]; omega))
  have heq : t + x.regs b + x.regs borrow = radix w + x.regs d := by dsimp only [t]; omega
  refine ⟨WP.Exact.exec ?_, ?_, ?_, ?_, rfl, fun i hi _ _ => by
    simp only [List.mem_singleton] at hi; unfold cellResult; wram_simp⟩
  · unfold cell cellResult
    wram_exec [hbase, hone, hsum]
    · simp only [Data.set, Function.update_idem, hbase]
    · exact h1.of_le (Nat.sub_le 1 _)
  · unfold cellResult; wram_simp [hbase]
    exact Nat.mod_lt t (by omega)
  · unfold cellResult; wram_simp
    exact Nat.sub_le 1 _
  · unfold cellResult; wram_simp [hbase]
    have hm' := Nat.mod_add_div t (radix w)
    have hmul : radix w * (1 - t / radix w) + radix w * (t / radix w) = radix w := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hquot, mul_one]
    change t % radix w + x.regs b + x.regs borrow = x.regs d + radix w * (1 - t / radix w)
    omega

/-- Unroll the digit cells. The final self-copy also handles an empty list. -/
def digits : List (Fin (r + 4)) → List (Fin (r + 4)) → Code .standard (r + 4)
  | b :: bs, d :: ds => .seq (cell b d) (digits bs ds)
  | _, _ => .op (.copy borrow borrow)

/-- Unrolling `ds.length` subtraction cells takes `6 * ds.length + 1` instructions. -/
theorem size_digits (bs ds : List (Fin (r + 4))) (hlen : bs.length = ds.length) :
    (digits bs ds).size = 6 * ds.length + 1 := by
  induction bs generalizing ds with
  | nil => cases ds <;> simp_all [digits]
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [digits, Code.size, cell, ih ds hlen, List.length_cons]
      omega

/-- Execute an entire subtraction, retaining a possible final borrow. Source digits and
all registers outside the destinations and arithmetic workspaces are preserved. -/
theorem exec_digits {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4)) (hbase : x.regs base = radix w) (hone : x.regs one = 1)
    (hb : Bounded (radix w) x bs) (hd : Bounded (radix w) x ds)
    (hc : x.regs borrow ≤ 1) :
    ∃ y, Exec w (digits bs ds) x y (6 * ds.length + 1) ∧
      Bounded (radix w) y ds ∧ y.regs borrow ≤ 1 ∧
      value (radix w) y ds + value (radix w) x bs + x.regs borrow =
        value (radix w) x ds + radix w ^ ds.length * y.regs borrow ∧
      Frame x y ds := by
  induction bs generalizing ds x with
  | nil =>
    cases ds with
    | nil =>
      refine WP.Exact.exists_exec ?_
      wram_exec [digits, List.length_nil]
      exact ⟨by simp [Bounded], by wram_simp [hc], by simp [value], frame_set_carry _ _ []⟩
    | cons => simp_all
  | cons b bs ih =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hd0 := hds d List.mem_cons_self
      have hbs' : ∀ i ∈ bs, IsDigit i := fun i hi => hbs i (List.mem_cons_of_mem b hi)
      have hds' : ∀ i ∈ ds, IsDigit i := fun i hi => hds i (List.mem_cons_of_mem d hi)
      have hdnot : d ∉ ds := (List.nodup_cons.mp hnd).1
      have hdis_b : ∀ i ∈ bs, i ∉ [d] := fun _ hi hm =>
        List.disjoint_left.mp hdis (List.mem_cons_of_mem b hi)
          (List.mem_singleton.mp hm ▸ List.mem_cons_self)
      have hdis_d : ∀ i ∈ ds, i ∉ [d] := fun _ hi hm => hdnot (List.mem_singleton.mp hm ▸ hi)
      refine WP.Exact.exists_exec ?_
      unfold digits
      wram_call (exec_cell hw x b d (hbs b List.mem_cons_self) hd0 hbase hone
        (hb b List.mem_cons_self) (hd d List.mem_cons_self) hc) with ⟨hzd, hzc, hzeq, hzf⟩
      wram_call (ih ds (by simpa using hlen) hbs' hds' (List.nodup_cons.mp hnd).2
        (List.disjoint_left.mpr fun i hi hj =>
          List.disjoint_left.mp hdis (List.mem_cons_of_mem b hi) (List.mem_cons_of_mem d hj))
        _ ((hzf.base_regs (by simpa using hd0)).trans hbase)
        ((hzf.zero_regs (by simpa using hd0)).trans hone)
        (hzf.bounded_of_digits hbs' hdis_b fun i hi => hb i (List.mem_cons_of_mem b hi))
        (hzf.bounded_of_digits hds' hdis_d fun i hi => hd i (List.mem_cons_of_mem d hi)) hzc)
        with y ⟨hyd, hyc, hyeq, hyf⟩
      obtain ⟨hyd0, hvalds, hyb, hyframe⟩ := hzf.cons_step hyf hd0 hds' hdnot hzd hyd
      rw [hzf.value_eq_of_digits hbs' hdis_b, hvalds] at hyeq
      refine ⟨by simp only [List.length_cons]; omega, hyb, hyc, ?_, hyframe⟩
      rw [value_cons, value_cons, value_cons, hyd0, List.length_cons, pow_succ]
      linarith [congrArg (radix w * ·) hyeq]

/-- Width-only constants, followed by a zero incoming borrow and the unrolled cells. -/
def program (w : ℕ) (bs ds : List (Fin (r + 4))) : Code .standard (r + 4) :=
  .seq (ram[base ← #(radix w); one ← #1; borrow ← #0]) (digits bs ds)

/-- Exact instruction count of `program`, including the three constant-setup instructions. -/
theorem size_program (w : ℕ) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) : (program w bs ds).size = 6 * ds.length + 4 := by
  simp only [program, Code.size, size_digits bs ds hlen]
  omega

/-- Only destinations and the four named workspace registers are written. -/
theorem preserves_program (w : ℕ) (bs ds : List (Fin (r + 4)))
    (i : Fin (r + 4)) (hi : IsDigit i) (hid : i ∉ ds) :
    (program w bs ds).Preserves i := by
  obtain ⟨ht, hc, hb, ho⟩ := digit_ne hi
  have hcell (b d : Fin (r + 4)) (hd : d ≠ i) : (cell b d).Preserves i := by
    simp only [cell, Code.Preserves, Op.dest_bin, ne_eq, Option.some.injEq]
    exact ⟨Ne.symm ht, Ne.symm ht, Ne.symm ht, hd, Ne.symm hc, Ne.symm hc⟩
  have hds : (digits bs ds).Preserves i := by
    induction bs generalizing ds with
    | nil => simpa only [digits, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        using Ne.symm hc
    | cons b bs ih =>
      cases ds with
      | nil => simpa only [digits, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
          using Ne.symm hc
      | cons d ds =>
        exact ⟨hcell b d (fun he => hid (by simp [he])),
          ih ds (fun hm => hid (by simp [hm]))⟩
  refine ⟨?_, hds⟩
  simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
  exact ⟨Ne.symm hb, Ne.symm ho, Ne.symm hc⟩

/-- Nonnegative multiword subtraction, with charged constant installation and no preloaded
radix or borrow. The running time depends only on the number of digits. -/
theorem exec {w : ℕ} (hw : 2 ≤ w) (bs ds : List (Fin (r + 4)))
    (hlen : bs.length = ds.length) (hbs : ∀ b ∈ bs, IsDigit b)
    (hds : ∀ d ∈ ds, IsDigit d) (hnd : ds.Nodup) (hdis : List.Disjoint bs ds)
    (x : Data (r + 4)) (hb : Bounded (radix w) x bs) (hd : Bounded (radix w) x ds)
    (hle : value (radix w) x bs ≤ value (radix w) x ds) :
    ∃ y, Exec w (program w bs ds) x y (6 * ds.length + 4) ∧
      Bounded (radix w) y ds ∧ y.regs borrow = 0 ∧
      value (radix w) y ds = value (radix w) x ds - value (radix w) x bs ∧
      y.mem = x.mem ∧ ∀ i ∈ bs, y.regs i = x.regs i := by
  have hβ := one_lt_radix hw
  refine WP.Exact.exists_exec ?_
  wram_exec [program, radix_fits hw]
  refine WP.Exact.name fun z hzx => ?_
  have hz (i : Fin (r + 4)) (hi : IsDigit i) : z.regs i = x.regs i := by
    obtain ⟨_, hc, hb, ho⟩ := digit_ne hi
    rw [hzx]; wram_simp
  wram_call (exec_digits hw bs ds hlen hbs hds hnd hdis z
    (by rw [hzx]; wram_simp) (by rw [hzx]; wram_simp)
    (fun i hi => hz i (hbs i hi) ▸ hb i hi)
    (fun i hi => hz i (hds i hi) ▸ hd i hi) (by rw [hzx]; wram_simp))
    with y ⟨hyd, hyc, hyeq, hyf⟩
  have hzbor : z.regs borrow = 0 := by rw [hzx]; wram_simp
  rw [value_congr (β := radix w) fun i hi => hz i (hbs i hi),
    value_congr (β := radix w) fun i hi => hz i (hds i hi), hzbor, Nat.add_zero] at hyeq
  have hzero : y.regs borrow = 0 := by
    by_contra hn
    have hh : y.regs borrow = 1 := by omega
    have hyv : value (radix w) y ds < radix w ^ ds.length :=
      (Nat.ofDigits_lt_base_pow_length hβ fun a ha => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hyd i hi).trans_eq (by simp)
    rw [hh, Nat.mul_one] at hyeq
    omega
  refine ⟨trivial, hyd, hzero, ?_, by rw [hyf.1, hzx]; rfl, fun i hi =>
    (hyf.digit_regs (hbs i hi) fun him => List.disjoint_left.mp hdis hi him).trans
      (hz i (hbs i hi))⟩
  simp only [hzero, Nat.mul_zero, Nat.add_zero] at hyeq
  omega

end Cslib.WordRAM.Multiword.Difference
