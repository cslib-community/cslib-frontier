/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.Schoening.Scan
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# A multiword counter on the word RAM

Schöning's algorithm runs about `(4 / 3) ^ n` trials for `3`-SAT, a number of `0.415 n` bits,
which does not fit a word of `O(log n)` bits. This module stores such a number in memory as its
little-endian binary digits, one digit per word, and provides the three routines the amplified
algorithm needs (`Cslib.Algorithms.WordRAM.Schoening.ampProgram`):

* `Cslib.Algorithms.WordRAM.Schoening.mulAdd` replaces the number `v` by `v a + c` for words `a`
  and `c`, appending digits as needed;
* `Cslib.Algorithms.WordRAM.Schoening.divFloor` replaces `v` by `⌊v / d⌋` for a word `d`;
* `Cslib.Algorithms.WordRAM.Schoening.decCounter` decrements a nonzero number and reports whether
  it was nonzero.

Each routine is specified against a function on digit lists (`mulAddDigits`, `divDigits`,
`decDigits`), whose value under `Nat.ofDigits 2` is proved separately. A multiply-add or a division
takes time linear in the number of digits. A decrement stops at the lowest nonzero digit, so it
takes `decSteps ds` iterations, and `decSteps_add_count_le` bounds this by the number of zero
digits it consumes, which gives the amortized constant cost per decrement used by the amplified
algorithm.

The routines use registers of the register file of Schöning's algorithm
(`Cslib.Algorithms.WordRAM.Schoening.Reg`). Those beyond the trial's own (`bBase`, `bLen`, `flag`)
keep the counter between trials; the others share registers with the scan, which are dead between
trials.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.mulAddPass`,
  `Cslib.Algorithms.WordRAM.Schoening.mulAddDigits`: multiply-add on digit lists.
* `Cslib.Algorithms.WordRAM.Schoening.divDigits`: division with remainder on digit lists.
* `Cslib.Algorithms.WordRAM.Schoening.decDigits`, `Cslib.Algorithms.WordRAM.Schoening.decSteps`:
  decrement on digit lists and its number of loop iterations.
* `Cslib.Algorithms.WordRAM.Schoening.mulAdd`, `Cslib.Algorithms.WordRAM.Schoening.divFloor`,
  `Cslib.Algorithms.WordRAM.Schoening.decCounter`: the routines.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.ofDigits_mulAddDigits`,
  `Cslib.Algorithms.WordRAM.Schoening.ofDigits_divDigits_zero`,
  `Cslib.Algorithms.WordRAM.Schoening.ofDigits_decDigits`: the values computed.
* `Cslib.Algorithms.WordRAM.Schoening.decSteps_add_count_le`: the amortized cost of a decrement.
* `Cslib.Algorithms.WordRAM.Schoening.mulAdd_spec`,
  `Cslib.Algorithms.WordRAM.Schoening.divFloor_spec`,
  `Cslib.Algorithms.WordRAM.Schoening.decCounter_spec`: the routines compute these functions within
  explicit instruction bounds and keep the memory below the counter.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block

/-! ### Digit lists -/

/-- The multiply-add pass over the little-endian binary digits `ds` with multiplier `a` and carry
`cy`: one new digit per old digit, and the final carry. -/
def mulAddPass (a : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | cy, [] => ([], cy)
  | cy, d :: ds =>
    ((d * a + cy) % 2 :: (mulAddPass a ((d * a + cy) / 2) ds).1,
      (mulAddPass a ((d * a + cy) / 2) ds).2)

/-- The binary digits of `v a + cy`, where `ds` are the digits of `v`: the pass, then the digits of
the final carry. -/
def mulAddDigits (a cy : ℕ) (ds : List ℕ) : List ℕ :=
  (mulAddPass a cy ds).1 ++ Nat.digits 2 (mulAddPass a cy ds).2

/-- Division by `d` of the number with digits `ds`, with `r` added at the top: the digits of the
quotient, one per digit, and the remainder. The high digits are divided first. -/
def divDigits (d : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | r, [] => ([], r)
  | r, b :: bs =>
    ((2 * (divDigits d r bs).2 + b) / d :: (divDigits d r bs).1,
      (2 * (divDigits d r bs).2 + b) % d)

/-- Decrement on binary digits: zeros below the lowest nonzero digit become ones, and that digit
becomes zero. A list of zeros becomes a list of ones. -/
def decDigits : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d = 0 then 1 :: decDigits ds else 0 :: ds

/-- The number of digits a decrement reads: up to and including the lowest nonzero digit. -/
def decSteps : List ℕ → ℕ
  | [] => 0
  | d :: ds => if d = 0 then decSteps ds + 1 else 1

@[simp]
theorem length_mulAddPass (a cy : ℕ) (ds : List ℕ) :
    (mulAddPass a cy ds).1.length = ds.length := by
  induction ds generalizing cy with
  | nil => rfl
  | cons d ds ih => simp [mulAddPass, ih]

/-- The pass computes `v a + cy`, split into its low digits and the final carry. -/
theorem ofDigits_mulAddPass (a cy : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (mulAddPass a cy ds).1 + 2 ^ ds.length * (mulAddPass a cy ds).2 =
      Nat.ofDigits 2 ds * a + cy := by
  induction ds generalizing cy with
  | nil => simp [mulAddPass]
  | cons d ds ih =>
    simp only [mulAddPass, Nat.ofDigits_cons, List.length_cons, pow_succ]
    have h := ih ((d * a + cy) / 2)
    have hm := Nat.mod_add_div (d * a + cy) 2
    linear_combination 2 * h + hm

/-- The carry of the pass stays below any bound on the multiplier and the initial carry. -/
theorem mulAddPass_carry_le {a cy B : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (ha : a ≤ B)
    (hc : cy ≤ B) : (mulAddPass a cy ds).2 ≤ B := by
  induction ds generalizing cy with
  | nil => exact hc
  | cons d ds ih =>
    have hd := hds d (by simp)
    have : d * a ≤ a := by nlinarith
    exact ih (fun d' hd' => hds d' (by simp [hd'])) (by omega)

/-- The digits of the pass are binary. -/
theorem mulAddPass_digit_le (a cy : ℕ) (ds : List ℕ) : ∀ d ∈ (mulAddPass a cy ds).1, d ≤ 1 := by
  induction ds generalizing cy with
  | nil => simp [mulAddPass]
  | cons d ds ih =>
    intro e he
    simp only [mulAddPass, List.mem_cons] at he
    exact he.elim (fun _ => by omega) (ih _ e)

/-- **The value of a multiply-add.** -/
theorem ofDigits_mulAddDigits (a cy : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (mulAddDigits a cy ds) = Nat.ofDigits 2 ds * a + cy := by
  rw [mulAddDigits, Nat.ofDigits_append, Nat.ofDigits_digits, length_mulAddPass,
    ofDigits_mulAddPass]

/-- The digits of a multiply-add are binary. -/
theorem mulAddDigits_digit_le (a cy : ℕ) (ds : List ℕ) : ∀ d ∈ mulAddDigits a cy ds, d ≤ 1 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact mulAddPass_digit_le a cy ds d hd
  · have := Nat.digits_lt_base (by decide) hd
    omega

/-- A multiply-add appends at most the number of digits of a bound on the multiplier and the
carry. -/
theorem length_mulAddDigits_le {a cy B : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (ha : a ≤ B)
    (hc : cy ≤ B) : (mulAddDigits a cy ds).length ≤ ds.length + (Nat.digits 2 B).length := by
  rw [mulAddDigits, List.length_append, length_mulAddPass]
  have := Nat.le_length_digits_le 2 _ _ (mulAddPass_carry_le hds ha hc)
  omega

/-- A multiply-add does not shorten the digit list. -/
theorem length_le_length_mulAddDigits (a cy : ℕ) (ds : List ℕ) :
    ds.length ≤ (mulAddDigits a cy ds).length := by
  simp [mulAddDigits]

@[simp]
theorem length_divDigits (d r : ℕ) (ds : List ℕ) : (divDigits d r ds).1.length = ds.length := by
  induction ds with
  | nil => rfl
  | cons b bs ih => simp [divDigits, ih]

/-- Dividing a list with one more digit on top: the top digit is divided first. -/
theorem divDigits_append_singleton (d r b : ℕ) (bs : List ℕ) :
    divDigits d r (bs ++ [b]) =
      ((divDigits d ((2 * r + b) % d) bs).1 ++ [(2 * r + b) / d],
        (divDigits d ((2 * r + b) % d) bs).2) := by
  induction bs with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, divDigits, ih]

/-- The remainder stays below the divisor. -/
theorem divDigits_rem_lt {d r : ℕ} (hd : 0 < d) (hr : r < d) (ds : List ℕ) :
    (divDigits d r ds).2 < d := by
  cases ds with
  | nil => exact hr
  | cons b bs => exact Nat.mod_lt _ hd

/-- The quotient digits are binary. -/
theorem divDigits_digit_le {d r : ℕ} (hd : 0 < d) (hr : r < d) {ds : List ℕ}
    (hds : ∀ b ∈ ds, b ≤ 1) : ∀ q ∈ (divDigits d r ds).1, q ≤ 1 := by
  induction ds with
  | nil => simp [divDigits]
  | cons b bs ih =>
    intro q hq
    simp only [divDigits, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have hb := hds b (by simp)
      have hrem : (divDigits d r bs).2 < d := divDigits_rem_lt hd hr bs
      rw [Nat.div_le_iff_le_mul_add_pred hd]
      omega
    · exact ih (fun b' hb' => hds b' (by simp [hb'])) q hq

/-- **Division with remainder.** -/
theorem ofDigits_divDigits (d r : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (divDigits d r ds).1 * d + (divDigits d r ds).2 =
      Nat.ofDigits 2 ds + r * 2 ^ ds.length := by
  induction ds with
  | nil => simp [divDigits]
  | cons b bs ih =>
    simp only [divDigits, Nat.ofDigits_cons, List.length_cons, pow_succ]
    have hm := Nat.div_add_mod (2 * (divDigits d r bs).2 + b) d
    linear_combination 2 * ih + hm

/-- **The value of a division** from remainder `0`: the floor of the quotient. -/
theorem ofDigits_divDigits_zero {d : ℕ} (hd : 0 < d) (ds : List ℕ) :
    Nat.ofDigits 2 (divDigits d 0 ds).1 = Nat.ofDigits 2 ds / d := by
  have h := ofDigits_divDigits d 0 ds
  have hr := divDigits_rem_lt hd hd ds
  rw [Nat.zero_mul, Nat.add_zero] at h
  rw [← h, Nat.mul_add_div_of_lt _ hr]

@[simp]
theorem length_decDigits (ds : List ℕ) : (decDigits ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => by_cases hd : d = 0 <;> simp [decDigits, hd, ih]

/-- A number is zero exactly when all its digits are. -/
theorem ofDigits_two_eq_zero_iff (ds : List ℕ) : Nat.ofDigits 2 ds = 0 ↔ ∀ d ∈ ds, d = 0 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, List.forall_mem_cons, ← ih]
    omega

/-- **The value of a decrement** of a nonzero number with binary digits. -/
theorem ofDigits_decDigits {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (hpos : 0 < Nat.ofDigits 2 ds) :
    Nat.ofDigits 2 (decDigits ds) + 1 = Nat.ofDigits 2 ds := by
  induction ds with
  | nil => simp at hpos
  | cons d ds ih =>
    have hd := hds d (by simp)
    rw [Nat.ofDigits_cons] at hpos ⊢
    by_cases h0 : d = 0
    · subst h0
      have := ih (fun d' hd' => hds d' (by simp [hd'])) (by omega)
      simp only [decDigits, ↓reduceIte, Nat.ofDigits_cons]
      omega
    · simp only [decDigits, h0, ↓reduceIte, Nat.ofDigits_cons]
      omega

/-- The digits of a decrement of binary digits are binary. -/
theorem decDigits_digit_le {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) : ∀ d ∈ decDigits ds, d ≤ 1 := by
  induction ds with
  | nil => simp [decDigits]
  | cons d ds ih =>
    intro e he
    by_cases h0 : d = 0 <;> simp only [decDigits, h0, ↓reduceIte, List.mem_cons] at he
    · exact he.elim Nat.le_of_eq (ih (fun d' hd' => hds d' (List.mem_cons_of_mem d hd')) e)
    · exact he.elim (· ▸ Nat.zero_le 1) fun h => hds e (List.mem_cons_of_mem d h)

/-- **Amortized cost of a decrement.** The digits read, minus two, are paid for by the zero digits
consumed. -/
theorem decSteps_add_count_le (ds : List ℕ) :
    decSteps ds + (decDigits ds).count 0 ≤ ds.count 0 + 2 := by
  induction ds with
  | nil => simp [decSteps, decDigits]
  | cons d ds ih =>
    by_cases h0 : d = 0
    · subst h0
      simp only [decSteps, decDigits, ↓reduceIte, List.count_cons_self, List.count_cons,
        beq_iff_eq, one_ne_zero, Nat.add_zero]
      omega
    · simp only [decSteps, h0, ↓reduceIte, decDigits, List.count_cons_self, List.count_cons,
        beq_iff_eq, Nat.add_zero]
      omega

/-! ### Registers -/

namespace Reg

/-- Base address of the counter digits. -/
abbrev bBase : Fin 24 := 21
/-- Number of counter digits. -/
abbrev bLen : Fin 24 := 22
/-- Whether the amplified algorithm runs another trial. -/
abbrev flag : Fin 24 := 23
/-- Digit index of the counter routines; shares register `12` with `sgn`. -/
abbrev idx : Fin 24 := 12
/-- Multiplier of a multiply-add; shares register `8` with `lend`. -/
abbrev mulr : Fin 24 := 8
/-- Carry of a multiply-add; shares register `9` with `sat`. -/
abbrev carry : Fin 24 := 9
/-- Divisor of a division; shares register `10` with `lit`. -/
abbrev dvs : Fin 24 := 10
/-- Remainder of a division; shares register `11` with `var`. -/
abbrev rmd : Fin 24 := 11
/-- Scratch value of a division; shares register `16` with `cPtr`. -/
abbrev tmp : Fin 24 := 16

end Reg

open Reg

/-! ### Multiply-add -/

/-- One digit of the multiply-add pass. -/
def mulAddBody : Code .standard 24 := ram[
  addr ← bBase + idx; val ← *addr; val ← val * mulr; val ← val + carry; carry ← val >>> one;
  val ← val &&& one; *addr ← val; idx ← idx + one ]

/-- The multiply-add pass over the digits from `idx`. -/
def mulAddLoop : Code .standard 24 := .loop (.lt idx bLen) mulAddBody

/-- Append the lowest digit of the carry. -/
def carryBody : Code .standard 24 := ram[
  addr ← bBase + bLen; val ← carry &&& one; *addr ← val; carry ← carry >>> one;
  bLen ← bLen + one ]

/-- Append the digits of the carry. -/
def carryLoop : Code .standard 24 := .loop (.lt zero carry) carryBody

/-- **Multiply-add**: replace the counter `v` by `v · mulr + carry`. -/
def mulAdd : Code .standard 24 := ram[ idx ← zero; ⟪mulAddLoop⟫; ⟪carryLoop⟫ ]

/-- Overwriting one entry of a represented list. -/
private theorem holdsList_update {B : ℕ} {pre ds : List ℕ} {d v : ℕ} {mem : ℕ → ℕ}
    (h : HoldsList B (pre ++ d :: ds) mem) :
    HoldsList B (pre ++ v :: ds) (Function.update mem (B + pre.length) v) := by
  obtain ⟨hpre, hd_ds⟩ := holdsList_append_iff.mp h
  obtain ⟨_, hds⟩ := (holdsList_append_iff (xs := [d]) (ys := ds)).mp hd_ds
  simp only [List.length_singleton] at hds
  simpa only [List.append_assoc, List.singleton_append] using holdsList_append_iff.mpr
    ⟨hpre.append_one v, by
      rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
      exact hds.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩

section Specs

variable {w : ℕ}

/-- **The multiply-add pass.** From the digits `ds` with `idx = 0`, the loop replaces them by the
digits of the pass and leaves its final carry in `carry`. -/
theorem mulAddLoop_spec {a Bd : ℕ} (haB : a ≤ Bd) (hf : Fits w (2 * Bd)) (ds : List ℕ)
    (x : Data 24) (cy : ℕ) (hone : x.regs one = 1) (ha : x.regs mulr = a) (hi : x.regs idx = 0)
    (hl : x.regs bLen = ds.length) (hc : x.regs carry = cy) (hcB : cy ≤ Bd)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hds : ∀ d ∈ ds, d ≤ 1)
    (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w mulAddLoop x y (10 * ds.length + 2) ∧
      HoldsList (x.regs bBase) (mulAddPass a cy ds).1 y.mem ∧
      y.regs carry = (mulAddPass a cy ds).2 ∧ ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  wram_fold (fun rest y => ∃ pre c, c ≤ Bd ∧ (∀ d ∈ rest, d ≤ 1) ∧ y.regs idx = pre.length ∧
      pre.length + rest.length = ds.length ∧ y.regs carry = c ∧
      HoldsList (x.regs bBase) (pre ++ rest) y.mem ∧ (∀ b, b < x.regs bBase → y.mem b = x.mem b) ∧
      pre ++ (mulAddPass a c rest).1 = (mulAddPass a cy ds).1 ∧
      (mulAddPass a c rest).2 = (mulAddPass a cy ds).2)
    over ds cost (fun _ => 8)
  case init => exact ⟨[], cy, hcB, hds, hi, by simp, hc, hh, fun _ _ => rfl, rfl, rfl⟩
  case exit => rintro v m ⟨pre, c, -, -, hi', hlen, -⟩; omega
  case step =>
    rintro d rest v m ⟨pre, c, hcB', hds', hi', hlen, hc', hh', hm', hrem₁, hrem₂⟩
    have hd : d ≤ 1 := hds' d (by simp)
    have hda : d * a ≤ a := by nlinarith
    have hmem : m (x.regs bBase + pre.length) = d := by simpa using hh'.get pre.length (by simp)
    set t := d * a + c with ht
    refine ⟨by omega, ?_⟩
    wram_exec [mulAddBody, hi', hmem, ha, hc', hone, ← ht, Nat.shiftRight_eq_div_pow, Nat.pow_one,
      Nat.and_one_is_mod]
    wram_simp
    refine ⟨pre ++ [t % 2], t / 2, by omega, fun d' hd' => hds' d' (by simp [hd']), by simp,
      by simp; omega, rfl, by simpa using holdsList_update (v := t % 2) hh', fun b hb => ?_, ?_, ?_⟩
    · wram_simp
      exact hm' b hb
    · rw [← hrem₁]; simp [mulAddPass, ht]
    · rw [← hrem₂]; simp [mulAddPass, ht]
  case post =>
    rintro v m ⟨pre, c, -, -, -, hlen, hc', hh', hm', hrem₁, hrem₂⟩
    simp only [mulAddPass, List.append_nil] at hh' hrem₁ hrem₂
    exact ⟨by simp [Nat.mul_comm], hrem₁ ▸ hh', hc'.trans hrem₂, hm'⟩

/-- **Appending the carry.** -/
theorem carryLoop_spec (cy : ℕ) (ds : List ℕ) (x : Data 24) (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (hc : x.regs carry = cy) (hl : x.regs bLen = ds.length)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hfc : Fits w cy)
    (hfit : Fits w (x.regs bBase + ds.length + (Nat.digits 2 cy).length)) :
    ∃ y, ExecWithin w carryLoop x y (7 * (Nat.digits 2 cy).length + 2) ∧
      HoldsList (x.regs bBase) (ds ++ Nat.digits 2 cy) y.mem ∧
      y.regs bLen = ds.length + (Nat.digits 2 cy).length ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  wram_fold (fun rest y => ∃ pre, pre ++ rest = Nat.digits 2 cy ∧
      Nat.digits 2 (y.regs carry) = rest ∧ y.regs carry ≤ cy ∧
      y.regs bLen = ds.length + pre.length ∧ HoldsList (x.regs bBase) (ds ++ pre) y.mem ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b)
    over (Nat.digits 2 cy) cost (fun _ => 5)
  case init =>
    exact ⟨[], rfl, by rw [hc], hc.le, by simpa using hl, by simpa using hh, fun _ _ => rfl⟩
  case exit =>
    rintro v m ⟨pre, -, hdig, -⟩
    have := Nat.digits_eq_nil_iff_eq_zero.mp hdig
    omega
  case step =>
    rintro d rest v m ⟨pre, hpre, hdig, hle, hl', hh', hm'⟩
    have hpos : 0 < v carry := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hdig
    rw [Nat.digits_def' (by decide) hpos] at hdig
    obtain ⟨rfl, hrest⟩ := List.cons.inj hdig
    have hlen : (Nat.digits 2 cy).length = pre.length + (rest.length + 1) := by
      rw [← hpre]; simp
    refine ⟨by omega, ?_⟩
    wram_exec [carryBody, hl', hone, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    wram_simp
    refine ⟨pre ++ [v carry % 2], by simpa using hpre, hrest, by omega, by simp; omega,
      by simpa using hh'.append_one (v carry % 2), fun b hb => ?_⟩
    wram_simp
    exact hm' b hb
  case post =>
    rintro v m ⟨pre, hpre, -, -, hl', hh', hm'⟩
    simp only [List.append_nil] at hpre
    subst hpre
    exact ⟨by simp [Nat.mul_comm], hh', hl', hm'⟩

/-- **Multiply-add.** On a counter with binary digits `ds`, with `mulr = a`, `carry = cy` and both
at most `Bd`, the routine leaves the digits `mulAddDigits a cy ds` of `v a + cy`. -/
theorem mulAdd_spec {a cy Bd : ℕ} {ds : List ℕ} {x : Data 24} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (ha : x.regs mulr = a) (hc : x.regs carry = cy)
    (hl : x.regs bLen = ds.length) (hh : HoldsList (x.regs bBase) ds x.mem)
    (hds : ∀ d ∈ ds, d ≤ 1) (haB : a ≤ Bd) (hcB : cy ≤ Bd) (hf : Fits w (2 * Bd))
    (hfit : Fits w (x.regs bBase + (mulAddDigits a cy ds).length)) :
    ∃ y, ExecWithin w mulAdd x y (10 * (mulAddDigits a cy ds).length + 5) ∧
      HoldsList (x.regs bBase) (mulAddDigits a cy ds) y.mem ∧
      y.regs bLen = (mulAddDigits a cy ds).length ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  have hlen : (mulAddDigits a cy ds).length =
      ds.length + (Nat.digits 2 (mulAddPass a cy ds).2).length := by
    simp [mulAddDigits]
  have hcarry := mulAddPass_carry_le hds haB hcB (cy := cy)
  refine WP.exists_execWithin ?_
  wram_exec [mulAdd, hz]
  wram_call (mulAddLoop_spec haB hf ds _ cy ..) framed with v₂ m₂ ⟨hh₂, hc₂, hm₂⟩
  wram_call (carryLoop_spec (mulAddPass a cy ds).2 (mulAddPass a cy ds).1 _ ..) framed
    [hl, length_mulAddPass] with v₃ m₃ ⟨hh₃, hl₃, hm₃⟩
  exact ⟨by omega, hh₃, by rw [hl₃, hlen], fun b hb => (hm₃ b hb).trans (hm₂ b hb)⟩

/-! ### Division -/

/-- One digit of the division, from the top: divide `2 · rmd + digit` by `dvs`. -/
def divBody : Code .standard 24 := ram[
  idx ← idx - one; addr ← bBase + idx; val ← *addr; tmp ← rmd + rmd; tmp ← tmp + val;
  val ← tmp / dvs; rmd ← tmp % dvs; *addr ← val ]

/-- Divide the digits below `idx`, from the top. -/
def divLoop : Code .standard 24 := .loop (.lt zero idx) divBody

/-- **Division**: replace the counter `v` by `⌊v / dvs⌋`. -/
def divFloor : Code .standard 24 := ram[ idx ← bLen; rmd ← zero; ⟪divLoop⟫ ]

/-- **The division loop.** From the digits `ds` with `idx` at their end and remainder `0`, the
loop replaces them, from the top, by the digits of the quotient. -/
theorem divLoop_spec {d : ℕ} (hd : 0 < d) (hfd : Fits w (2 * d)) (ds : List ℕ) (x : Data 24)
    (hz : x.regs zero = 0) (hone : x.regs one = 1) (hdv : x.regs dvs = d)
    (hi : x.regs idx = ds.length) (hr : x.regs rmd = 0)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hb : ∀ b ∈ ds, b ≤ 1)
    (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w divLoop x y (10 * ds.length + 2) ∧
      HoldsList (x.regs bBase) (divDigits d 0 ds).1 y.mem ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  wram_fold (fun rest y => ∃ qs r, r < d ∧ (∀ b ∈ rest, b ≤ 1) ∧ y.regs idx = rest.length ∧
      rest.length + qs.length = ds.length ∧ y.regs rmd = r ∧
      HoldsList (x.regs bBase) (rest.reverse ++ qs) y.mem ∧
      (∀ b, b < x.regs bBase → y.mem b = x.mem b) ∧
      (divDigits d r rest.reverse).1 ++ qs = (divDigits d 0 ds).1)
    over ds.reverse cost (fun _ => 8)
  case init =>
    exact ⟨[], 0, hd, by simpa using hb, by simpa using hi, by simp, hr, by simpa using hh,
      fun _ _ => rfl, by simp⟩
  case exit => rintro v m ⟨qs, r, -, -, hi', -⟩; omega
  case step =>
    rintro b rest v m ⟨qs, r, hrd, hb', hi', hlen, hr', hh', hm', hrem⟩
    have hbb : b ≤ 1 := hb' b (by simp)
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hh'
    have hmem : m (x.regs bBase + rest.length) = b := by
      simpa using hh'.get rest.length (by simp)
    set t := r + r + b with ht
    have := Nat.div_le_self t d
    have := Nat.mod_le t d
    refine ⟨by omega, ?_⟩
    wram_exec [divBody, hi', hone, hmem, hr', hdv, ← ht, Nat.add_sub_cancel]
    wram_simp
    refine ⟨t / d :: qs, t % d, Nat.mod_lt _ hd, fun b' h => hb' b' (by simp [h]), by simp; omega,
      rfl, by simpa using holdsList_update (v := t / d) hh', fun a ha => ?_, ?_⟩
    · wram_simp
      exact hm' a ha
    · rw [← hrem, List.reverse_cons, divDigits_append_singleton, show 2 * r + b = t by omega]
      simp
  case post =>
    rintro v m ⟨qs, r, -, -, -, hlen, -, hh', hm', hrem⟩
    simp only [List.reverse_nil, divDigits, List.nil_append] at hh' hrem
    exact ⟨by simp [Nat.mul_comm], hrem ▸ hh', hm'⟩

/-- **Division.** On a counter with binary digits `ds` and `dvs = d > 0`, the routine leaves the
digits `(divDigits d 0 ds).1` of `⌊v / d⌋`, with the same length. -/
theorem divFloor_spec {d : ℕ} {ds : List ℕ} {x : Data 24} (hd : 0 < d) (hfd : Fits w (2 * d))
    (hz : x.regs zero = 0) (hone : x.regs one = 1) (hdv : x.regs dvs = d)
    (hl : x.regs bLen = ds.length) (hh : HoldsList (x.regs bBase) ds x.mem)
    (hds : ∀ b ∈ ds, b ≤ 1) (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w divFloor x y (10 * ds.length + 4) ∧
      HoldsList (x.regs bBase) (divDigits d 0 ds).1 y.mem ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  refine WP.exists_execWithin ?_
  wram_exec [divFloor, hl, hz]
  wram_call (divLoop_spec hd hfd ds _ ..) framed with v m ⟨hyh, hym⟩
  exact ⟨by omega, hyh, hym⟩

/-! ### Decrement -/

/-- One digit of the decrement: a zero becomes one and the scan continues; a nonzero digit becomes
zero, the routine records that the counter was nonzero, and the scan stops. -/
def decBody : Code .standard 24 := ram[
  addr ← bBase + idx; val ← *addr;
  if val = zero then [ *addr ← one; idx ← idx + one ]
  else [ *addr ← zero; found ← one; idx ← bLen ] ]

/-- Decrement from the digit `idx`. -/
def decLoop : Code .standard 24 := .loop (.lt idx bLen) decBody

/-- **Decrement**: decrement a nonzero counter and set `found = 1`; on a zero counter set
`found = 0`. -/
def decCounter : Code .standard 24 := ram[ idx ← zero; found ← zero; ⟪decLoop⟫ ]

/-- **The decrement loop.** -/
theorem decLoop_spec : ∀ (ds pre : List ℕ) (x : Data 24),
    x.regs zero = 0 → x.regs one = 1 → x.regs idx = pre.length →
    x.regs bLen = pre.length + ds.length → x.regs found = 0 →
    HoldsList (x.regs bBase) (pre ++ ds) x.mem → Fits w (x.regs bBase + pre.length + ds.length) →
    ∃ y, ExecWithin w decLoop x y (9 * decSteps ds + 2) ∧
      HoldsList (x.regs bBase) (pre ++ decDigits ds) y.mem ∧
      y.regs found = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b
  | [], pre, x, _, _, hi, hl, hfd, hh, _ => by
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp [decSteps]), by simpa [decDigits] using hh,
      by simp [hfd], fun _ _ => rfl⟩
    simp [Cond.holds_lt, hi, hl]
  | d :: ds, pre, x, hz, hone, hi, hl, hfd, hh, hfit => by
    have hc : (Cond.lt idx bLen).Holds x := by
      simp only [Cond.holds_lt, hi, hl, List.length_cons]; omega
    simp only [List.length_cons] at hl hfit
    have hmem : x.mem (x.regs bBase + pre.length) = d := by simpa using hh.get pre.length (by simp)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold decBody
    by_cases h0 : d = 0
    · subst h0
      have hupd : HoldsList (x.regs bBase) (pre ++ [1] ++ ds)
          (Function.update x.mem (x.regs bBase + pre.length) 1) := by
        simpa using holdsList_update (v := 1) hh
      wram_exec [hi, hmem, hz, hone]
      wram_call (decLoop_spec ds (pre ++ [1]) _ ..) framed
        [List.length_append, List.length_singleton] with v m ⟨hyh, hyf, hym⟩
      refine ⟨by simp [decSteps]; omega, by simpa [decDigits] using hyh, by simp [hyf],
        fun b hb => ?_⟩
      rw [hym b hb]; wram_simp
    · wram_exec [hi, hmem, hz, hone, hl]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hl]))
        ⟨by simp [decSteps, h0], ?_, by wram_simp; simp [h0], fun b hb => by wram_simp⟩
      simpa [decDigits, h0] using holdsList_update (v := 0) hh

/-- **Decrement.** On a counter with digits `ds`, the routine leaves the digits `decDigits ds`
within `9 · decSteps ds + 4` instructions and sets `found` to whether some digit was nonzero. -/
theorem decCounter_spec {ds : List ℕ} {x : Data 24} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (hl : x.regs bLen = ds.length)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w decCounter x y (9 * decSteps ds + 4) ∧
      HoldsList (x.regs bBase) (decDigits ds) y.mem ∧
      y.regs found = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  refine WP.exists_execWithin ?_
  wram_exec [decCounter, hz]
  wram_call (decLoop_spec ds [] _ ..) framed [List.length_nil, List.nil_append, Nat.zero_add]
    with v m ⟨hyh, hyf, hym⟩
  exact ⟨by omega, hyh, hyf, hym⟩

end Specs

end Cslib.Algorithms.WordRAM.Schoening

end
