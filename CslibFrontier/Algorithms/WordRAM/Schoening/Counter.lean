/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
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
    rcases he with rfl | he
    · omega
    · exact ih _ e he

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
    by_cases h0 : d = 0
    · simp only [decDigits, h0, ↓reduceIte, List.mem_cons] at he
      rcases he with rfl | he
      · decide
      · exact ih (fun d' hd' => hds d' (by simp [hd'])) e he
    · simp only [decDigits, h0, ↓reduceIte, List.mem_cons] at he
      rcases he with rfl | he
      · decide
      · exact hds e (by simp [he])

/-- **Amortized cost of a decrement.** The digits read, minus two, are paid for by the zero digits
consumed. -/
theorem decSteps_add_count_le (ds : List ℕ) :
    decSteps ds + (decDigits ds).count 0 ≤ ds.count 0 + 2 := by
  induction ds with
  | nil => simp [decSteps, decDigits]
  | cons d ds ih =>
    by_cases h0 : d = 0
    · subst h0
      simp only [decSteps, decDigits, ↓reduceIte, List.count_cons_self, List.count_cons]
      simp only [beq_iff_eq, one_ne_zero, ↓reduceIte, Nat.add_zero]
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

/-- **The multiply-add pass.** From the digits `pre ++ ds` with `idx` at `ds`, the loop replaces
`ds` by the digits of the pass and leaves its final carry in `carry`. -/
theorem mulAddLoop_spec {a Bd : ℕ} (haB : a ≤ Bd) (hf : Fits w (2 * Bd)) :
    ∀ (ds pre : List ℕ) (x : Data 24) (cy : ℕ),
      x.regs one = 1 → x.regs mulr = a → x.regs idx = pre.length →
      x.regs bLen = pre.length + ds.length → x.regs carry = cy → cy ≤ Bd →
      HoldsList (x.regs bBase) (pre ++ ds) x.mem → (∀ d ∈ ds, d ≤ 1) →
      Fits w (x.regs bBase + pre.length + ds.length) →
      ∃ y, ExecWithin w mulAddLoop x y (10 * ds.length + 2) ∧
        HoldsList (x.regs bBase) (pre ++ (mulAddPass a cy ds).1) y.mem ∧
        y.regs carry = (mulAddPass a cy ds).2 ∧ y.regs bLen = x.regs bLen ∧
        y.regs bBase = x.regs bBase ∧ y.regs one = 1 ∧ y.regs mulr = a ∧
        ∀ b, b < x.regs bBase → y.mem b = x.mem b
  | [], pre, x, cy, hone, _, hi, hl, hc, _, hh, _, _ => by
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simpa [mulAddPass] using hh,
      by simp [mulAddPass, hc], rfl, rfl, hone, by assumption, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hi, hl]
  | d :: ds, pre, x, cy, hone, ha, hi, hl, hc, hcB, hh, hds, hfit => by
    have hd : d ≤ 1 := hds d (by simp)
    have hda : d * a ≤ a := by nlinarith
    simp only [List.length_cons] at hl hfit
    have hc' : (Cond.lt idx bLen).Holds x := by simp only [Cond.holds_lt, hi, hl]; omega
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = d := by simpa using hh.get pre.length (by simp)
    set v := d * a + cy with hv
    have : Fits w (d * a) := hf.of_le (by omega)
    have hfv : Fits w v := hf.of_le (by omega)
    have : Fits w (v / 2) := hfv.of_le (by omega)
    have : Fits w (v % 2) := hfv.of_le (by omega)
    have : Fits w (pre.length + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin (WP.loop_iter hc' ?_)
    unfold mulAddBody
    wram_exec [hB, hi, hmem, ha, hc, hone, ← hv, Nat.shiftRight_eq_div_pow, Nat.pow_one,
      Nat.and_one_is_mod]
    wram_call (mulAddLoop_spec haB hf ds (pre ++ [v % 2]) _ (v / 2)
      (by wram_simp [hone]) (by wram_simp [ha])
      (by wram_simp [List.length_append, List.length_singleton])
      (by wram_simp [hl, List.length_append, List.length_singleton]; omega)
      (by wram_simp) (by omega)
      (by wram_simp [hB]; simpa using holdsList_update (v := v % 2) hh)
      (fun d' hd' => hds d' (by simp [hd']))
      (by wram_simp [hB]; exact hfit.of_le (by simp; omega)))
      with y ⟨hyh, hyc, hyl, hyb, hyo, hya, hym⟩
    wram_simp [hB] at hyh hyb hym
    wram_simp at hyl
    refine ⟨by simp only [List.length_cons]; omega, by simpa [mulAddPass, hv] using hyh,
      by simpa [mulAddPass, hv] using hyc, hyl, hyb, hyo, hya, fun b hb => ?_⟩
    rw [hym b hb]; wram_simp

/-- **Appending the carry.** -/
theorem carryLoop_spec : ∀ (cy : ℕ) (ds : List ℕ) (x : Data 24),
    x.regs zero = 0 → x.regs one = 1 → x.regs carry = cy → x.regs bLen = ds.length →
    HoldsList (x.regs bBase) ds x.mem → Fits w cy →
    Fits w (x.regs bBase + ds.length + (Nat.digits 2 cy).length) →
    ∃ y, ExecWithin w carryLoop x y (7 * (Nat.digits 2 cy).length + 2) ∧
      HoldsList (x.regs bBase) (ds ++ Nat.digits 2 cy) y.mem ∧
      y.regs bLen = ds.length + (Nat.digits 2 cy).length ∧ y.regs bBase = x.regs bBase ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  intro cy
  induction cy using Nat.strong_induction_on with
  | _ cy ih =>
    intro ds x hz hone hc hl hh hfc hfit
    rcases Nat.eq_zero_or_pos cy with rfl | hpos
    · refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp), by simpa using hh, by simp [hl], rfl,
        fun _ _ => rfl⟩
      simp [Cond.holds_lt, hz, hc]
    · have hdig : Nat.digits 2 cy = cy % 2 :: Nat.digits 2 (cy / 2) :=
        Nat.digits_def' (by decide) hpos
      rw [hdig] at hfit ⊢
      simp only [List.length_cons] at hfit ⊢
      have hc' : (Cond.lt zero carry).Holds x := by simp [Cond.holds_lt, hz, hc, hpos]
      obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
      rw [hB] at hh hfit ⊢
      have : Fits w (cy % 2) := hfc.of_le (by omega)
      have : Fits w (cy / 2) := hfc.of_le (by omega)
      have : Fits w (ds.length + 1) := hfit.of_le (by omega)
      refine WP.exists_execWithin (WP.loop_iter hc' ?_)
      unfold carryBody
      wram_exec [hB, hl, hc, hone, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      wram_call (ih (cy / 2) (by omega) (ds ++ [cy % 2]) _
        (by wram_simp [hz]) (by wram_simp [hone]) (by wram_simp)
        (by wram_simp [List.length_append, List.length_singleton])
        (by wram_simp [hB]; exact hh.append_one (cy % 2))
        (hfc.of_le (by omega)) (by wram_simp [hB]; exact hfit.of_le (by simp; omega)))
        with y ⟨hyh, hyl, hyb, hym⟩
      wram_simp [hB] at hyh hyb hym
      have hyl' : y.regs bLen = ds.length + ((Nat.digits 2 (cy / 2)).length + 1) := by
        simp only [List.length_append, List.length_singleton] at hyl; omega
      refine ⟨by omega, by simpa using hyh, hyl', hyb, fun b hb => ?_⟩
      rw [hym b hb]; wram_simp

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
  unfold mulAdd
  wram_exec [hz]
  refine WP.name fun x₁ hx₁ => ?_
  obtain ⟨y₂, hy₂, hh₂, hc₂, hl₂, hb₂, ho₂, -, hm₂⟩ := mulAddLoop_spec haB hf ds [] x₁ cy
    (by subst hx₁; wram_simp [hone]) (by subst hx₁; wram_simp [ha])
    (by subst hx₁; wram_simp; rfl) (by subst hx₁; wram_simp [hl, List.length_nil])
    (by subst hx₁; wram_simp [hc]) hcB (by subst hx₁; wram_simp; exact hh) hds
    (hfit.of_le (by subst hx₁; wram_simp [List.length_nil]; omega))
  have hz₂ : y₂.regs zero = 0 :=
    (hy₂.regs_eq (by decide)).trans (by subst hx₁; wram_simp [hz])
  subst hx₁
  wram_simp at hh₂ hb₂ hm₂
  wram_simp [hl] at hl₂
  refine WP.of_execWithin hy₂ ?_
  wram_call (carryLoop_spec (mulAddPass a cy ds).2 (mulAddPass a cy ds).1 y₂ hz₂ ho₂ hc₂
    (by simp [hl₂]) (by rw [hb₂]; simpa using hh₂) (hf.of_le (by omega))
    (by rw [hb₂]; exact hfit.of_le (by simp; omega)))
    with y₃ ⟨hh₃, hl₃, _, hm₃⟩
  rw [hb₂] at hh₃ hm₃
  exact ⟨by omega, hh₃, by rw [hl₃, hlen]; simp, fun b hb => (hm₃ b hb).trans (hm₂ b hb)⟩

/-! ### Division -/

/-- One digit of the division, from the top: divide `2 · rmd + digit` by `dvs`. -/
def divBody : Code .standard 24 := ram[
  idx ← idx - one; addr ← bBase + idx; val ← *addr; tmp ← rmd + rmd; tmp ← tmp + val;
  val ← tmp / dvs; rmd ← tmp % dvs; *addr ← val ]

/-- Divide the digits below `idx`, from the top. -/
def divLoop : Code .standard 24 := .loop (.lt zero idx) divBody

/-- **Division**: replace the counter `v` by `⌊v / dvs⌋`. -/
def divFloor : Code .standard 24 := ram[ idx ← bLen; rmd ← zero; ⟪divLoop⟫ ]

/-- **The division loop.** From the digits `pre ++ qs` with `idx` at the end of `pre` and remainder
`r < d`, the loop replaces `pre` by its quotient digits and leaves the remainder in `rmd`. -/
theorem divLoop_spec {d : ℕ} (hd : 0 < d) (hfd : Fits w (2 * d)) :
    ∀ (pre qs : List ℕ) (x : Data 24) (r : ℕ),
      x.regs zero = 0 → x.regs one = 1 → x.regs dvs = d → x.regs idx = pre.length →
      x.regs rmd = r → r < d → HoldsList (x.regs bBase) (pre ++ qs) x.mem →
      (∀ b ∈ pre, b ≤ 1) → Fits w (x.regs bBase + pre.length) →
      ∃ y, ExecWithin w divLoop x y (10 * pre.length + 2) ∧
        HoldsList (x.regs bBase) ((divDigits d r pre).1 ++ qs) y.mem ∧
        y.regs rmd = (divDigits d r pre).2 ∧ y.regs bBase = x.regs bBase ∧
        ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro qs x r hz _ _ hi hr _ hh _ _
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simpa [divDigits] using hh,
      by simp [divDigits, hr], rfl, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hz, hi]
  | append_singleton pre b ih =>
    intro qs x r hz hone hdv hi hr hrd hh hb hfit
    simp only [List.length_append, List.length_singleton] at hi hfit
    have hbb : b ≤ 1 := hb b (by simp)
    have hc : (Cond.lt zero idx).Holds x := by simp [Cond.holds_lt, hz, hi]
    rw [List.append_assoc, List.singleton_append] at hh
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = b := by simpa using hh.get pre.length (by simp)
    set t := r + r + b with ht
    have : Fits w pre.length := hfit.of_le (by omega)
    have : Fits w (B + pre.length) := hfit.of_le (by omega)
    have : Fits w (r + r) := hfd.of_le (by omega)
    have hft : Fits w t := hfd.of_le (by omega)
    have : Fits w (t / d) := hft.of_le (Nat.div_le_self _ _)
    have : Fits w (t % d) := hft.of_le (Nat.mod_le _ _)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold divBody
    wram_exec [hi, hone, hB, hmem, hr, hdv, ← ht, Nat.add_sub_cancel]
    wram_call (ih (t / d :: qs) _ (t % d) (by wram_simp [hz]) (by wram_simp [hone])
      (by wram_simp [hdv]) (by wram_simp) (by wram_simp) (Nat.mod_lt _ hd)
      (by wram_simp [hB]; exact holdsList_update (v := t / d) hh)
      (fun b' hb' => hb b' (by simp [hb'])) (by wram_simp [hB]; exact hfit.of_le (by omega)))
      with y ⟨hyh, hyr, hyb, hym⟩
    wram_simp [hB] at hyh hyb hym
    have ht' : t = 2 * r + b := by omega
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_,
      by rw [hyr, divDigits_append_singleton, ← ht'], hyb, fun a ha => ?_⟩
    · rw [divDigits_append_singleton, List.append_assoc, List.singleton_append, ← ht']
      exact hyh
    · rw [hym a ha]; wram_simp

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
  unfold divFloor
  wram_exec [hl, hz]
  wram_call (divLoop_spec hd hfd ds [] _ 0 (by wram_simp [hz]) (by wram_simp [hone])
    (by wram_simp [hdv]) (by wram_simp) (by wram_simp) hd (by wram_simp; simpa using hh) hds
    (by wram_simp; exact hfit))
    with y ⟨hyh, -, _, hym⟩
  wram_simp at hyh hym
  exact ⟨by omega, by simpa using hyh, hym⟩

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
      y.regs found = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧ y.regs bBase = x.regs bBase ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b
  | [], pre, x, _, _, hi, hl, hfd, hh, _ => by
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp [decSteps]), by simpa [decDigits] using hh,
      by simp [hfd], rfl, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hi, hl]
  | d :: ds, pre, x, hz, hone, hi, hl, hfd, hh, hfit => by
    have hc : (Cond.lt idx bLen).Holds x := by
      simp only [Cond.holds_lt, hi, hl, List.length_cons]; omega
    simp only [List.length_cons] at hl hfit
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = d := by simpa using hh.get pre.length (by simp)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    unfold decBody
    by_cases h0 : d = 0
    · subst h0
      have : Fits w (pre.length + 1) := hfit.of_le (by omega)
      wram_exec [hB, hi, hmem, hz, hone]
      wram_call (decLoop_spec ds (pre ++ [1]) _ (by wram_simp [hz]) (by wram_simp [hone])
        (by wram_simp [List.length_append, List.length_singleton])
        (by wram_simp [hl, List.length_append, List.length_singleton]; omega)
        (by wram_simp [hfd])
        (by wram_simp [hB]; simpa using holdsList_update (v := 1) hh)
        (by wram_simp [hB]; exact hfit.of_le (by simp; omega)))
        with y ⟨hyh, hyf, hyb, hym⟩
      wram_simp [hB] at hyh hyb hym
      refine ⟨by simp [decSteps]; omega, by simpa [decDigits] using hyh, by simp [hyf], hyb,
        fun b hb => ?_⟩
      rw [hym b hb]; wram_simp
    · have : Fits w (pre.length + (ds.length + 1)) := hfit.of_le (by omega)
      have : Fits w 1 := hfit.of_le (by omega)
      wram_exec [hB, hi, hmem, hz, hone, hl]
      refine WP.of_execWithin (ExecWithin.loop_exit (by wram_simp [Cond.holds_lt, hl]))
        ⟨by simp [decSteps, h0], ?_, by wram_simp; simp [h0], by wram_simp [hB],
          fun b hb => by wram_simp⟩
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
  unfold decCounter
  wram_exec [hz]
  wram_call (decLoop_spec ds [] _ (by wram_simp [hz]) (by wram_simp [hone]) (by wram_simp; rfl)
    (by wram_simp [hl, List.length_nil]) (by wram_simp) (by wram_simp; exact hh)
    (by wram_simp [List.length_nil]; exact hfit))
    with y ⟨hyh, hyf, _, hym⟩
  wram_simp at hyh hym
  exact ⟨by omega, hyh, hyf, hym⟩

end Specs

end Cslib.Algorithms.WordRAM.Schoening

end
