/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-! # Decimal digits that the kernel can evaluate

`Nat.toDecimal n` is the list of the decimal digits of `n`, most significant first: Lean core's
`Nat.toDigits 10 n`, behind `toString n` (`Nat.toDecimal_eq_toDigits`). It is defined again, by
recursion on a fuel argument and with its body exposed, so that the kernel evaluates it:
`Nat.toDigits` has no exposed body. `Int.toDecimal` writes an integer, with `-` if it is
negative.

`Nat.ofDecimal?` is the checked reader of decimal numerals shared by the DIMACS and OPB front
ends: one or more decimal digits, read from the left by `Nat.digitStep`, which is the step of
core's `Nat.ofDigitChars 10` (`Nat.foldl_digitStep_eq_ofDigitChars`). Each front end adds its
own syntax at its boundary: DIMACS its `_` digit separators, OPB its signs. Reading back what
`Nat.toDecimal` writes gives the number (`Nat.ofDecimal?_toDecimal`), by core's
`Nat.ofDigitChars_ten_toDigits`.

## Main definitions

* `Nat.toDecimal`, `Int.toDecimal`: the decimal digits of a number, of an integer.
* `Nat.digitStep`: reading one more digit.
* `Nat.ofDecimal?`: reading a decimal numeral.

## Main statements

* `Nat.toDecimal_eq_toDigits`: the digits are those of `Nat.toDigits 10`.
* `Nat.isDigit_of_mem_toDecimal`: the digits are decimal digits.
* `Nat.foldl_digitStep_eq_ofDigitChars`: reading digits is core's `Nat.ofDigitChars 10`.
* `Nat.ofDecimal?_toDecimal`: reading back the digits of a number gives it.
-/

@[expose] public section

namespace Nat

/-- The decimal digit of `d < 10`, and `'9'` above. -/
def decimalDigit : ℕ → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- The decimal digits of `n`, with `fuel` bounding their number. -/
def toDecimalAux : ℕ → ℕ → List Char
  | 0, _ => []
  | fuel + 1, n => (if n < 10 then [] else toDecimalAux fuel (n / 10)) ++ [decimalDigit (n % 10)]

/-- **The decimal digits of `n`**, most significant first, without leading zeros: `['0']` for
`0`. -/
def toDecimal (n : ℕ) : List Char := toDecimalAux (n + 1) n

/-- The value `10 * m + d` of the digit `c`, with value `d`, after the value `m` of the digits
before it: the step of `Nat.ofDigitChars 10`. -/
def digitStep (m : ℕ) (c : Char) : ℕ := 10 * m + (c.toNat - '0'.toNat)

/-- **A decimal numeral**: one or more decimal digits, read from the left. -/
def ofDecimal? (cs : List Char) : Option ℕ :=
  if !cs.isEmpty && cs.all Char.isDigit then some (cs.foldl digitStep 0) else none

end Nat

/-- **The decimal digits of an integer**, with `-` in front if it is negative. -/
def Int.toDecimal (a : ℤ) : List Char :=
  if a < 0 then '-' :: Nat.toDecimal a.natAbs else Nat.toDecimal a.natAbs

end

public section

namespace Nat

/-- The decimal digit of `d < 10` is core's `Nat.digitChar d`. -/
theorem decimalDigit_eq_digitChar : ∀ {d : ℕ}, d < 10 → decimalDigit d = d.digitChar
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by simp [decimalDigit]
  | _ + 10, h => absurd h (by omega)

private theorem toDecimalAux_eq {fuel n : ℕ} (h : n < fuel) :
    toDecimalAux fuel n = Nat.toDigits 10 n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    rw [toDecimalAux, Nat.toDigits_eq_ite (by decide),
      decimalDigit_eq_digitChar (Nat.mod_lt n (by decide))]
    split
    · rename_i h10
      rw [Nat.mod_eq_of_lt h10]
      rfl
    · rw [ih (by omega)]

/-- **The digits are those of Lean core's `Nat.toDigits 10`**, which `toString` writes. -/
theorem toDecimal_eq_toDigits (n : ℕ) : toDecimal n = Nat.toDigits 10 n :=
  toDecimalAux_eq (Nat.lt_succ_self n)

/-- **The decimal digits of a number are digits.** -/
theorem isDigit_of_mem_toDecimal {n : ℕ} {c : Char} (h : c ∈ toDecimal n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) (toDecimal_eq_toDigits n ▸ h)

/-- A number has at least one decimal digit. -/
theorem toDecimal_ne_nil (n : ℕ) : toDecimal n ≠ [] :=
  toDecimal_eq_toDigits n ▸ Nat.toDigits_ne_nil

/-- **Reading digits by `Nat.digitStep` is core's `Nat.ofDigitChars 10`.** -/
theorem foldl_digitStep_eq_ofDigitChars (cs : List Char) (a : ℕ) :
    cs.foldl digitStep a = Nat.ofDigitChars 10 cs a :=
  Nat.ofDigitChars_eq_foldl.symm

/-- **Reading a decimal numeral**: the value of its digits, if it has one or more and only
digits. -/
theorem ofDecimal?_eq_some_iff {cs : List Char} {n : ℕ} :
    ofDecimal? cs = some n ↔
      cs ≠ [] ∧ (∀ c ∈ cs, c.isDigit = true) ∧ Nat.ofDigitChars 10 cs 0 = n := by
  unfold ofDecimal?
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at h
    simp only [Option.some.injEq, foldl_digitStep_eq_ofDigitChars]
    exact ⟨fun hn => ⟨h.1, h.2, hn⟩, fun hn => hn.2.2⟩
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      not_and] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun hne hd => absurd hd (h hne)

/-- **Reading back the decimal digits of a number gives it.** -/
@[simp] theorem ofDecimal?_toDecimal (n : ℕ) : ofDecimal? (toDecimal n) = some n :=
  ofDecimal?_eq_some_iff.2 ⟨toDecimal_ne_nil n, fun _ => isDigit_of_mem_toDecimal,
    by rw [toDecimal_eq_toDigits, Nat.ofDigitChars_ten_toDigits]⟩

/-- A number has a first decimal digit. -/
theorem exists_toDecimal_eq_cons (n : ℕ) :
    ∃ d ds, toDecimal n = d :: ds ∧ d.isDigit = true := by
  obtain ⟨d, ds, h⟩ := List.exists_cons_of_ne_nil (toDecimal_ne_nil n)
  exact ⟨d, ds, h, isDigit_of_mem_toDecimal (h ▸ List.mem_cons_self)⟩

end Nat

namespace Int

/-- The characters of an integer are `-` and decimal digits. -/
theorem mem_toDecimal {a : ℤ} {c : Char} (h : c ∈ a.toDecimal) : c = '-' ∨ c.isDigit = true := by
  unfold toDecimal at h
  split at h
  · rcases List.mem_cons.1 h with rfl | h
    · exact .inl rfl
    · exact .inr (Nat.isDigit_of_mem_toDecimal h)
  · exact .inr (Nat.isDigit_of_mem_toDecimal h)

/-- The first character of an integer is `-` or a decimal digit. -/
theorem exists_toDecimal_eq_cons (a : ℤ) :
    ∃ d ds, a.toDecimal = d :: ds ∧ (d = '-' ∨ d.isDigit = true) := by
  unfold toDecimal
  split
  · exact ⟨_, _, rfl, .inl rfl⟩
  · obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons a.natAbs
    exact ⟨d, ds, h, .inr hd⟩

/-- An integer has at least one character. -/
theorem toDecimal_ne_nil (a : ℤ) : a.toDecimal ≠ [] := by
  obtain ⟨d, ds, h, -⟩ := exists_toDecimal_eq_cons a
  simp [h]

end Int

end
