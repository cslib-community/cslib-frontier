/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-! # Decimal digits that the kernel can evaluate

`Nat.toDecimal n` is the list of the decimal digits of `n`, most significant first, as
`toString n` writes them. It is defined by recursion on a fuel argument, with its body exposed,
so that the kernel evaluates it: `Nat.toDigits`, behind `toString`, has no exposed body. Reading
the digits back from the left gives `n`, which is what a parser of decimal numbers needs to read
back what a printer wrote.

## Main definitions

* `Nat.toDecimal`: the decimal digits of a number.
* `Nat.digitStep`: reading one more digit.

## Main statements

* `Nat.isDigit_of_mem_toDecimal`: the digits are decimal digits.
* `Nat.foldl_digitStep_toDecimal`: reading them back gives the number.
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
before it. -/
def digitStep (m : ℕ) (c : Char) : ℕ := 10 * m + (c.toNat - '0'.toNat)

/-- A digit `d < 10` is a decimal digit character, and its value is `d`. -/
theorem decimalDigit_spec : ∀ {d : ℕ}, d < 10 →
    (decimalDigit d).isDigit = true ∧ (decimalDigit d).toNat - '0'.toNat = d
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

private theorem toDecimalAux_spec {fuel n : ℕ} (h : n < fuel) :
    (∀ c ∈ toDecimalAux fuel n, c.isDigit = true) ∧ toDecimalAux fuel n ≠ [] ∧
      ∀ a, (toDecimalAux fuel n).foldl digitStep a =
        a * 10 ^ (toDecimalAux fuel n).length + n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    have hd := decimalDigit_spec (Nat.mod_lt n (show 10 > 0 by decide))
    rw [toDecimalAux]
    refine ⟨fun c hc => ?_, by simp, fun a => ?_⟩
    · rcases List.mem_append.1 hc with hc | hc
      · split at hc
        · simp at hc
        · exact (ih (by omega)).1 c hc
      · rw [List.mem_singleton.1 hc]
        exact hd.1
    · split
      · rename_i h10
        rw [Nat.mod_eq_of_lt h10] at hd ⊢
        simp only [List.nil_append, List.foldl_cons, List.foldl_nil, digitStep, hd.2,
          List.length_singleton, Nat.pow_one, Nat.mul_comm]
      · rw [List.foldl_append, (ih (by omega)).2.2, List.length_append, List.foldl_cons,
          List.foldl_nil, digitStep, hd.2, List.length_singleton, Nat.pow_succ]
        have := Nat.div_add_mod n 10
        generalize 10 ^ (toDecimalAux fuel (n / 10)).length = P
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 10 a, Nat.mul_assoc, Nat.mul_comm 10 P]
        omega

/-- **The decimal digits of a number are digits.** -/
theorem isDigit_of_mem_toDecimal {n : ℕ} {c : Char} (h : c ∈ toDecimal n) : c.isDigit = true :=
  (toDecimalAux_spec (Nat.lt_succ_self n)).1 c h

/-- A number has at least one decimal digit. -/
theorem toDecimal_ne_nil (n : ℕ) : toDecimal n ≠ [] := (toDecimalAux_spec (Nat.lt_succ_self n)).2.1

/-- **Reading back the decimal digits of a number**, after the value `a` of the digits before
them. -/
theorem foldl_digitStep_toDecimal (n a : ℕ) :
    (toDecimal n).foldl digitStep a = a * 10 ^ (toDecimal n).length + n :=
  (toDecimalAux_spec (Nat.lt_succ_self n)).2.2 a

/-- Reading back the decimal digits of a number gives it. -/
theorem foldl_digitStep_toDecimal_zero (n : ℕ) : (toDecimal n).foldl digitStep 0 = n := by
  simp [foldl_digitStep_toDecimal]

end Nat
