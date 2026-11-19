/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CNF

/-!
# Clauses as words

The word-RAM SAT programs store a literal `(v, b)` over the variables `ℕ` as the word `2 v + b`
(`Cslib.Algorithms.WordRAM.ClauseCode.litCode`), and a clause as its length followed by the codes of
its literals (`Cslib.Algorithms.WordRAM.ClauseCode.encodeClause`). The variable of a code is its
shift right by one bit and the sign its low bit, so the codes determine the literals
(`Cslib.Algorithms.WordRAM.ClauseCode.litCode_injective`), and flipping the low bit negates the
literal (`Cslib.Algorithms.WordRAM.ClauseCode.litCode_xor_one`).

Programs over the variables `Fin n`, such as Schöning's and PPSZ's, encode a literal through the
value of its variable.

## Main definitions

* `Cslib.Algorithms.WordRAM.ClauseCode.litCode`, `Cslib.Algorithms.WordRAM.ClauseCode.encodeClause`:
  the codes of literals and clauses.

## Main results

* `Cslib.Algorithms.WordRAM.ClauseCode.litCode_shiftRight`,
  `Cslib.Algorithms.WordRAM.ClauseCode.litCode_and_one`: decoding the variable and the sign.
* `Cslib.Algorithms.WordRAM.ClauseCode.litCode_injective`: the codes determine the literals.
* `Cslib.Algorithms.WordRAM.ClauseCode.litCode_xor_one`: the low bit negates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ClauseCode

open Cslib.Logic.PL

/-- The word code `2 v + b` of the literal `(v, b)`. -/
def litCode (l : Literal ℕ) : ℕ := 2 * l.1 + l.2.toNat

/-- A clause is stored as its length followed by the codes of its literals. -/
def encodeClause (c : Clause ℕ) : List ℕ := c.length :: c.map litCode

@[simp]
theorem length_encodeClause (c : Clause ℕ) : (encodeClause c).length = c.length + 1 := by
  simp [encodeClause]

/-- Shifting a literal code right recovers its variable. -/
theorem litCode_shiftRight (l : Literal ℕ) : litCode l >>> 1 = l.1 := by
  obtain ⟨v, b⟩ := l
  rw [Nat.shiftRight_eq_div_pow]
  cases b <;> simp only [litCode, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The low bit of a literal code is its sign. -/
theorem litCode_and_one (l : Literal ℕ) : litCode l &&& 1 = l.2.toNat := by
  obtain ⟨v, b⟩ := l
  rw [Nat.and_one_is_mod]
  cases b <;> simp only [litCode, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A literal code is at most twice its variable plus one. -/
theorem litCode_le (l : Literal ℕ) : litCode l ≤ 2 * l.1 + 1 := by
  have := Bool.toNat_le l.2
  simp only [litCode]; omega

/-- **The codes determine the literals.** -/
theorem litCode_injective : Function.Injective litCode := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  simp only [litCode] at h
  cases b <;> cases b' <;> simp_all <;> omega

theorem litCode_inj {l l' : Literal ℕ} : litCode l = litCode l' ↔ l = l' :=
  litCode_injective.eq_iff

theorem two_mul_xor_one (v : ℕ) : (2 * v) ^^^ 1 = 2 * v + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · have : (2 * v + 1) / 2 = v := by omega
    simp [Nat.testBit_succ, this]

theorem two_mul_add_one_xor_one (v : ℕ) : (2 * v + 1) ^^^ 1 = 2 * v := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · have : (2 * v + 1) / 2 = v := by omega
    simp [Nat.testBit_succ, this]

/-- **Flipping the low bit negates**: the code of the negation of a literal. -/
theorem litCode_xor_one (l : Literal ℕ) : litCode l ^^^ 1 = litCode (Std.Sat.Literal.negate l) := by
  obtain ⟨v, b⟩ := l
  cases b
  · simpa [litCode, Std.Sat.Literal.negate] using two_mul_xor_one v
  · simpa [litCode, Std.Sat.Literal.negate] using two_mul_add_one_xor_one v

end Cslib.Algorithms.WordRAM.ClauseCode

end
