/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CNF
import Mathlib.Data.Nat.Bitwise

/-!
# Clauses as words

The word-RAM SAT programs store a literal `(v, b)` as the word `2 f(v) + b`, where `f` numbers the
variables (`Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy`), and a clause as its length followed by
the codes of its literals (`Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy`). The variable's
number of a code is its shift right by one bit and the sign its low bit, so for injective `f` the
codes determine the literals (`Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_injective`), and
flipping the low bit negates the literal (`Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_xor_one`).

Programs over the variables `ℕ`, such as the LRAT checker, number them by `id`
(`Cslib.Algorithms.WordRAM.ClauseCode.litCode`, `Cslib.Algorithms.WordRAM.ClauseCode.encodeClause`);
programs over `Fin n`, such as Schöning's and PPSZ's, by `Fin.val`.

## Main definitions

* `Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy`,
  `Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy`: the codes of literals and clauses.

## Main results

* `Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_shiftRight`,
  `Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_and_one`: decoding the variable and the sign.
* `Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_injective`: the codes determine the literals.
* `Cslib.Algorithms.WordRAM.ClauseCode.litCodeBy_xor_one`: the low bit negates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ClauseCode

open Cslib.Logic.PL

variable {α : Type*} (f : α → ℕ)

/-- The word code `2 f(v) + b` of the literal `(v, b)`. Inlined, so that compiled code computes
the code without a call through `f`. -/
@[inline] def litCodeBy (l : Literal α) : ℕ := 2 * f l.1 + l.2.toNat

/-- A clause is stored as its length followed by the codes of its literals. -/
def encodeClauseBy (c : Clause α) : List ℕ := c.length :: c.map (litCodeBy f)

/-- The code of a literal over the variables `ℕ`. -/
abbrev litCode (l : Literal ℕ) : ℕ := litCodeBy id l

/-- The words of a clause over the variables `ℕ`. -/
abbrev encodeClause (c : Clause ℕ) : List ℕ := encodeClauseBy id c

@[simp]
theorem length_encodeClauseBy (c : Clause α) : (encodeClauseBy f c).length = c.length + 1 := by
  simp [encodeClauseBy]

/-- Shifting a literal code right recovers the number of its variable. -/
theorem litCodeBy_shiftRight (l : Literal α) : litCodeBy f l >>> 1 = f l.1 := by
  obtain ⟨v, b⟩ := l
  rw [Nat.shiftRight_eq_div_pow]
  cases b <;> simp only [litCodeBy, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The low bit of a literal code is its sign. -/
theorem litCodeBy_and_one (l : Literal α) : litCodeBy f l &&& 1 = l.2.toNat := by
  obtain ⟨v, b⟩ := l
  rw [Nat.and_one_is_mod]
  cases b <;> simp only [litCodeBy, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A literal code is at most twice the number of its variable plus one. -/
theorem litCodeBy_le (l : Literal α) : litCodeBy f l ≤ 2 * f l.1 + 1 := by
  have := Bool.toNat_le l.2
  simp only [litCodeBy]; omega

/-- **The codes determine the literals** when `f` is injective. -/
theorem litCodeBy_injective {f : α → ℕ} (hf : Function.Injective f) :
    Function.Injective (litCodeBy f) := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have h1 := congrArg (· >>> 1) h
  have h2 := congrArg (· &&& 1) h
  simp only [litCodeBy_shiftRight, litCodeBy_and_one] at h1 h2
  rw [hf h1]
  cases b <;> cases b' <;> simp_all

/-- The codes of literals over `ℕ` determine the literals. -/
theorem litCode_injective : Function.Injective litCode :=
  litCodeBy_injective Function.injective_id

/-- **Flipping the low bit negates**: the code of the negation of a literal. -/
theorem litCodeBy_xor_one (l : Literal α) :
    litCodeBy f l ^^^ 1 = litCodeBy f (Std.Sat.Literal.negate l) := by
  obtain ⟨v, b⟩ := l
  simp only [litCodeBy, Std.Sat.Literal.negate]
  cases b
  · simp only [Bool.toNat_false, Nat.add_zero, Bool.not_false, Bool.toNat_true]
    exact Nat.xor_one_of_even (even_two_mul _)
  · simp only [Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero]
    rw [Nat.xor_one_of_odd (odd_two_mul_add_one _)]
    omega

/-- Negating a literal raises its code by at most one. -/
theorem litCodeBy_negate_le (l : Literal α) :
    litCodeBy f (Std.Sat.Literal.negate l) ≤ litCodeBy f l + 1 := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp only [litCodeBy, Std.Sat.Literal.negate, Bool.not_false, Bool.not_true,
    Bool.toNat_false, Bool.toNat_true] <;> omega

end Cslib.Algorithms.WordRAM.ClauseCode

end
