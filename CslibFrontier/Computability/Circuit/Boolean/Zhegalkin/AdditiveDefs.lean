/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log

/-!
# Active square of a Boolean matrix and the additive `{0, +}` circuit basis

Defines `Matrix.activeSquare` (`S(A)`), the additive circuit signature `Additive.signature`
over `{0, +}`, its monoid `Additive.interpretation`, and the explicit Lemma 1 gate budget
`Additive.matrixBound`.

## Main definitions

* `Matrix.activeSquare`: active square `S(A)` of an `m × n` Boolean matrix.
* `Cslib.Circuits.Additive.Op`, `Cslib.Circuits.Additive.signature`,
  `Cslib.Circuits.Additive.interpretation`, `Cslib.Circuits.Additive.matrixBound`: the additive
  circuit basis `{0, +}` and explicit `(s, p)` gate budget of Lemma 1.

## Main results

* `Matrix.activeSquare_le_mul`: `A.activeSquare ≤ m * n`.
* `Cslib.Circuits.Additive.interpretation_zero`, `Cslib.Circuits.Additive.interpretation_add`:
  simp evaluation rules for `Additive.interpretation`.

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

open Finset

namespace Matrix

/-- The *active square* `S(A)` of an `m × n` Boolean matrix `A`
([Sergeev, p. 2][Sergeev2013AdditiveMultiplicative]): the number of entries `(i, j)` located within
horizontal distance `Nat.log 2 m` of a `true` entry in the same row `i`. Because column distances
are natural numbers, for `1 ≤ m` the condition `Nat.dist j j' ≤ Nat.log 2 m` is equivalent to
`(Nat.dist j j' : ℝ) ≤ Real.logb 2 m`. -/
@[expose] def activeSquare {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) : ℕ :=
  #{p : Fin m × Fin n | ∃ j' : Fin n, A p.1 j' = true ∧ Nat.dist p.2.val j'.val ≤ Nat.log 2 m}

/-- The active square of an `m × n` Boolean matrix is at most `m * n`. -/
theorem activeSquare_le_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) :
    A.activeSquare ≤ m * n :=
  (card_filter_le _ _).trans_eq (by simp)

end Matrix

namespace Cslib.Circuits

namespace Additive

/-- Operations of the additive monoid circuit basis `{0, +}`. -/
inductive Op where
  /-- The additive identity `0`. -/
  | zero
  /-- Binary addition `+`. -/
  | add
  deriving DecidableEq

instance : Fintype Op :=
  ⟨{.zero, .add}, fun op => by cases op <;> simp⟩

/-- The additive circuit signature: nullary `zero` and binary `add`. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .zero => 0
    | .add => 2

/-- Interpretation of the additive signature in any type with `0` and `+`. -/
@[expose] def interpretation (G : Type*) [AddZeroClass G] : Interpretation signature G
  | .zero, _ => 0
  | .add, x => x 0 + x 1

@[simp] theorem interpretation_zero (G : Type*) [AddZeroClass G] (x : Fin 0 → G) :
    interpretation G .zero x = 0 := rfl

@[simp] theorem interpretation_add (G : Type*) [AddZeroClass G] (x : Fin 2 → G) :
    interpretation G .add x = x 0 + x 1 := rfl

/-- Explicit gate budget of [Sergeev, Lemma 1, p. 3][Sergeev2013AdditiveMultiplicative] for an
`m × n` Boolean matrix `A` with column-group width `s` and horizontal section height `p`. -/
@[expose] def matrixBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) : ℕ :=
  (n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)

end Additive

end Cslib.Circuits
