/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.Order.Floor.Div
import CslibFrontier.Computability.Circuit.Simulation

/-!
# The Zhegalkin Boolean basis `{⊕, ∧, 1}` and Theorem 1 gate budget

Defines the Zhegalkin operation signature `Zhegalkin.Op` (`{1, ⊕, ∧}`), its standard Boolean
interpretation `Zhegalkin.interpretation`, conjunction-gate weight `Zhegalkin.andCost`, and the
explicit Theorem 1 gate budget `Zhegalkin.totalBound`.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.Op`, `Cslib.Circuits.Boolean.Zhegalkin.signature`,
  `Cslib.Circuits.Boolean.Zhegalkin.interpretation`: the Zhegalkin Boolean basis `{⊕, ∧, 1}`.
* `Cslib.Circuits.Boolean.Zhegalkin.andCost`: conjunction-gate weight (`1` on `.and`, `0` on
  `.xor` and `.one`).
* `Cslib.Circuits.Boolean.Zhegalkin.totalBound`: explicit `(n, M, s, p)` total gate budget for the
  upper bound of Theorem 1.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.interpretation_one`, `interpretation_xor`,
  `interpretation_and`, `andCost_and`, `andCost_xor`, `andCost_one`, `cost_andCost_le`:
  evaluation and conjunction-cost bounds over `{⊕, ∧, 1}`.

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

namespace Cslib.Circuits.Boolean.Zhegalkin

/-- Operations of the Zhegalkin (algebraic normal form) Boolean circuit basis `{⊕, ∧, 1}`. -/
inductive Op where
  /-- The Boolean constant `true` (`1`). -/
  | one
  /-- Binary exclusive-or `⊕` (`xor`, addition in `GF(2)`). -/
  | xor
  /-- Binary conjunction `∧` (`and`, multiplication in `GF(2)`). -/
  | and
  deriving DecidableEq

/-- Finite enumeration of the Zhegalkin basis operations. -/
instance : Fintype Op :=
  ⟨{.one, .xor, .and}, fun op => by cases op <;> simp⟩

/-- The Zhegalkin signature: nullary `one` and binary `xor` and `and`. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .one => 0
    | .xor | .and => 2

/-- Standard Boolean interpretation of the Zhegalkin basis `{⊕, ∧, 1}`. -/
@[expose] def interpretation : Interpretation signature Bool
  | .one, _ => true
  | .xor, x => x 0 ^^ x 1
  | .and, x => x 0 && x 1

/-- Under `interpretation`, `.one` evaluates to `true`. -/
@[simp] theorem interpretation_one (x : Fin 0 → Bool) :
    interpretation .one x = true := rfl

/-- Under `interpretation`, `.xor` evaluates to `x 0 ^^ x 1`. -/
@[simp] theorem interpretation_xor (x : Fin 2 → Bool) :
    interpretation .xor x = (x 0 ^^ x 1) := rfl

/-- Under `interpretation`, `.and` evaluates to `x 0 && x 1`. -/
@[simp] theorem interpretation_and (x : Fin 2 → Bool) :
    interpretation .and x = (x 0 && x 1) := rfl

/-- Conjunction-gate weight charging `1` for each `.and` gate and `0` for `.xor` and `.one`. -/
@[expose] def andCost : Op → ℕ
  | .and => 1
  | .one | .xor => 0

/-- A conjunction gate has `andCost` equal to `1`. -/
@[simp] theorem andCost_and : andCost .and = 1 := rfl

/-- An XOR gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_xor : andCost .xor = 0 := rfl

/-- A constant-`1` gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_one : andCost .one = 0 := rfl

/-- The number of conjunction gates in a `{⊕, ∧, 1}`-program is at most its total gate count. -/
theorem cost_andCost_le {n g : ℕ} (p : Program signature n g) : p.cost andCost ≤ g := by
  simpa only [one_mul] using p.cost_le_mul (b := 1) (fun op => by cases op <;> decide)

/-- Explicit total gate budget over `{⊕, ∧, 1}` for the upper bound of [Sergeev, Theorem 1, p. 3]
[Sergeev2013AdditiveMultiplicative] for an `n`-input Boolean function of multiplicative complexity
at most `M`, with block/stage width `s` and horizontal section height `p`. -/
@[expose] def totalBound (n M s p : ℕ) : ℕ :=
  ((n + M) * 2 ^ s) / s + (M * (M + 2 * n)) / (2 * s) + 2 * M * (p + s + 1) +
    ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2

end Cslib.Circuits.Boolean.Zhegalkin
