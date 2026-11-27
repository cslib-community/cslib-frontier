/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Tabulation

/-!
# Tests for unary arithmetic in logarithmic space

Composite arithmetic on unary numbers and list lengths, discharged by `fun_prop` alone with the
instances of
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary`.
-/

namespace CslibFrontierTests.LogSpaceUnary

open Turing Turing.MultiTapeTM

/-- A polynomial with a truncated difference, in unary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.1 + (p.2 - p.1))
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- A constant factor on the left, by `unaryMul` with a constant. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => 3 * p.1 + p.2 * 2)
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- Quotient and remainder, combined with minimum and maximum. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => max (p.1 / p.2) (min (p.1 % p.2) 3))
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- A comparison of composite values, used as the condition of an `if`. -/
example : ComputableInLogSpace
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ p.1 + p.2 then p.1 else p.2 * p.2)
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- Equality and strict comparison of products, as Booleans. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => decide (p.1 * p.2 = p.2) && decide (p.1 < p.2))
    (encPair encUnary encUnary) encBool := by
  fun_prop

/-- A unary product, in binary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.2) (encPair encUnary encUnary) encNat :=
  ComputableInLogSpace.unaryToBinary (by fun_prop)

/-- A polynomial given directly as a counter-program expression, in unary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.1 + p.2) (encPair encUnary encUnary)
    encUnary :=
  CounterProgram.Unary.computableInLogSpace_unary (F := fun a b => a * a + b)
    (.add (.mul (.reg 0) (.reg 0)) (.reg 1)) fun _ _ => rfl

/-- A polynomial given directly as a counter-program expression, in binary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.1 + p.2) (encPair encUnary encUnary)
    encNat :=
  CounterProgram.Unary.computableInLogSpace_binary (F := fun a b => a * a + b)
    (.add (.mul (.reg 0) (.reg 0)) (.reg 1)) fun _ _ => rfl

/-- Comparing the length of a list with its head. -/
example : ComputableInLogSpace (fun l : List ℕ => decide (l.length * l.length ≤ l.headD 0))
    (encList encUnary) encBool := by
  fun_prop

/-- Bit-word length, logarithm, size and fixed unary powers under `fun_prop`. -/
example : ComputableInLogSpace
    (fun p : List Bool × ℕ => (Nat.log2 p.1.length) ^ 3 + p.2.size ^ 2)
    (encPair encBits encUnary) encUnary := by
  fun_prop

/-- `List.length` on `encBits` targets `encUnary`; binary output requires `unaryToBinary`. -/
example : ComputableInLogSpace (fun w : List Bool => w.length ^ 2) encBits encNat := by
  fail_if_success fun_prop
  exact ComputableInLogSpace.unaryToBinary (by fun_prop)

-- Nested variable-length rows. The first row is empty and later rows share both outer parameters.
example : ComputableInLogSpace (fun p : ℕ × ℕ => (List.range p.1).map fun j =>
    (List.range j).map fun i => p.2 + i + j) (encPair encUnary encUnary)
    (encList (encList encUnary)) := by
  apply ComputableInLogSpace.map_range (.pair .unary .unary) (r := Prod.fst)
    (f := fun p : (ℕ × ℕ) × ℕ => (List.range p.2).map fun i => p.1.2 + i + p.2) (by fun_prop)
  apply ComputableInLogSpace.map_range (.pair (.pair .unary .unary) .unary) (r := Prod.snd)
    (f := fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2 + p.2 + p.1.2) (by fun_prop)
  fun_prop

end CslibFrontierTests.LogSpaceUnary
