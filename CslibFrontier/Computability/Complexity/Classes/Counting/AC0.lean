/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Basic
public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Constant-depth arithmetic counting classes

`GapAC0` uses nonuniform polynomial-size constant-depth circuits over the integers, with
unbounded fan-in sums and products, input literals and constants zero, one and minus one.
`CeqAC0` tests equality of two such circuit families using only zero and one as constants.
A logspace-uniform variant would also require a uniform circuit generator.

## References

* [Allender et al., *Bounded Depth Arithmetic Circuits: Counting and Closure*]
  (https://www.cs.rutgers.edu/~allender/papers/icalp99.pdf)
* [Complexity Zoo, GapAC⁰](https://complexityzoo.net/Complexity_Zoo:G#gapac0)
* [Complexity Zoo, exact-counting AC⁰](https://complexityzoo.net/Complexity_Zoo:C)
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Circuits
open scoped BigOperators

/-- Gates for a constant-depth arithmetic counting circuit. The constant labels are drawn
from `K`. -/
inductive AC0CountingGate (K : Type)
  | const : K → AC0CountingGate K
  | sum : ℕ → AC0CountingGate K
  | prod : ℕ → AC0CountingGate K

/-- The unbounded finite-arity arithmetic counting signature. -/
def ac0CountingSignature (K : Type) : Signature where
  Op := AC0CountingGate K
  Arity
    | .const _ => 0
    | .sum k | .prod k => k

/-- Evaluate the unbounded fan-in arithmetic gates over the integers. -/
def ac0CountingInterpretation {K : Type} (constant : K → ℤ) :
    Interpretation (ac0CountingSignature K) ℤ
  | .const a, _ => constant a
  | .sum _, x => ∑ i, x i
  | .prod _, x => ∏ i, x i

/-- A single family computing an integer-valued string function in constant depth with
polynomially bounded gate count and fan-in. The first half of the inputs are the positive
literals and the second half are the negative literals. The bounds also bound total wiring. -/
def HasAC0CountingCircuits {K : Type} (constant : K → ℤ) (f : List Bool → ℤ) : Prop :=
  ∃ (d : ℕ) (p : Polynomial ℕ) (c : ∀ n, Circuit (ac0CountingSignature K) (n + n) 1),
    (∀ n, (c n).depth ≤ d ∧ (c n).size ≤ p.eval n ∧ (c n).FanInAtMost (p.eval n)) ∧
      ∀ x, (c x.length).eval (ac0CountingInterpretation constant)
        (Fin.addCases (fun i => (x[i].toNat : ℤ)) (fun i => ((!x[i]).toNat : ℤ))) 0 = f x

/-- Nonuniform `GapAC0`, with constants `0`, `1` and `-1`. -/
def GapAC0 : Set (List Bool → ℤ) :=
  {f | HasAC0CountingCircuits (fun i : Fin 3 => (i.val : ℤ) - 1) f}

/-- Exact counting in nonuniform `AC0`. The difference of two nonnegative counting families
is zero precisely on members. -/
def CeqAC0 : Set (Set (List Bool)) :=
  {A | ∃ f g : List Bool → ℤ,
    HasAC0CountingCircuits (fun b : Bool => (b.toNat : ℤ)) f ∧
    HasAC0CountingCircuits (fun b : Bool => (b.toNat : ℤ)) g ∧
    ∀ x, x ∈ A ↔ f x = g x}

end Cslib.Complexity
