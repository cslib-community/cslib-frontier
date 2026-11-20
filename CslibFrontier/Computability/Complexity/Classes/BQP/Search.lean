/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP
public import CslibFrontier.Computability.Complexity.Classes.TFNP

/-!
# Bounded-error quantum search

`FBQP` uses total relations and vanishing error, as in
[Aaronson, §2.2, Definition 3][Aaronson2010BQPPolynomialHierarchy]. A single uniform circuit
family and polynomial-time decoder produce a valid output with probability tending to one
uniformly over inputs as their encoded length grows.

`VerifiableFBQPSearch` requires a polynomial-time graph verifier and a uniform quantum solver
with fixed bounded error. A uniform quantum circuit is measured in the
computational basis, and a polynomial-time classical decoder turns the measured word into
an optional witness. On an input having no witness the correct result is `none`, as in
`FPSearch`. The probability bound applies to the entire event of returning a correct result,
which can include several different witnesses.

## Main definitions

* `FBQP`: total relational search with vanishing error.
* `VerifiableFBQPSearch`: polynomial-time verifiable search with a bounded-error quantum solver.
* `RBQP`: the domains of `VerifiableFBQPSearch` problems.
* `ZBQP`: both membership and nonmembership have such search witnesses.

## References

* [Complexity Zoo, FBQP](https://complexityzoo.net/Complexity_Zoo:F#FBQP:_Function_BQP)
* [Complexity Zoo, RBQP](https://complexityzoo.net/Complexity_Zoo:R#RBQP:_Strict_Quantum_RP)
* [Complexity Zoo, ZBQP](https://complexityzoo.net/Complexity_Zoo:Z#ZBQP:_Zero-Error_BQP)
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type}

/-- Probability that measurement and decoding give a valid witness, or report an empty fiber
when the fiber is empty. -/
noncomputable def quantumSearchSuccess (F : UniformCircuitFamily)
    (decode : List Bool × List Bool → Option (List Bool))
    (enc : α ↪ List Bool) (R : α → List Bool → Prop) (a : α) : ℝ :=
  let x := enc a
  let C := Circuit.ofCodes (F.width x.length) (F.gates x.length)
  ((C.measure (inputState (F.width x.length) x)).toOuterMeasure
    {y | match decode (x, List.ofFn y) with
         | some w => R a w
         | none => a ∉ searchDomain R}).toReal

/-- Total relations solved by one quantum polynomial-time algorithm with vanishing error. -/
def FBQP (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | (∀ a, ∃ w, R a w) ∧
    ∃ F : UniformCircuitFamily, ∃ decode : List Bool × List Bool → Option (List Bool),
      ComputableInPolyTime decode (encPair encBits encBits) (encOption encBits) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ a, n ≤ (enc a).length →
        1 - ε ≤ quantumSearchSuccess F decode enc R a}

/-- The relations in `FNP` solved with probability at least `2 / 3` by measuring a uniform
quantum circuit and decoding its output together with the original input. -/
def VerifiableFBQPSearch (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧
    ∃ F : UniformCircuitFamily, ∃ decode : List Bool × List Bool → Option (List Bool),
      ComputableInPolyTime decode (encPair encBits encBits) (encOption encBits) ∧
      ∀ a, 2 / 3 ≤ quantumSearchSuccess F decode enc R a}

/-- The decision problems with polynomial-time verifiable witnesses findable in
`VerifiableFBQPSearch`. -/
def RBQP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ R ∈ VerifiableFBQPSearch enc, searchDomain R = A}

/-- Strict zero-error quantum polynomial time, with efficiently checkable witnesses for
both answers. -/
def ZBQP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | A ∈ RBQP enc ∧ Aᶜ ∈ RBQP enc}


end Cslib.Complexity
