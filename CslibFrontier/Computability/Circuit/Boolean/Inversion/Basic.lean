/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Negation cost and descent ranks

Negation cost counts NOT gates and gives AND, OR and constants cost zero. It is an operation
weight for the native circuit syntax, so sharing and multiple outputs have their usual meaning.

A descent rank increases weakly when the supplied inputs increase, and increases strictly
whenever the target fails to increase. The rank is the invariant used in both directions of
Markov's inversion theorem: a circuit with `k` negations has a rank below `2 ^ k`, and such a
rank permits synthesis with `k` negations. These are the two rank arguments behind
[Markov1963, Theorem 4.1 and Lemmas 5.1–5.2].

## Main definitions

* `Cslib.Circuits.Boolean.negationCost`: the operation weight charging exactly NOT gates.
* `Cslib.Circuits.Boolean.IsDescentRank`: a rank separating every target decrease along
  comparable source values.

## References

* [A. A. Markov, *On the Inversion Complexity of a System of Boolean Functions*][Markov1963],
  Theorem 4.1 and Lemmas 5.1–5.2, printed pp. 478–479.
-/

public section

namespace Cslib.Circuits.Boolean

/-- The operation weight charging one for NOT and zero for AND, OR and constants. -/
@[expose] def negationCost : Op → ℕ
  | .not => 1
  | _ => 0

/-- Negation has cost one. -/
@[simp] theorem negationCost_not : negationCost .not = 1 := rfl

/-- Conjunction is free when counting negations. -/
@[simp] theorem negationCost_and : negationCost .and = 0 := rfl

/-- Disjunction is free when counting negations. -/
@[simp] theorem negationCost_or : negationCost .or = 0 := rfl

/-- Constants are free when counting negations. -/
@[simp] theorem negationCost_const (b : Bool) : negationCost (.const b) = 0 := rfl

/-- A natural-valued rank that increases with the supplied values, and makes the target
monotone between comparable points of equal rank. Thus every target decrease forces a strict
rank increase. Sources and targets may be vectors or any other preordered types. -/
structure IsDescentRank {X α β : Type*} [Preorder α] [Preorder β]
    (sources : X → α) (target : X → β) (rank : X → ℕ) : Prop where
  /-- Increasing source values cannot decrease the rank. -/
  monotone : ∀ ⦃x y⦄, sources x ≤ sources y → rank x ≤ rank y
  /-- At equal rank, increasing source values cannot decrease the target. -/
  preserves_eq : ∀ ⦃x y⦄, sources x ≤ sources y → rank x = rank y → target x ≤ target y

end Cslib.Circuits.Boolean
