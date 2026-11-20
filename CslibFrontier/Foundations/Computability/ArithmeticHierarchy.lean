/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Computability.ComputablePred

/-!
# The arithmetic hierarchy

The finite levels use alternating quantifiers over natural numbers followed by a computable
predicate. The zero level consists of computable predicates. Each block can use one natural
number because finite tuples of natural numbers have computable encodings.
[Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

namespace Cslib.Computability

/-- Apply `k` alternating unbounded natural-number quantifiers. A true flag makes the
outermost quantifier existential. The matrix receives the witnesses in quantifier order. -/
def arithmeticQuantify : ℕ → Bool → (List ℕ → Prop) → Prop
  | 0, _, matrix => matrix []
  | k + 1, true, matrix => ∃ n, arithmeticQuantify k false (fun ns => matrix (n :: ns))
  | k + 1, false, matrix => ∀ n, arithmeticQuantify k true (fun ns => matrix (n :: ns))

/-- The existential level `Σ⁰ₖ` of the arithmetic hierarchy. -/
def ArithmeticSigma (k : ℕ) : Set (Set ℕ) :=
  {A | ∃ matrix : ℕ × List ℕ → Prop, ComputablePred matrix ∧
    ∀ a, a ∈ A ↔ arithmeticQuantify k true (fun ns => matrix (a, ns))}

/-- The universal level `Π⁰ₖ` of the arithmetic hierarchy. -/
def ArithmeticPi (k : ℕ) : Set (Set ℕ) :=
  {A | ∃ matrix : ℕ × List ℕ → Prop, ComputablePred matrix ∧
    ∀ a, a ∈ A ↔ arithmeticQuantify k false (fun ns => matrix (a, ns))}

/-- The level `Δ⁰ₖ` consists of the sets in both levels `Σ⁰ₖ` and `Π⁰ₖ`. -/
def ArithmeticDelta (k : ℕ) : Set (Set ℕ) := ArithmeticSigma k ∩ ArithmeticPi k

/-- The sets of natural numbers in the arithmetic hierarchy, at any finite level. -/
def AH : Set (Set ℕ) := ⋃ k, ArithmeticSigma k ∪ ArithmeticPi k

end Cslib.Computability
