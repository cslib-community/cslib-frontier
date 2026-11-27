/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Basic polynomial-time rules

Direct plain machine providers supply framing, finite functions, equality, Boolean guards and
composition. This module adds disjunction and inequality rules and the shared polynomial-bound
extraction lemma `PolyBounded.exists_polynomial`.
-/

public section

namespace Turing.MultiTapeTM

/-- A polynomially bounded resource admits a polynomial upper bound at every input size. -/
theorem PolyBounded.exists_polynomial {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : ∃ p : Polynomial ℕ, ∀ a, u a ≤ p.eval (size a) := by
  obtain ⟨c, d, hle⟩ := h.exists_le
  exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun a => by simpa using hle a⟩

end Turing.MultiTapeTM

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Disjunction of efficiently decidable propositions uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_or {left right : α → Prop} [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hleft : ComputableInPolyTime (fun a => decide (left a)) encA encBool)
    (hright : ComputableInPolyTime (fun a => decide (right a)) encA encBool) :
    ComputableInPolyTime (fun a => decide (left a ∨ right a)) encA encBool := by
  simpa only [Bool.decide_or, Function.comp_def] using bool_or.comp (hleft.prod hright)

/-- Disjoin computed guards, fixing both intermediate Boolean encodings. -/
theorem bool_or' {left right : α → Bool}
    (hleft : ComputableInPolyTime left encA encBool)
    (hright : ComputableInPolyTime right encA encBool) :
    ComputableInPolyTime (fun a => left a || right a) encA encBool :=
  bool_or.comp (hleft.prod hright)

/-- Lawful Boolean inequality compares computed values through their common encoding. -/
@[fun_prop]
theorem bne [BEq β] [LawfulBEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => left x != right x) encA encBool := by
  simpa only [_root_.bne, Function.comp_def] using bool_not.comp (hleft.beq hright)

/-- Compare two computed values using their common encoding. -/
@[fun_prop]
theorem decide_ne [DecidableEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left encA encB)
    (hright : ComputableInPolyTime right encA encB) :
    ComputableInPolyTime (fun x => decide (left x ≠ right x)) encA encBool := by
  simpa only [Function.comp_def, decide_not] using bool_not.comp (hleft.decide_eq' hright)

end Turing.MultiTapeTM.ComputableInPolyTime
