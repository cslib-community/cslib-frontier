/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Basic

/-!
# Formal midpoints

Terms built from letters by a binary "midpoint" operation, which name the iterated midpoints in
the proof that the space of prices is CAT(0) in *VP ≠ VNP over every field* (Anthropic,
`anthropics/formal-math`, commit `11b6c7e3c9`, module `Nc.Cat.Space`).

## Main definitions

* `Separation.MidpointTerm V`: formal midpoints over the letters `V`.
* `MidpointTerm.depth`, `MidpointTerm.base`: the depth and the first letter of a term.
* `MidpointTerm.place n s`: a term of depth at most `n + 1` is either kept (depth at most `n`) or
  split into the pair of its two arguments.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation

/-- Formal midpoints over the letters `V`. -/
inductive MidpointTerm (V : Type) : Type
  | of : V → MidpointTerm V
  | mid : MidpointTerm V → MidpointTerm V → MidpointTerm V

namespace MidpointTerm

variable {V : Type}

/-- The depth of a term. -/
def depth : MidpointTerm V → ℕ
  | of _ => 0
  | mid s t => max s.depth t.depth + 1

/-- The first letter of a term. -/
def base : MidpointTerm V → V
  | of v => v
  | mid s _ => s.base

/-- Where the terms of depth at most `n + 1` stand when a new point is added for every pair of
terms of depth at most `n`: terms of depth at most `n` stay, deeper ones become the pair of their
arguments. -/
def place (n : ℕ) (s : MidpointTerm V) : MidpointTerm V ⊕ (MidpointTerm V × MidpointTerm V) :=
  if s.depth ≤ n then Sum.inl s else
    match s with
    | of v => Sum.inl (of v)
    | mid a b => Sum.inr (a, b)

end MidpointTerm

end Cslib.Circuits.Arithmetic.Separation
