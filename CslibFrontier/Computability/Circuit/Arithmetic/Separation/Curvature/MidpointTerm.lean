/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Free

/-!
# Formal midpoints

Terms built from letters by a binary "midpoint" operation name the iterated midpoints in the
proof that the space of prices is CAT(0) in *VP ≠ VNP over every field* [AnthropicVPVNP2026]
(module `Nc.Cat.Space`). They are the elements of Mathlib's free magma `FreeMagma V`: a letter
`FreeMagma.of v`, or the formal midpoint `s * t` of two terms, with no associativity law.

## Main definitions

* `Separation.MidpointTerm.depth`, `Separation.MidpointTerm.base`: the depth and the first letter
  of a term.
* `Separation.MidpointTerm.place n s`: a term of depth at most `n` stays, a deeper one is split
  into the pair of its two arguments.

## Main results

* `Separation.MidpointTerm.place_of_depth_le`: terms of depth at most `n` stay.
* `Separation.MidpointTerm.place_of_depth_eq_succ`: a term of depth `n + 1` splits into two
  arguments of depth at most `n`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.MidpointTerm

variable {V : Type}

/-- The depth of a formal midpoint term. -/
@[expose] def depth : FreeMagma V → ℕ
  | .of _ => 0
  | .mul s t => max (depth s) (depth t) + 1

/-- The first letter of a term. -/
@[expose] def base : FreeMagma V → V
  | .of v => v
  | .mul s _ => base s

@[simp] theorem depth_of (v : V) : depth (FreeMagma.of v) = 0 := rfl

@[simp] theorem depth_mul (s t : FreeMagma V) : depth (s * t) = max (depth s) (depth t) + 1 :=
  rfl

@[simp] theorem base_of (v : V) : base (FreeMagma.of v) = v := rfl

@[simp] theorem base_mul (s t : FreeMagma V) : base (s * t) = base s := rfl

/-- Where the terms of depth at most `n + 1` stand when a new point is added for every pair of
terms of depth at most `n`: terms of depth at most `n` stay, deeper ones become the pair of their
arguments. -/
@[expose] def place (n : ℕ) (s : FreeMagma V) : FreeMagma V ⊕ (FreeMagma V × FreeMagma V) :=
  if depth s ≤ n then .inl s else
    match s with
    | .of v => .inl (.of v)
    | .mul a b => .inr (a, b)

theorem place_of_depth_le {n : ℕ} {s : FreeMagma V} (h : depth s ≤ n) : place n s = .inl s := by
  simp only [place, ite_eq_left h]

/-- A term of depth `n + 1` splits into the pair of its arguments, both of depth at most `n`. -/
theorem place_of_depth_eq_succ {n : ℕ} {s : FreeMagma V} (h : depth s = n + 1) :
    ∃ a b, s = a * b ∧ place n s = .inr (a, b) ∧ depth a ≤ n ∧ depth b ≤ n := by
  cases s with
  | of v => simp at h
  | mul a b =>
    have h' : max (depth a) (depth b) + 1 = n + 1 := h
    refine ⟨a, b, rfl, ?_, by omega, by omega⟩
    simp only [place, ite_eq_right (show ¬ depth (a.mul b) ≤ n from fun h'' => by
      change max (depth a) (depth b) + 1 ≤ n at h''; omega)]

end Cslib.Circuits.Arithmetic.Separation.MidpointTerm
