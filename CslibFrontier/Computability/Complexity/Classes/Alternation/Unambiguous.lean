/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation

/-!
# Unambiguous alternating polynomial time

An existential node has at most one accepting child, and a universal node at most one rejecting
child. This applies throughout the tree, including descendants of a branch that does not determine
its parent's result. We use the binary branching model, counting the two moves separately,
as in the binary normal form of [Niedermeier and Rossmanith][NiedermeierRossmanith1998],
Definition 11 and Theorem 13.

The separate polynomial clock covers every branch. In the [checked examples]
(https://github.com/cslib-community/cslib-frontier/blob/e95c90d139/CslibFrontierTests/Alternation.lean),
a one-step machine witnesses membership in `UAP`, and an existential root with an accepting
move still fails the restriction when its other move leads to an ambiguous universal node.

## Main definitions

* `Turing.MultiTapeATM.UnambiguousWithin`: local unambiguity throughout a clocked tree.
* `Cslib.Complexity.UAP`: languages decided in alternating polynomial time under that restriction.
-/

public section

namespace Turing.MultiTapeATM

/-- Every existential node before the clock expires has at most one accepting move.
Every universal node has at most one rejecting move. Child values use the remaining clock.
A separate halting condition is needed to guarantee that the clock includes the whole tree. -/
@[expose] def UnambiguousWithin {k : ℕ} {State : Type} (M : MultiTapeATM k Bool State)
    {input : List Bool} : ℕ → Cfg k Bool State input → Prop
  | 0, _ => True
  | n + 1, c => match c.state with
    | none => True
    | some q =>
      (if M.universal q then
        M.AcceptsWithin n (M.next false c) ∨ M.AcceptsWithin n (M.next true c)
      else
        ¬ (M.AcceptsWithin n (M.next false c) ∧ M.AcceptsWithin n (M.next true c))) ∧
      ∀ b, M.UnambiguousWithin n (M.next b c)

end Turing.MultiTapeATM

namespace Cslib.Complexity

open Turing

/-- Unambiguous alternating polynomial time, with one finite machine and a polynomial clock. -/
def UAP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (t : α → ℕ), MultiTapeTM.PolyBounded (fun a => (enc a).length) t ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeATM k Bool State),
      M.DecidesInTime enc A t ∧
      ∀ a, M.UnambiguousWithin (t a) (M.toPTM.toNTM.initCfg (enc a))}

/-- Forgetting the unambiguity restriction gives ordinary alternating polynomial time. -/
theorem UAP_subset_AP {α : Type} (enc : α ↪ List Bool) : UAP enc ⊆ AP enc := by
  rintro A ⟨t, ht, k, State, hfinite, M, hM, _⟩
  exact ⟨t, ht, k, State, hfinite, M, hM⟩

end Cslib.Complexity
