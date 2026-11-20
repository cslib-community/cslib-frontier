/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import Mathlib.Order.Cover

/-!
# Cluster counting in polynomial time

In `CLSharpP`, the accepting certificates are contiguous in a global length-respecting
linear order. Only the directed adjacency test for that order has a polynomial-time
requirement. The order is shared across all instances.

## References

* [L. Hemaspaandra, C. Homan, S. Kosub and K. Wagner,
  *Cluster Computing and the Power of Edge Recognition*](https://arxiv.org/abs/cs/0509060)
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- Cluster `#P`. The verifier reads a fixed polynomial number of certificate bits per
input length, and its accepting certificates form an interval in a single order. -/
def CLSharpP (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ order : LinearOrder (List Bool), letI := order
    (∀ x y : List Bool, x.length < y.length → x < y) ∧
    (∃ adjacent : List Bool × List Bool → Bool,
      ComputableInPolyTime adjacent (encPair encBits encBits) encBool ∧
        ∀ x y, adjacent (x, y) = true ↔ x ⋖ y) ∧
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a, f a = acceptCount V a (p.eval (enc a).length)) ∧
      ∀ a, Set.OrdConnected {w | w.length = p.eval (enc a).length ∧ V (a, w) = true}}

/-- Forgetting the interval condition gives ordinary polynomial-time counting. -/
theorem CLSharpP_subset_SharpP {enc : α ↪ List Bool} : CLSharpP enc ⊆ SharpP enc := by
  rintro f ⟨order, hlength, hadjacent, p, V, hV, hf, hconnected⟩
  exact ⟨p, V, hV, hf⟩

end Cslib.Complexity
