/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim

/-!
# The crossing interface

A crossing consists of two independent positive-weight wires. Its top ports have colors
`[c, d]`, its bottom ports `[d, c]`; each top port is paired with the opposite bottom port.
A pair is legal when at least one endpoint points inward, as for a subdividing W vertex.

## Main definitions

* `Cslib.Complexity.NCL.Prim.cross`: the weighted crossing relation on four boundary wires.

## Main results

* `Cslib.Complexity.NCL.Prim.genLegal_cross`: the two independent Boolean implications.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Prim

/-- Two crossing wires: each requires an inward endpoint, independently of the other. -/
@[expose] def cross (c d : Color) : Prim [c, d] [d, c] :=
  [⟨[⟨⟨.inl 0, true⟩, c.weight⟩, ⟨⟨.inr 1, false⟩, c.weight⟩], c.weight⟩,
    ⟨[⟨⟨.inl 1, true⟩, d.weight⟩, ⟨⟨.inr 0, false⟩, d.weight⟩], d.weight⟩]

/-- Each bottom direction is bounded by the direction of the paired top wire. -/
theorem genLegal_cross (c d : Color) (β : Fin 2 ⊕ Fin 2 → Bool) :
    Diagram.GenLegal interp (cross c d) β ↔
      β (.inr 1) ≤ β (.inl 0) ∧ β (.inr 0) ≤ β (.inl 1) := by
  cases c <;> cases d <;> revert β <;> decide +kernel

end Cslib.Complexity.NCL.Prim
