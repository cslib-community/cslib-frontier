/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim

/-!
# A free end for a blue wire

A blue wire whose other end must stay unconstrained, such as the try-in wire that starts the
quantifier chain [HearnDemaine2005, Section 3.1], is closed by a small AND/OR gadget
(`Cslib.Complexity.NCL.Gadgets.freeEnd`) instead of the loop of the paper: an OR vertex `v` on
the wire `e` and two wires `a`, `b`, and two AND vertices sharing their red wires `r`, `p`, one
with the blue wire `a`, one with `b`. The inner configuration with `a` into `v`, `b` into the
second AND vertex and `r`, `p` into the first satisfies every vertex whatever the direction of
`e`. The pair `a`, `b` of the OR vertex is protected: `a` into `v` needs `r` and `p` into the
first AND vertex, `b` into `v` needs them into the second.

## Main results

* `Cslib.Complexity.NCL.Gadgets.FreeEnd.openSim`: the gadget implements a free blue end.
* `Cslib.Complexity.NCL.Gadgets.freeEnd_protected`: its OR vertex is protected.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gadgets

open Diagram

local notation "B" => Color.blue

/-- The free end: OR `v(e, a, b)`, AND `(r, p; a)` and AND `(r, p; b)`. -/
@[expose] def freeEnd : Diagram Prim [B] [] :=
  ((gen Prim.orSplit).comp ((gen Prim.andSplit).tensor (id [B]))).comp (gen Prim.andSink)

namespace FreeEnd

/-- The wire `e`. -/
@[expose] def e : freeEnd.Edge := .inl 0
/-- The wire `a`, the left one below the OR vertex. -/
@[expose] def a : freeEnd.Edge := .inr (.inl (.inl (0 : Fin 2)))
/-- The wire `b`, the right one below the OR vertex. -/
@[expose] def b : freeEnd.Edge := .inr (.inl (.inl (1 : Fin 2)))
/-- The red wire `r`, the left one between the AND vertices. -/
@[expose] def r : freeEnd.Edge := .inr (.inl (.inr (.inl (0 : Fin 2))))
/-- The red wire `p`, the right one between the AND vertices. -/
@[expose] def p : freeEnd.Edge := .inr (.inl (.inr (.inl (1 : Fin 2))))

/-- The certificates: the canonical configuration has `e` as given, `a` up into `v`, `b` down
into the second AND vertex, `r` and `p` up into the first; it works for both directions of `e`, so
reversing `e` needs no other move; and the free end forbids nothing. -/
@[expose] def cert : Cert Prim.free freeEnd where
  canon β y := if y = e then β (.inl 0) else if y = b then true else false
  rounds := 0
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- **The free end implements a free blue end.** -/
@[expose] def openSim : OpenSim Prim.interp Prim.interp (gen Prim.free) freeEnd :=
  OpenSim.ofCert cert (by decide +kernel)

/-- One round of propagation refutes `a` and `b` both pointing up, into the OR vertex: `a` points
away from the first AND vertex, which forces `r` and `p` into it; then the second AND vertex gets
neither `b` nor `r`, `p`. -/
private theorem bothIn_refuted :
    (Refutation.conflict : Refutation ℕ).check (numVertexList Prim.interp freeEnd) 1
      (freeEnd.numOrient [(a, false), (b, false)]) = true := by
  decide +kernel

end FreeEnd

open FreeEnd in
/-- **The OR vertex of the free end is protected**: `a` and `b` never both point into it. -/
theorem freeEnd_protected (t : freeEnd.Edge → Bool) (ht : (freeEnd.graph Prim.interp).Legal t) :
    ¬(t a = false ∧ t b = false) := fun h =>
  not_extends_of_refutes (Refutation.conflict.refutes bothIn_refuted) ht (by simpa using h)

end Cslib.Complexity.NCL.Gadgets
