/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Edge networks (§2 of the paper)

An *edge network* (`EdgeNet`) has edges `Fin M`, each with two distinct ends `u i`, `w i`, and
vertices `V` with ordered ports (the edges at the vertex) and tables `eval v`; its value is
`Z = Σ_x Π_v eval_v(x on the ports of v)`. This module holds only the definition, so that its
clients (`Cube/*`, the 3-CNF network of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Net.lean`) can
import it cheaply.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Finset

/-- An edge network over `R`. -/
structure EdgeNet (R V : Type) where
  /-- The number of edges. -/
  M : ℕ
  /-- The two ends of an edge. -/
  u : Fin M → V
  /-- The second end of an edge. -/
  w : Fin M → V
  huw : ∀ i, u i ≠ w i
  /-- The ports of a vertex, in order. -/
  ports : V → List (Fin M)
  hports : ∀ v i, i ∈ ports v ↔ (u i = v ∨ w i = v)
  /-- The table of a vertex, at the bits on its ports. -/
  eval : V → List Bool → R

namespace EdgeNet

variable {R : Type} [CommRing R] {V : Type} [Fintype V] (G : EdgeNet R V)

/-- `Z = Σ_x Π_v eval_v(x on the ports of v)`. -/
def value : R := ∑ x : Fin G.M → Bool, ∏ v, G.eval v ((G.ports v).map x)

end EdgeNet

end Cslib.Complexity.NtimeDspace.Cross
